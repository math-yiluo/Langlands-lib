/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# The Brown right adjoint of a coproduct-preserving triangulated functor

Let `C` be a pretriangulated category with `Hom`-types in `Type v`, with coproducts indexed by
`Type v` and a family of compact generators `S`
(`CategoryTheory.BrownRepresentability.CompactGenerators`), and let `F : C ⥤ D` be a triangulated
functor which preserves coproducts. Brown representability
(`CategoryTheory.Functor.isLeftAdjoint_of_compactGenerators`) shows that `F` has a right adjoint
`G`. We complete this to the abstract form of blueprint nodes
`theorem-existence-exceptional-inverse-image` and `theorem-existence-exceptional-inverse-image--4`:

* `G` commutes with shifts compatibly with the adjunction and is triangulated, and any two right
  adjoints of `F` are isomorphic by a unique isomorphism compatible with the counits
  (`CategoryTheory.Functor.exists_rightAdjoint_of_compactGenerators`,
  `CategoryTheory.Adjunction.existsUnique_iso_comp_counit`);
* if moreover `F` sends the generators to compact objects, then `G` preserves coproducts
  (`CategoryTheory.Adjunction.preservesColimitsOfShape_discrete_of_compactGenerators`): the
  canonical map `∐ G(Nⱼ) ⟶ G(∐ Nⱼ)` induces bijections on `Hom(S i, -)` by compactness of
  `S i` and of `F(S i)`, hence is an isomorphism because the generators detect isomorphisms
  (`CategoryTheory.BrownRepresentability.CompactGenerators.isIso_of_bijective`).

We then specialize to localizing closures (`CategoryTheory.ObjectProperty.localizingClosure`).
A property `P` *compactly generates its localizing closure*
(`CategoryTheory.ObjectProperty.CompactlyGeneratesLocalizingClosure`) if it has a small set of
isomorphism representatives, its objects are compact in `Loc(P)` and detect zero objects of
`Loc(P)`. Given such `P₁`, `P₂` on pretriangulated categories `C₁`, `C₂` and a triangulated
functor `Φ : C₁ ⥤ C₂` mapping `Loc(P₁)` into `Loc(P₂)` and `P₁` into `P₂`, whose restriction to
`Loc(P₁)` preserves coproducts, the restricted functor
`Loc(P₁) ⥤ Loc(P₂)` (`CategoryTheory.ObjectProperty.localizingClosureLift`) has a triangulated,
coproduct-preserving right adjoint, unique up to unique isomorphism
(`CategoryTheory.ObjectProperty.exists_rightAdjoint_localizingClosureLift`). This is the formal
part of blueprint `theorem-existence-exceptional-inverse-image`.
-/

@[expose] public section

universe v u u' u₁ u₂

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory

namespace BrownRepresentability

variable {C : Type u} [Category.{v} C]

/-- In a preadditive category, if a finite sum `∑ⱼ gⱼ ≫ ιⱼ` of morphisms into a coproduct
vanishes, then each `gⱼ` vanishes. -/
lemma eq_zero_of_sum_comp_ι_eq_zero [Preadditive C] {J : Type*} {X : J → C} [HasCoproduct X]
    {s : C} (T : Finset J) (g : ∀ j, s ⟶ X j) (h : ∑ j ∈ T, g j ≫ Sigma.ι X j = 0) {j : J}
    (hj : j ∈ T) : g j = 0 := by
  classical
  have := h =≫ Sigma.desc (Pi.single (M := fun k ↦ X k ⟶ X j) j (𝟙 (X j)))
  rw [Preadditive.sum_comp, Finset.sum_eq_single j] at this
  · simpa using this
  · intro b _ hb
    rw [assoc, Sigma.ι_comp_desc, Pi.single_eq_of_ne hb, comp_zero]
  · exact fun h ↦ (h hj).elim

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Compact generators detect isomorphisms: if composition with `g : X ⟶ X'` is bijective on
morphisms out of each generator, then `g` is an isomorphism. -/
lemma CompactGenerators.isIso_of_bijective {ι : Type v} {S : ι → C} (hS : CompactGenerators S)
    {X X' : C} (g : X ⟶ X') (hbij : ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ f ≫ g)) :
    IsIso g := by
  obtain ⟨Z, p, δ, hT⟩ := distinguished_cocone_triangle g
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hS.isZero_of_forall_eq_zero _ fun i f ↦ ?_)
  obtain ⟨j, ⟨e⟩⟩ := hS.exists_iso_shift i (-1)
  have h₁ : f ≫ δ = 0 := by
    refine eq_zero_of_comp_shift_eq_zero e g (fun f' hf' ↦ (hbij j).1 ?_) _ ?_
    · simpa using hf'
    · have : δ ≫ g⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      rw [assoc, this, comp_zero]
  obtain ⟨f', rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
  obtain ⟨f'', rfl⟩ := (hbij i).2 f'
  have : g ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  simp [this]

end BrownRepresentability

open BrownRepresentability

namespace Adjunction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]

/-- Let `F ⊣ G` with `F` additive, and let `s` be a compact object such that `F(s)` is compact.
Then the canonical map `∐ G(Nⱼ) ⟶ G(∐ Nⱼ)` induces a bijection on morphisms out of `s`. -/
lemma bijective_comp_sigmaComparison [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] {J : Type v} (N : J → D) [HasCoproduct N]
    [HasCoproduct fun j ↦ G.obj (N j)] {s : C} (hs : IsCompactObj s)
    (hFs : IsCompactObj (F.obj s)) :
    Function.Bijective (fun f : s ⟶ ∐ (fun j ↦ G.obj (N j)) ↦ f ≫ sigmaComparison G N) := by
  have : G.Additive := adj.right_adjoint_additive
  have key (T : Finset J) (k : ∀ j, F.obj s ⟶ N j) :
      (∑ j ∈ T, adj.homEquiv _ _ (k j) ≫ Sigma.ι (fun j ↦ G.obj (N j)) j) ≫
        sigmaComparison G N = adj.homEquiv _ _ (∑ j ∈ T, k j ≫ Sigma.ι N j) := by
    simp [Adjunction.homEquiv_unit, Preadditive.sum_comp, Preadditive.comp_sum, Functor.map_sum]
  have hzero (f : s ⟶ ∐ (fun j ↦ G.obj (N j))) (hf : f ≫ sigmaComparison G N = 0) : f = 0 := by
    obtain ⟨T, g, hg⟩ := hs _ (coproductIsCoproduct _) f
    have hg' : f = ∑ j ∈ T, adj.homEquiv _ _ ((adj.homEquiv _ _).symm (g j)) ≫
        Sigma.ι (fun j ↦ G.obj (N j)) j := by
      simpa using hg
    rw [hg', key] at hf
    have h₀ : ∑ j ∈ T, (adj.homEquiv _ _).symm (g j) ≫ Sigma.ι N j = 0 := by
      refine (adj.homEquiv _ _).injective (hf.trans ?_)
      simp [Adjunction.homEquiv_unit]
    rw [hg']
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [eq_zero_of_sum_comp_ι_eq_zero T _ h₀ hj]
    simp [Adjunction.homEquiv_unit]
  refine ⟨fun f₁ f₂ h ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    refine hzero _ ?_
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.2 h
  · obtain ⟨T, k, hk⟩ := hFs _ (coproductIsCoproduct N) ((adj.homEquiv _ _).symm g)
    refine ⟨∑ j ∈ T, adj.homEquiv _ _ (k j) ≫ Sigma.ι (fun j ↦ G.obj (N j)) j, ?_⟩
    dsimp only
    rw [key]
    have hk' : (adj.homEquiv _ _).symm g = ∑ j ∈ T, k j ≫ Sigma.ι N j := by
      simpa using hk
    rw [← hk', Equiv.apply_symm_apply]

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Blueprint `theorem-existence-exceptional-inverse-image--4` (abstract form): let `C` be a
pretriangulated category with a family of compact generators `S`, and `F ⊣ G` with `F` additive. If
`F` sends each generator to a compact object, then the right adjoint `G` preserves coproducts: the
canonical map `∐ G(Nⱼ) ⟶ G(∐ Nⱼ)` induces bijections on `Hom(S i, -)`
(`Adjunction.bijective_comp_sigmaComparison`), and the generators detect isomorphisms. -/
theorem preservesColimitsOfShape_discrete_of_compactGenerators [Preadditive D]
    [HasCoproducts.{v} C] [HasCoproducts.{v} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Additive] {ι : Type v} {S : ι → C} (hS : CompactGenerators S)
    (hF : ∀ i, IsCompactObj (F.obj (S i))) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) G := by
  have (N : J → D) : PreservesColimit (Discrete.functor N) G := by
    have : IsIso (sigmaComparison G N) := hS.isIso_of_bijective _ fun i ↦
      adj.bijective_comp_sigmaComparison N (hS.isCompactObj i) (hF i)
    exact PreservesCoproduct.of_iso_comparison G N
  exact preservesColimitsOfShape_of_discrete G

/-- Uniqueness of right adjoints (blueprint `theorem-existence-exceptional-inverse-image` (3)): two
right adjoints of `F` are isomorphic by a unique isomorphism compatible with the counits. -/
lemma existsUnique_iso_comp_counit {C : Type u₁} {D : Type u₂} [Category* C] [Category* D]
    {F : C ⥤ D} {G G' : D ⥤ C} (adj : F ⊣ G) (adj' : F ⊣ G') :
    ∃! e : G ≅ G', ∀ Y, F.map (e.hom.app Y) ≫ adj'.counit.app Y = adj.counit.app Y := by
  refine ⟨adj.rightAdjointUniq adj', fun Y ↦ rightAdjointUniq_hom_app_counit adj adj' Y,
    fun e he ↦ ?_⟩
  ext Y
  apply (adj'.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, he, rightAdjointUniq_hom_app_counit]

end Adjunction

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Blueprint `theorem-existence-exceptional-inverse-image` (abstract form): let `C` be a
pretriangulated category with coproducts and a family of compact generators, and `F : C ⥤ D` a
triangulated functor preserving coproducts. Then

1. `F` has a right adjoint `G` (Brown representability,
   `Functor.isLeftAdjoint_of_compactGenerators`);
2. `G` commutes with shifts, compatibly with the adjunction, and is triangulated (Stacks, Tag
   0A8G);
3. any two right adjoints of `F` are isomorphic by a unique isomorphism compatible with the
   counits. -/
theorem exists_rightAdjoint_of_compactGenerators [HasCoproducts.{v} C] {ι : Type v} {S : ι → C}
    (hS : CompactGenerators S) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D ⥤ C) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.CommShift ℤ ∧ G.IsTriangulated ∧
      ∀ (G' : D ⥤ C) (adj' : F ⊣ G'),
        ∃! e : G ≅ G', ∀ Y, F.map (e.hom.app Y) ≫ adj'.counit.app Y = adj.counit.app Y := by
  have := isLeftAdjoint_of_compactGenerators hS F
  let adj := Adjunction.ofIsLeftAdjoint F
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact ⟨_, adj, inferInstance, inferInstance, adj.isTriangulated_rightAdjoint,
    fun _ adj' ↦ adj.existsUnique_iso_comp_counit adj'⟩

end Functor

namespace ObjectProperty

section CompactlyGenerates

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- A property of objects `P` *compactly generates its localizing closure* `Loc(P)` if

* `P` is essentially small: it has a set (indexed by a type in `Type v`) of isomorphism
  representatives;
* the objects of `P` are compact in `Loc(P)`;
* they detect zero objects of `Loc(P)`: an object of `Loc(P)` without nonzero morphisms from the
  objects of `P` is zero.

So any small skeleton of `P`, closed under shifts, is a set of compact generators of `Loc(P)`
(`ObjectProperty.CompactlyGeneratesLocalizingClosure.exists_compactGenerators`). -/
structure CompactlyGeneratesLocalizingClosure : Prop where
  exists_skeleton : ∃ (ι : Type v) (S : ι → C), (∀ i, P (S i)) ∧
    ∀ X, P X → ∃ i, Nonempty (S i ≅ X)
  isCompactObj (X : P.localizingClosure.FullSubcategory) (hX : P X.obj) : IsCompactObj X
  isZero_of_forall_eq_zero (Y : P.localizingClosure.FullSubcategory)
    (hY : ∀ X : P.localizingClosure.FullSubcategory, P X.obj → ∀ f : X ⟶ Y, f = 0) : IsZero Y

variable {P}

/-- If `P` compactly generates `Loc(P)`, then `Loc(P)` has a family of compact generators, each of
which is a shift of an object of `P`. -/
lemma CompactlyGeneratesLocalizingClosure.exists_compactGenerators
    (h : P.CompactlyGeneratesLocalizingClosure) :
    ∃ (ι : Type v) (S : ι → P.localizingClosure.FullSubcategory), CompactGenerators S ∧
      ∀ i, ∃ (X : P.localizingClosure.FullSubcategory) (n : ℤ), P X.obj ∧
        Nonempty (S i ≅ X⟦n⟧) := by
  obtain ⟨ι, S₀, hS₀, hS₀'⟩ := h.exists_skeleton
  let X₀ (k : ι) : P.localizingClosure.FullSubcategory := ⟨S₀ k, P.le_localizingClosure _ (hS₀ k)⟩
  refine ⟨ι × ULift.{v} ℤ, fun p ↦ (X₀ p.1)⟦p.2.down⟧, ⟨fun p m ↦ ?_, fun p ↦ ?_, fun Y hY ↦ ?_⟩,
    fun p ↦ ⟨X₀ p.1, p.2.down, hS₀ p.1, ⟨Iso.refl _⟩⟩⟩
  · exact ⟨(p.1, ⟨p.2.down + m⟩), ⟨(shiftFunctorAdd _ p.2.down m).app (X₀ p.1)⟩⟩
  · exact (h.isCompactObj (X₀ p.1) (hS₀ p.1)).shift p.2.down
  · refine h.isZero_of_forall_eq_zero Y fun X hX f ↦ ?_
    obtain ⟨k, ⟨e⟩⟩ := hS₀' X.obj hX
    let e' : X₀ k ≅ X := P.localizingClosure.fullyFaithfulι.preimageIso e
    have h₀ : ((shiftFunctorZero _ ℤ).hom.app (X₀ k) ≫ e'.hom) ≫ f = 0 := hY (k, ⟨0⟩) _
    rw [← cancel_epi e'.hom, comp_zero]
    exact (cancel_epi ((shiftFunctorZero _ ℤ).hom.app (X₀ k))).1
      (by rw [← assoc, h₀, comp_zero])

end CompactlyGenerates

section Lift

variable {C₁ : Type u₁} [Category.{v} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (Φ : C₁ ⥤ C₂)
  (hΦ : ∀ X, P₁.localizingClosure X → P₂.localizingClosure (Φ.obj X))

/-- The restriction `Loc(P₁) ⥤ Loc(P₂)` of a functor `Φ : C₁ ⥤ C₂` which maps `Loc(P₁)` into
`Loc(P₂)`. -/
noncomputable def localizingClosureLift :
    P₁.localizingClosure.FullSubcategory ⥤ P₂.localizingClosure.FullSubcategory :=
  P₂.localizingClosure.lift (P₁.localizingClosure.ι ⋙ Φ) fun X ↦ hΦ X.obj X.property

/-- The restriction of `Φ` to localizing closures is compatible with the inclusions. -/
noncomputable def localizingClosureLiftCompιIso :
    localizingClosureLift P₁ P₂ Φ hΦ ⋙ P₂.localizingClosure.ι ≅ P₁.localizingClosure.ι ⋙ Φ :=
  P₂.localizingClosure.liftCompιIso _ _

@[simp]
lemma localizingClosureLift_obj_obj (X : P₁.localizingClosure.FullSubcategory) :
    ((localizingClosureLift P₁ P₂ Φ hΦ).obj X).obj = Φ.obj X.obj :=
  rfl

variable [Φ.CommShift ℤ]

noncomputable instance : (localizingClosureLift P₁ P₂ Φ hΦ).CommShift ℤ :=
  inferInstanceAs ((P₂.localizingClosure.lift (P₁.localizingClosure.ι ⋙ Φ) _).CommShift ℤ)

instance [Φ.IsTriangulated] : (localizingClosureLift P₁ P₂ Φ hΦ).IsTriangulated :=
  inferInstanceAs ((P₂.localizingClosure.lift (P₁.localizingClosure.ι ⋙ Φ) _).IsTriangulated)

/-- The restriction of `Φ` to localizing closures preserves the coproducts which the restriction
of `Φ` to `Loc(P₁)` preserves. -/
instance preservesColimitsOfShape_localizingClosureLift (J : Type v)
    [PreservesColimitsOfShape (Discrete J) (P₁.localizingClosure.ι ⋙ Φ)] :
    PreservesColimitsOfShape (Discrete J) (localizingClosureLift P₁ P₂ Φ hΦ) :=
  have := preservesColimitsOfShape_of_natIso (J := Discrete J)
    (localizingClosureLiftCompιIso P₁ P₂ Φ hΦ).symm
  preservesColimitsOfShape_of_reflects_of_preserves _ P₂.localizingClosure.ι

/-- Blueprint `theorem-existence-exceptional-inverse-image` (1), on localizing closures: if `P₁`
compactly generates its localizing closure and the restriction of the triangulated functor `Φ` to
`Loc(P₁)` preserves coproducts, then the restriction `Φ : Loc(P₁) ⥤ Loc(P₂)` is a left adjoint
(Brown representability). -/
theorem isLeftAdjoint_localizingClosureLift [HasCoproducts.{v} C₁] [Φ.IsTriangulated]
    (hP₁ : P₁.CompactlyGeneratesLocalizingClosure)
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) (P₁.localizingClosure.ι ⋙ Φ)] :
    (localizingClosureLift P₁ P₂ Φ hΦ).IsLeftAdjoint := by
  obtain ⟨ι, S, hS, -⟩ := hP₁.exists_compactGenerators
  exact Functor.isLeftAdjoint_of_compactGenerators hS _

/-- Blueprint `theorem-existence-exceptional-inverse-image--4`, on localizing closures: if `P₁` and
`P₂` compactly generate their localizing closures and `Φ` maps `P₁` into `P₂`, then every right
adjoint of the restriction `Φ : Loc(P₁) ⥤ Loc(P₂)` preserves coproducts. -/
theorem preservesColimitsOfShape_of_localizingClosureLift_adjunction [HasCoproducts.{v} C₁]
    [HasCoproducts.{v} C₂] [Φ.IsTriangulated] (hP₁ : P₁.CompactlyGeneratesLocalizingClosure)
    (hP₂ : P₂.CompactlyGeneratesLocalizingClosure) (hΦ' : ∀ X, P₁ X → P₂ (Φ.obj X))
    {G : P₂.localizingClosure.FullSubcategory ⥤ P₁.localizingClosure.FullSubcategory}
    (adj : localizingClosureLift P₁ P₂ Φ hΦ ⊣ G) (J : Type v) :
    PreservesColimitsOfShape (Discrete J) G := by
  obtain ⟨ι, S, hS, hS'⟩ := hP₁.exists_compactGenerators
  refine adj.preservesColimitsOfShape_discrete_of_compactGenerators hS (fun i ↦ ?_) J
  obtain ⟨X, n, hX, ⟨e⟩⟩ := hS' i
  exact ((hP₂.isCompactObj _ (hΦ' _ hX)).shift n).of_iso
    ((localizingClosureLift P₁ P₂ Φ hΦ).mapIso e ≪≫
      ((localizingClosureLift P₁ P₂ Φ hΦ).commShiftIso n).app X)

/-- The formal part of blueprint `theorem-existence-exceptional-inverse-image`. Let `P₁`, `P₂`
compactly generate their localizing closures, and let `Φ : C₁ ⥤ C₂` be a triangulated functor which
maps `Loc(P₁)` into `Loc(P₂)` and `P₁` into `P₂`, and whose restriction to `Loc(P₁)` preserves
coproducts. Then the restriction `Φ : Loc(P₁) ⥤ Loc(P₂)` has a right adjoint `G`, which commutes
with shifts compatibly with the adjunction, is triangulated, preserves coproducts, and is unique up
to a unique isomorphism compatible with the counits. -/
theorem exists_rightAdjoint_localizingClosureLift [HasCoproducts.{v} C₁] [HasCoproducts.{v} C₂]
    [Φ.IsTriangulated] (hP₁ : P₁.CompactlyGeneratesLocalizingClosure)
    (hP₂ : P₂.CompactlyGeneratesLocalizingClosure) (hΦ' : ∀ X, P₁ X → P₂ (Φ.obj X))
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) (P₁.localizingClosure.ι ⋙ Φ)] :
    ∃ (G : P₂.localizingClosure.FullSubcategory ⥤ P₁.localizingClosure.FullSubcategory)
      (adj : localizingClosureLift P₁ P₂ Φ hΦ ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type v, PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : P₂.localizingClosure.FullSubcategory ⥤ P₁.localizingClosure.FullSubcategory)
        (adj' : localizingClosureLift P₁ P₂ Φ hΦ ⊣ G'),
        ∃! e : G ≅ G', ∀ Y, (localizingClosureLift P₁ P₂ Φ hΦ).map (e.hom.app Y) ≫
          adj'.counit.app Y = adj.counit.app Y := by
  obtain ⟨ι, S, hS, -⟩ := hP₁.exists_compactGenerators
  obtain ⟨G, adj, _, h₁, h₂, h₃⟩ :=
    Functor.exists_rightAdjoint_of_compactGenerators hS (localizingClosureLift P₁ P₂ Φ hΦ)
  exact ⟨G, adj, inferInstance, h₁, h₂,
    preservesColimitsOfShape_of_localizingClosureLift_adjunction P₁ P₂ Φ hΦ hP₁ hP₂ hΦ' adj, h₃⟩

end Lift

end ObjectProperty

end CategoryTheory
