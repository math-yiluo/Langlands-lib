/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-!
# Exactness and Grothendieck categories of algebras with invertible structure morphism

Let `F` be an exact additive endofunctor of an abelian category `C`. The category
`IsoAlgebra F` of pairs `(X, φ : F X ≅ X)` is abelian, and its forgetful functor to `C` is
exact and reflects isomorphisms. This file shows:

- the transport `IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G` along an exact functor
  `L : C ⥤ D` with `e : L ⋙ G ≅ F ⋙ L` is exact, since the forgetful functors reflect finite
  limits and colimits;
- if `F` is an autoequivalence of a Grothendieck abelian category, then `IsoAlgebra F` is again
  Grothendieck abelian.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.strNatIso`: the structure isomorphisms as a natural
  isomorphism `forget F ⋙ F ≅ forget F`.
- `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso`.
- `CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteLimits_mapOfNatIso` and
  `CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso`.
- `CategoryTheory.Endofunctor.IsoAlgebra.isGrothendieckAbelian`.
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section StrNatIso

variable (F : C ⥤ C)

/-- The structure isomorphisms of algebras with invertible structure morphism, as a natural
isomorphism `F ∘ forget ≅ forget`. -/
noncomputable def strNatIso : forget F ⋙ F ≅ forget F :=
  NatIso.ofComponents (fun K ↦ K.str) fun φ ↦ φ.hom.h

@[simp]
lemma strNatIso_hom_app (K : IsoAlgebra F) : (strNatIso F).hom.app K = K.str.hom :=
  rfl

end StrNatIso

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The underlying object of the transport of an algebra along `L` is the image under `L` of
its underlying object. -/
noncomputable def mapOfNatIsoCompForgetIso : mapOfNatIso e ⋙ forget G ≅ forget F ⋙ L :=
  Iso.refl _

variable [Abelian C] [Abelian D] [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

instance reflectsFiniteLimits_forget : ReflectsFiniteLimits (forget G) where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

instance reflectsFiniteColimits_forget : ReflectsFiniteColimits (forget G) where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- The transport of algebras along a left exact functor is left exact: its composite with
the forgetful functor, which reflects finite limits, is `forget F ⋙ L`. -/
instance preservesFiniteLimits_mapOfNatIso [PreservesFiniteLimits L] :
    PreservesFiniteLimits (mapOfNatIso e) := by
  have : PreservesFiniteLimits (mapOfNatIso e ⋙ forget G) :=
    preservesFiniteLimits_of_natIso (mapOfNatIsoCompForgetIso e).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget G)

/-- The transport of algebras along a right exact functor is right exact: its composite with
the forgetful functor, which reflects finite colimits, is `forget F ⋙ L`. -/
instance preservesFiniteColimits_mapOfNatIso [PreservesFiniteColimits L] :
    PreservesFiniteColimits (mapOfNatIso e) := by
  have : PreservesFiniteColimits (mapOfNatIso e ⋙ forget G) :=
    preservesFiniteColimits_of_natIso (mapOfNatIsoCompForgetIso e).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget G)

end Map

section Autoequivalence

variable (F : C ⥤ C) [F.IsEquivalence]

instance : (forget F).Faithful :=
  inferInstanceAs ((Algebra.IsIsoStr F).ι ⋙ Algebra.forget F).Faithful

/-- The category of algebras with invertible structure morphism of an autoequivalence has the
colimits that the underlying category has: they are created by the forgetful functor. -/
instance (J : Type*) [Category J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (IsoAlgebra F) :=
  inferInstanceAs (HasColimitsOfShape J (Algebra.IsIsoStr F).FullSubcategory)

instance (J : Type*) [Category J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (forget F) :=
  inferInstanceAs (PreservesColimitsOfShape J ((Algebra.IsIsoStr F).ι ⋙ Algebra.forget F))

/-! ### The free algebra on an object

For an object `S`, the coproduct `∐_{n ∈ ℤ} Fⁿ S` carries the structure isomorphism
`F (∐ₙ Fⁿ S) ≅ ∐ₙ Fⁿ⁺¹ S ≅ ∐ₙ Fⁿ S` shifting the summands, and a morphism `s : S ⟶ K` into an
algebra `K` extends to a morphism of algebras `∐ₙ Fⁿ S ⟶ K`, given on `Fⁿ S` by `Fⁿ s` followed
by the `n`-th iterate of the structure isomorphism of `K`. -/

namespace Free

/-- (Impl) The objects `Fⁿ S` for `n ≥ 0`. -/
def posObj (S : C) : ℕ → C
  | 0 => S
  | n + 1 => F.obj (posObj S n)

/-- (Impl) The objects `F⁻⁽ⁿ⁺¹⁾ S` for `n ≥ 0`, for a quasi-inverse `F⁻¹` of `F`. -/
noncomputable def negObj (S : C) : ℕ → C
  | 0 => F.inv.obj S
  | n + 1 => F.inv.obj (negObj S n)

/-- (Impl) The objects `Fⁿ S` for `n : ℤ`. -/
noncomputable def obj (S : C) : ℤ → C
  | .ofNat n => posObj F S n
  | .negSucc n => negObj F S n

/-- (Impl) The isomorphisms `F (Fⁿ S) ≅ Fⁿ⁺¹ S`: identities for `n ≥ 0` and counits of
`F⁻¹ ⊣ F` for `n < 0`. -/
noncomputable def objSucc (S : C) : ∀ n : ℤ, F.obj (obj F S n) ≅ obj F S (n + 1)
  | .ofNat _ => Iso.refl _
  | .negSucc 0 => F.asEquivalence.counitIso.app S
  | .negSucc (n + 1) => F.asEquivalence.counitIso.app (negObj F S n)

variable {F} {S : C} (K : IsoAlgebra F) (s : S ⟶ K.carrier)

/-- (Impl) The morphisms `Fⁿ S ⟶ K` for `n ≥ 0` induced by `s : S ⟶ K`: `Fⁿ s` followed by
the iterated structure isomorphism. -/
noncomputable def posHom : ∀ n : ℕ, posObj F S n ⟶ K.carrier
  | 0 => s
  | n + 1 => F.map (posHom n) ≫ K.str.hom

/-- (Impl) The morphisms `F⁻⁽ⁿ⁺¹⁾ S ⟶ K` for `n ≥ 0` induced by `s : S ⟶ K`, defined by
descending induction using that `F` is fully faithful. -/
noncomputable def negHom : ∀ n : ℕ, negObj F S n ⟶ K.carrier
  | 0 => F.preimage ((objSucc F S (.negSucc 0)).hom ≫ s ≫ K.str.inv)
  | n + 1 => F.preimage ((objSucc F S (.negSucc (n + 1))).hom ≫ negHom n ≫ K.str.inv)

/-- (Impl) The morphisms `Fⁿ S ⟶ K` for `n : ℤ` induced by `s : S ⟶ K`. -/
noncomputable def hom : ∀ n : ℤ, obj F S n ⟶ K.carrier
  | .ofNat n => posHom K s n
  | .negSucc n => negHom K s n

/-- The morphisms `Fⁿ S ⟶ K` are compatible with the structure isomorphisms. -/
lemma map_hom_comp_str (n : ℤ) :
    F.map (hom K s n) ≫ K.str.hom = (objSucc F S n).hom ≫ hom K s (n + 1) := by
  rcases n with n | _ | n
  · exact (Category.id_comp _).symm
  all_goals
    simp only [hom, negHom, Functor.map_preimage, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl

/-- On `F⁰ S = S`, the induced morphism is `s`. -/
@[simp]
lemma hom_zero : hom K s 0 = s :=
  rfl

variable (F S) [HasColimitsOfShape (Discrete ℤ) C]

/-- (Impl) The structure isomorphism `F (∐ₙ Fⁿ S) ≅ ∐ₙ F (Fⁿ S) ≅ ∐ₙ Fⁿ⁺¹ S ≅ ∐ₙ Fⁿ S` of the free
algebra. -/
noncomputable def str : F.obj (∐ obj F S) ≅ ∐ obj F S :=
  PreservesCoproduct.iso F (obj F S) ≪≫ Sigma.mapIso (objSucc F S) ≪≫
    Sigma.reindex (Equiv.addRight (1 : ℤ)) (obj F S)

/-- The structure isomorphism of the free algebra maps the summand `F (Fⁿ S)` to the summand
`Fⁿ⁺¹ S`. -/
@[reassoc]
lemma map_ι_comp_str (n : ℤ) :
    F.map (Sigma.ι (obj F S) n) ≫ (str F S).hom =
      (objSucc F S n).hom ≫ Sigma.ι (obj F S) (n + 1) := by
  have h : F.map (Sigma.ι (obj F S) n) ≫ (PreservesCoproduct.iso F (obj F S)).hom =
      Sigma.ι (fun n ↦ F.obj (obj F S n)) n := by
    rw [← Iso.eq_comp_inv, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  simp only [str, Iso.trans_hom, reassoc_of% h, Sigma.ι_mapIso_hom_assoc]
  exact congrArg _ (Sigma.ι_reindex_hom (Equiv.addRight (1 : ℤ)) (obj F S) n)

/-- Morphisms out of `F (∐ₙ Fⁿ S)` are determined by their restrictions to the `F (Fⁿ S)`, since
`F` preserves coproducts. -/
lemma map_hom_ext {Z : C} {u u' : F.obj (∐ obj F S) ⟶ Z}
    (h : ∀ n, F.map (Sigma.ι (obj F S) n) ≫ u = F.map (Sigma.ι (obj F S) n) ≫ u') : u = u' := by
  rw [← cancel_epi (PreservesCoproduct.iso F (obj F S)).inv]
  refine Sigma.hom_ext _ _ fun n ↦ ?_
  simpa [PreservesCoproduct.inv_hom] using h n

/-- The free algebra `∐ₙ Fⁿ S` on `S`, with structure isomorphism shifting the summands. -/
noncomputable def algebra : IsoAlgebra F :=
  IsoAlgebra.mk (∐ obj F S) (str F S)

variable {F S}

/-- The morphism of algebras `∐ₙ Fⁿ S ⟶ K` induced by a morphism `s : S ⟶ K`. -/
noncomputable def desc : algebra F S ⟶ K :=
  ObjectProperty.homMk
    { f := Sigma.desc (hom K s)
      h := map_hom_ext F S fun n ↦ by
        change F.map (Sigma.ι (obj F S) n) ≫ F.map (Sigma.desc (hom K s)) ≫ K.str.hom =
          F.map (Sigma.ι (obj F S) n) ≫ (str F S).hom ≫ Sigma.desc (hom K s)
        rw [map_ι_comp_str_assoc, ← F.map_comp_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc,
          map_hom_comp_str] }

/-- The morphism `desc K s` restricts to `s` on the summand `S = F⁰ S`. -/
@[reassoc (attr := simp)]
lemma ι_desc_hom_f : Sigma.ι (obj F S) 0 ≫ (desc K s).hom.f = s :=
  Sigma.ι_comp_desc _ _

/-- The free algebra on a separator of `C` is a separator of `IsoAlgebra F`. -/
lemma isSeparator_algebra (hS : IsSeparator S) : IsSeparator (algebra F S) := by
  rw [isSeparator_def] at hS ⊢
  intro K L f g hfg
  refine (forget F).map_injective (hS _ _ fun s ↦ ?_)
  have := congr_arg (fun φ ↦ Sigma.ι (obj F S) 0 ≫ (forget F).map φ) (hfg (desc K s))
  simp only [Functor.map_comp] at this
  simpa only [forget_map, ι_desc_hom_f_assoc] using this

variable {K}

/-- A morphism of algebras out of the free algebra satisfies, on the summands, the recursion
defining `Free.hom`. -/
lemma map_ι_comp_comp_str (g : algebra F S ⟶ K) (n : ℤ) :
    F.map (Sigma.ι (obj F S) n ≫ g.hom.f) ≫ K.str.hom =
      (objSucc F S n).hom ≫ Sigma.ι (obj F S) (n + 1) ≫ g.hom.f := by
  rw [F.map_comp, Category.assoc, str_hom, g.hom.h, ← map_ι_comp_str_assoc]
  rfl

/-- Morphisms of algebras out of the free algebra `∐ₙ Fⁿ S` are determined by their
restrictions to the summand `F⁰ S = S`. -/
lemma hom_ext {g g' : algebra F S ⟶ K}
    (h : Sigma.ι (obj F S) 0 ≫ g.hom.f = Sigma.ι (obj F S) 0 ≫ g'.hom.f) : g = g' := by
  have step : ∀ m n : ℤ, m + 1 = n → (Sigma.ι (obj F S) m ≫ g.hom.f =
      Sigma.ι (obj F S) m ≫ g'.hom.f ↔
        Sigma.ι (obj F S) n ≫ g.hom.f = Sigma.ι (obj F S) n ≫ g'.hom.f) := by
    rintro m _ rfl
    have e₁ := map_ι_comp_comp_str g m
    have e₂ := map_ι_comp_comp_str g' m
    constructor
    · intro hm
      rw [← cancel_epi (objSucc F S m).hom, ← e₁, ← e₂, hm]
    · intro hm
      apply F.map_injective
      rw [← cancel_mono K.str.hom, e₁, e₂, hm]
  have hn (n : ℤ) : Sigma.ι (obj F S) n ≫ g.hom.f = Sigma.ι (obj F S) n ≫ g'.hom.f :=
    Int.induction_on n h (fun i hi ↦ (step _ _ rfl).1 hi)
      (fun i hi ↦ (step _ _ (by omega)).2 hi)
  exact (forget F).map_injective (Sigma.hom_ext _ _ hn)

variable {T U : C}

variable (F) in
/-- (Impl) The morphisms `Fⁿ S ⟶ Fⁿ T` induced by `f : S ⟶ T`, for `n ≥ 0`. -/
def posMap (f : S ⟶ T) : ∀ n : ℕ, posObj F S n ⟶ posObj F T n
  | 0 => f
  | n + 1 => F.map (posMap f n)

variable (F) in
/-- (Impl) The morphisms `F⁻⁽ⁿ⁺¹⁾ S ⟶ F⁻⁽ⁿ⁺¹⁾ T` induced by `f : S ⟶ T`, for `n ≥ 0`. -/
noncomputable def negMap (f : S ⟶ T) : ∀ n : ℕ, negObj F S n ⟶ negObj F T n
  | 0 => F.inv.map f
  | n + 1 => F.inv.map (negMap f n)

variable (F) in
/-- (Impl) The morphisms `Fⁿ S ⟶ Fⁿ T` induced by `f : S ⟶ T`, for `n : ℤ`. -/
noncomputable def objMap (f : S ⟶ T) : ∀ n : ℤ, obj F S n ⟶ obj F T n
  | .ofNat n => posMap F f n
  | .negSucc n => negMap F f n

omit [HasColimitsOfShape (Discrete ℤ) C] in
@[simp]
lemma objMap_zero (f : S ⟶ T) : objMap F f 0 = f :=
  rfl

omit [HasColimitsOfShape (Discrete ℤ) C] in
/-- The morphisms `Fⁿ S ⟶ Fⁿ T` are compatible with the isomorphisms `F (Fⁿ S) ≅ Fⁿ⁺¹ S`. -/
@[reassoc]
lemma map_objMap_comp_objSucc (f : S ⟶ T) (n : ℤ) :
    F.map (objMap F f n) ≫ (objSucc F T n).hom = (objSucc F S n).hom ≫ objMap F f (n + 1) := by
  rcases n with n | _ | n
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact F.asEquivalence.counit.naturality f
  · exact F.asEquivalence.counit.naturality (negMap F f n)

omit [HasColimitsOfShape (Discrete ℤ) C] in
instance mono_objMap (f : S ⟶ T) [Mono f] (n : ℤ) : Mono (objMap F f n) := by
  have hpos (n : ℕ) : Mono (posMap F f n) := by
    induction n with
    | zero => assumption
    | succ n ih => exact F.map_mono (posMap F f n)
  have hneg (n : ℕ) : Mono (negMap F f n) := by
    induction n with
    | zero => exact F.inv.map_mono f
    | succ n ih => exact F.inv.map_mono (negMap F f n)
  rcases n with n | n
  · exact hpos n
  · exact hneg n

/-- The morphism of free algebras `∐ₙ Fⁿ S ⟶ ∐ₙ Fⁿ T` induced by a morphism `f : S ⟶ T`. -/
noncomputable def map (f : S ⟶ T) : algebra F S ⟶ algebra F T :=
  ObjectProperty.homMk
    { f := Limits.Sigma.map (objMap F f)
      h := map_hom_ext F S fun n ↦ by
        change F.map (Sigma.ι (obj F S) n) ≫ F.map (Limits.Sigma.map (objMap F f)) ≫ (str F T).hom =
          F.map (Sigma.ι (obj F S) n) ≫ (str F S).hom ≫ Limits.Sigma.map (objMap F f)
        rw [← F.map_comp_assoc, Sigma.ι_map, F.map_comp, Category.assoc,
          map_ι_comp_str, map_objMap_comp_objSucc_assoc, map_ι_comp_str_assoc,
          Sigma.ι_map] }

@[simp]
lemma map_hom_f (f : S ⟶ T) : (map f).hom.f = Limits.Sigma.map (objMap F f) :=
  rfl

variable (F) in
/-- The free algebra functor `S ↦ ∐ₙ Fⁿ S`, left adjoint to the forgetful functor
(`CategoryTheory.Endofunctor.IsoAlgebra.Free.adjunction`). -/
@[simps obj]
noncomputable def functor : C ⥤ IsoAlgebra F where
  obj S := algebra F S
  map f := map f
  map_id S := hom_ext ((Sigma.ι_map _ _).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm))
  map_comp f g := hom_ext (by simp [Sigma.ι_map_assoc])

variable (F) in
/-- The free algebra functor is left adjoint to the forgetful functor: a morphism of
algebras `∐ₙ Fⁿ S ⟶ K` is the same as a morphism `S ⟶ K` in `C`. -/
noncomputable def adjunction : functor F ⊣ forget F :=
  Adjunction.mkOfHomEquiv
    { homEquiv S K :=
        { toFun g := Sigma.ι (obj F S) 0 ≫ g.hom.f
          invFun s := desc K s
          left_inv g := hom_ext (ι_desc_hom_f _ _)
          right_inv s := ι_desc_hom_f K s }
      homEquiv_naturality_left_symm f s := hom_ext (by simp [functor, Sigma.ι_map_assoc])
      homEquiv_naturality_right g φ := by simp }

/-- The free algebra functor preserves monomorphisms if coproducts indexed by `ℤ` do. -/
instance [(MorphismProperty.monomorphisms C).IsStableUnderCoproductsOfShape ℤ] :
    (functor F).PreservesMonomorphisms where
  preserves _ _ := (forget F).mono_of_mono_map (inferInstanceAs (Mono (Limits.Sigma.map _)))

end Free

end Autoequivalence

variable (F : C ⥤ C) [Abelian C] [F.Additive] [F.IsEquivalence]

/-- **Algebras for an autoequivalence of a Grothendieck abelian category.** If `F` is an
additive autoequivalence of a Grothendieck abelian category `C`, then the category of pairs
`(X, φ : F X ≅ X)` is Grothendieck abelian. Filtered colimits are created by the forgetful
functor, since `F` preserves them, and they are exact, the forgetful functor being exact and
conservative. If `S` is a separator of `C`, then the free objects
`⨁_{n ∈ ℤ} Fⁿ S`, with the structure isomorphism shifting the summands, form a separator: a
morphism of algebras out of the free object on `S` is the same as a morphism out of `S` in
`C`. -/
theorem isGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w} (IsoAlgebra F) := by
  have : HasFilteredColimitsOfSize.{w, w} (IsoAlgebra F) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{w, w} (IsoAlgebra F) :=
    ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J (forget F)⟩
  have : LocallySmall.{w} (IsoAlgebra F) := locallySmall_of_faithful (forget F)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0} C
  obtain ⟨S, hS⟩ := HasSeparator.hasSeparator (C := C)
  have : HasSeparator (IsoAlgebra F) := ⟨_, Free.isSeparator_algebra hS⟩
  exact {}

end CategoryTheory.Endofunctor.IsoAlgebra
