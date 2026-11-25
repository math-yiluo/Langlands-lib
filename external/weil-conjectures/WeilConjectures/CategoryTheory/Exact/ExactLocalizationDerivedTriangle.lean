/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Deriving an exact localization sequence

Source: Stacks, Tags 0152, 070I and 070K; the construction used in blueprint
`proposition-extension-zero-restriction-closed-subscheme`, proof (1)
(blueprint: lem-sf-exact-localization-derived-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

section TransportShortExact

variable {E : Type*} [Category* E]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {L M N : E ⥤ DerivedCategory D}
  {T : E → ShortComplex (CochainComplex D ℤ)}
  {p : ∀ X, L.obj X ≅ DerivedCategory.Q.obj (T X).X₁}
  {q : ∀ X, M.obj X ≅ DerivedCategory.Q.obj (T X).X₂}
  {r : ∀ X, N.obj X ≅ DerivedCategory.Q.obj (T X).X₃}

/-- The natural transformation `L ⟶ M` obtained by transporting the first arrows of a
family of short complexes along natural identifications.
Source: Stacks, Tag 0152 (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def transportShortComplexMor₁
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      M.map f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) : L ⟶ M where
  app X := (p X).hom ≫ DerivedCategory.Q.map (T X).f ≫ (q X).inv
  naturality X Y f := by
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
    apply (cancel_mono (q Y).hom).1
    simp only [Category.assoc]
    rw [← Category.assoc, hg₂]
    simp only [Category.assoc]
    rw [← Category.assoc, hg₁]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, ← Functor.map_comp] using
      congrArg (fun k ↦ (p X).hom ≫ DerivedCategory.Q.map k) g.comm₁₂

/-- The natural transformation `M ⟶ N` obtained by transporting the second arrows of a
family of short complexes along natural identifications.
Source: Stacks, Tag 0152 (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def transportShortComplexMor₂
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      M.map f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) : M ⟶ N where
  app X := (q X).hom ≫ DerivedCategory.Q.map (T X).g ≫ (r X).inv
  naturality X Y f := by
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
    apply (cancel_mono (r Y).hom).1
    simp only [Category.assoc]
    rw [← Category.assoc, hg₃]
    simp only [Category.assoc]
    rw [← Category.assoc, hg₂]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, ← Functor.map_comp] using
      congrArg (fun k ↦ (q X).hom ≫ DerivedCategory.Q.map k) g.comm₂₃

/-- The natural connecting transformation `N ⟶ L[1]` obtained by transporting the
connecting maps of a family of short exact sequences of complexes.
Source: Stacks, Tag 0152 (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def transportShortComplexMor₃
    (ht : ∀ X, (T X).ShortExact)
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      M.map f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) :
    N ⟶ L ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ) where
  app X := (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
    (shiftFunctor _ (1 : ℤ)).map (p X).inv
  naturality X Y f := by
    obtain ⟨g, hg₁, hg₂, hg₃⟩ := hn f
    apply (cancel_mono ((shiftFunctor _ (1 : ℤ)).map (p Y).hom)).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id]
    rw [← Category.assoc, hg₃]
    rw [Category.assoc, ← DerivedCategory.triangleOfSESδ_naturality (ht X) (ht Y) g]
    change _ = (r X).hom ≫ DerivedCategory.triangleOfSESδ (ht X) ≫
      (shiftFunctor _ (1 : ℤ)).map (p X).inv ≫
      (shiftFunctor _ (1 : ℤ)).map (L.map f) ≫
      (shiftFunctor _ (1 : ℤ)).map (p Y).hom
    simp only [← Functor.map_comp, hg₁, Iso.inv_hom_id_assoc]

/-- The transported arrows form distinguished triangles.
Source: Stacks, Tag 0152 (blueprint: lem-sf-exact-localization-derived-triangle). -/
theorem transportShortComplex_distinguished
    (ht : ∀ X, (T X).ShortExact)
    (hn : ∀ {X Y} (f : X ⟶ Y), ∃ g : T X ⟶ T Y,
      L.map f ≫ (p Y).hom = (p X).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      M.map f ≫ (q Y).hom = (q X).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      N.map f ≫ (r Y).hom = (r X).hom ≫ DerivedCategory.Q.map g.τ₃) (X : E) :
    Triangle.mk ((transportShortComplexMor₁ hn).app X) ((transportShortComplexMor₂ hn).app X)
      ((transportShortComplexMor₃ ht hn).app X) ∈ distTriang (DerivedCategory D) := by
  apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (ht X)) _
  refine Triangle.isoMk _ _ (p X) (q X) (r X) ?_ ?_ ?_
  · simp [transportShortComplexMor₁]
  · simp [transportShortComplexMor₂]
  · simp [transportShortComplexMor₃, ← Functor.map_comp]

end TransportShortExact

set_option backward.isDefEq.respectTransparency false in
private theorem computation_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (G : C ⥤ D) [G.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    {J J' : CochainComplex C ℤ} [J.IsKInjective] [J'.IsKInjective] (f : J ⟶ J') :
    (G.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map f) ≫
        (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J')).hom =
      (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 J)).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) := by
  let η := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  let := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J
  let := G.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J'
  have hn : (G.rightDerivedFunctorOfQuasiIsoResolutions h).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f)) ≫
        inv (η.app ((HomotopyCategory.quotient _ _).obj J')) =
      inv (η.app ((HomotopyCategory.quotient _ _).obj J)) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ _).map f)) := by
    apply (cancel_mono (η.app ((HomotopyCategory.quotient _ _).obj J'))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hn := η.naturality ((HomotopyCategory.quotient _ _).map f)
    dsimp only [Functor.comp_map] at hn
    rw [hn, IsIso.inv_hom_id_assoc]
  dsimp [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso]
  simp only [Functor.map_id, Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp, DerivedCategory.quotientCompQhIso_inv_naturality]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := reassoc_of% hn
  dsimp only [η] at hn'
  rw [hn', Functor.mapHomotopyCategory_map]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]


section ExactLocalization

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- Every derived object is isomorphic to the localization of a K-injective complex,
given a supply of K-injective resolutions.
Source: Stacks, Tag 070I (blueprint: lem-sf-exact-localization-derived-triangle). -/
theorem exists_isKInjective_derivedCategory_iso
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    (K : DerivedCategory C) :
    ∃ J : CochainComplex C ℤ, J.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj J ≅ K) := by
  obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  obtain ⟨J, s, hJ, hs⟩ := h L
  exact ⟨J, hJ, ⟨(asIso (DerivedCategory.Q.map s)).symm ≪≫ e⟩⟩

/-- A chosen K-injective complex representing a derived object.
Source: Stacks, Tag 070I (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def kInjectiveRepresentative
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    (K : DerivedCategory C) : CochainComplex C ℤ :=
  (exists_isKInjective_derivedCategory_iso h K).choose

instance kInjectiveRepresentative_isKInjective
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    (K : DerivedCategory C) : (kInjectiveRepresentative h K).IsKInjective :=
  (exists_isKInjective_derivedCategory_iso h K).choose_spec.1

/-- The chosen identification of the localized K-injective representative.
Source: Stacks, Tag 070I (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def kInjectiveRepresentativeIso
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)
    (K : DerivedCategory C) : DerivedCategory.Q.obj (kInjectiveRepresentative h K) ≅ K :=
  (exists_isKInjective_derivedCategory_iso h K).choose_spec.2.some

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (S : D ⥤ C) [S.Additive] (G : C ⥤ D) [G.Additive] (adj : S ⊣ G) [IsIso adj.counit]
  (H : D ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s)

/-- The termwise short complex `F(S(G J)) → G J → H(G J)` given by `a` and `b`, where `J`
is the chosen K-injective representative.
Source: Stacks, Tag 0152 (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationShortComplex (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) (K : DerivedCategory C) :
    ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk
    ((a.mapHomologicalComplex (.up ℤ)).app
      ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K)))
    ((b.mapHomologicalComplex (.up ℤ)).app
      ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K)))
    (by
      ext n
      exact hab _)

/-- The identification of `F` applied to `K` with the first term of the short complex, via
the counit `S(G J) ≅ J`.
Source: Stacks, Tag 070K (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationIsoLeft (K : DerivedCategory C) :
    F.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj
      (((S ⋙ F).mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K))) :=
  F.mapDerivedCategory.mapIso (kInjectiveRepresentativeIso h K).symm ≪≫
    F.mapDerivedCategoryFactors.app (kInjectiveRepresentative h K) ≪≫
    (DerivedCategory.Q.mapIso ((F.mapHomologicalComplex (.up ℤ)).mapIso
      ((NatIso.mapHomologicalComplex (asIso adj.counit) (.up ℤ)).app
        (kInjectiveRepresentative h K)))).symm

/-- The computation of the right derived functor of `G` on the K-injective representative.
Source: Stacks, Tag 070K (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationIsoMiddle (K : DerivedCategory C) :
    (G.rightDerivedFunctorOfQuasiIsoResolutions h).obj K ≅ DerivedCategory.Q.obj
      ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K)) :=
  (G.rightDerivedFunctorOfQuasiIsoResolutions h).mapIso
      (kInjectiveRepresentativeIso h K).symm ≪≫
    G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h (𝟙 (kInjectiveRepresentative h K))

/-- The identification of `H` applied to `RG(K)` with the third term of the short complex.
Source: Stacks, Tag 070K (blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationIsoRight (K : DerivedCategory C) :
    (G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory).obj K ≅
      DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K))) :=
  H.mapDerivedCategory.mapIso (exactLocalizationIsoMiddle G h K) ≪≫
    H.mapDerivedCategoryFactors.app _

set_option backward.isDefEq.respectTransparency false in
/-- The three identifications are natural: every derived morphism is induced by a
morphism of short complexes.
Source: Stacks, Tags 070I and 070K
(blueprint: lem-sf-exact-localization-derived-triangle).

Proof: compute morphisms on K-injectives, where localization is fully faithful (070I),
lift to a cochain map `c` of representatives and apply `G` termwise. The three squares
follow from naturality of the counit, of the computation isomorphism of the universal
right-derived pair, and of the comparison for the exact functor `H`. -/
theorem exactLocalizationShortComplex_naturality (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) {K L : DerivedCategory C} (f : K ⟶ L) :
    ∃ g : exactLocalizationShortComplex F S G H h a b hab K ⟶
        exactLocalizationShortComplex F S G H h a b hab L,
      F.mapDerivedCategory.map f ≫ (exactLocalizationIsoLeft F S G adj h L).hom =
        (exactLocalizationIsoLeft F S G adj h K).hom ≫ DerivedCategory.Q.map g.τ₁ ∧
      (G.rightDerivedFunctorOfQuasiIsoResolutions h).map f ≫
          (exactLocalizationIsoMiddle G h L).hom =
        (exactLocalizationIsoMiddle G h K).hom ≫ DerivedCategory.Q.map g.τ₂ ∧
      (G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory).map f ≫
          (exactLocalizationIsoRight G H h L).hom =
        (exactLocalizationIsoRight G H h K).hom ≫ DerivedCategory.Q.map g.τ₃ := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let RG := G.rightDerivedFunctorOfQuasiIsoResolutions h
  let J := kInjectiveRepresentative h
  let e := kInjectiveRepresentativeIso h
  let counit := NatIso.mapHomologicalComplex (asIso adj.counit) (.up ℤ)
  let qc := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (qc.obj (J K)) (J L)).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app (J K) ≫
        (e K).hom ≫ f ≫ (e L).inv ≫
          (DerivedCategory.quotientCompQhIso C).inv.app (J L))
  obtain ⟨c, rfl⟩ := qc.map_surjective g
  have hc : DerivedCategory.Q.map c = (e K).hom ≫ f ≫ (e L).inv := by
    apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app (J K))).1
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  let gc := Gc.map c
  let m : exactLocalizationShortComplex F S G H h a b hab K ⟶
      exactLocalizationShortComplex F S G H h a b hab L :=
    { τ₁ := ((S ⋙ F).mapHomologicalComplex (.up ℤ)).map gc
      τ₂ := gc
      τ₃ := Hc.map gc
      comm₁₂ := (a.mapHomologicalComplex (.up ℤ)).naturality gc
      comm₂₃ := (b.mapHomologicalComplex (.up ℤ)).naturality gc }
  have heq : f ≫ (e L).inv = (e K).inv ≫ DerivedCategory.Q.map c := by
    rw [hc]
    simp only [Iso.inv_hom_id_assoc]
  have hq : RG.map f ≫ (exactLocalizationIsoMiddle G h L).hom =
      (exactLocalizationIsoMiddle G h K).hom ≫ DerivedCategory.Q.map gc := by
    dsimp only [exactLocalizationIsoMiddle, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hq := computation_naturality G h c
    dsimp only [RG] at *
    rw [← Category.assoc, ← Functor.map_comp, heq,
      Functor.map_comp, Category.assoc, hq]
    dsimp only [gc, Gc]
    simp only [Category.assoc]
    rfl
  refine ⟨m, ?_, hq, ?_⟩
  · have hn := counit.inv.naturality c
    change c ≫ counit.inv.app (J L) = counit.inv.app (J K) ≫ Sc.map (Gc.map c) at hn
    have hn' := congrArg (fun k ↦ DerivedCategory.Q.map (Fc.map k)) hn
    simp only [Functor.map_comp] at hn'
    dsimp only [exactLocalizationIsoLeft, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv]
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, heq, Functor.map_comp]
    simp only [Category.assoc]
    change F.mapDerivedCategory.map (e K).inv ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map c) ≫
        F.mapDerivedCategoryFactors.hom.app (J L) ≫
          DerivedCategory.Q.map (Fc.map (counit.inv.app (J L))) =
      F.mapDerivedCategory.map (e K).inv ≫
        F.mapDerivedCategoryFactors.hom.app (J K) ≫
          DerivedCategory.Q.map (Fc.map (counit.inv.app (J K))) ≫
            DerivedCategory.Q.map (Fc.map (Sc.map (Gc.map c)))
    rw [reassoc_of% (F.mapDerivedCategoryFactors_hom_naturality c)]
    exact congrArg (fun k ↦ F.mapDerivedCategory.map (e K).inv ≫
      F.mapDerivedCategoryFactors.hom.app (J K) ≫ k) hn'
  · dsimp only [exactLocalizationIsoRight, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, hq, Functor.map_comp]
    change (H.mapDerivedCategory.map (exactLocalizationIsoMiddle G h K).hom ≫
      H.mapDerivedCategory.map (DerivedCategory.Q.map gc)) ≫
        H.mapDerivedCategoryFactors.hom.app (Gc.obj (J L)) =
      (H.mapDerivedCategory.map (exactLocalizationIsoMiddle G h K).hom ≫
        H.mapDerivedCategoryFactors.hom.app (Gc.obj (J K))) ≫
          DerivedCategory.Q.map (Hc.map gc)
    rw [Category.assoc, H.mapDerivedCategoryFactors_hom_naturality gc, Category.assoc]

/-- The canonical natural transformation `F ⟶ RG` of the derived exact localization
sequence: on `K` it is `a` applied termwise to `G(J)` for the chosen K-injective
representative `J` of `K`, transported along `exactLocalizationIsoLeft` and
`exactLocalizationIsoMiddle`.
Source: Stacks, Tags 0152 and 070K
(blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationDerivedMor₁ (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) :
    F.mapDerivedCategory ⟶ G.rightDerivedFunctorOfQuasiIsoResolutions h :=
  transportShortComplexMor₁ (T := exactLocalizationShortComplex F S G H h a b hab)
    (p := exactLocalizationIsoLeft F S G adj h) (q := exactLocalizationIsoMiddle G h)
    (r := exactLocalizationIsoRight G H h)
    (exactLocalizationShortComplex_naturality F S G adj H h a b hab)

/-- The canonical natural transformation `RG ⟶ H ∘ RG` of the derived exact localization
sequence: on `K` it is `b` applied termwise to `G(J)`, transported along
`exactLocalizationIsoMiddle` and `exactLocalizationIsoRight`.
Source: Stacks, Tags 0152 and 070K
(blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationDerivedMor₂ (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) :
    G.rightDerivedFunctorOfQuasiIsoResolutions h ⟶
      G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory :=
  transportShortComplexMor₂ (T := exactLocalizationShortComplex F S G H h a b hab)
    (p := exactLocalizationIsoLeft F S G adj h) (q := exactLocalizationIsoMiddle G h)
    (r := exactLocalizationIsoRight G H h)
    (exactLocalizationShortComplex_naturality F S G adj H h a b hab)

/-- The canonical connecting transformation `H ∘ RG ⟶ F[1]`: on `K` it is the connecting
map of the termwise short exact sequence `F(S(G J)) → G J → H(G J)`, transported along
`exactLocalizationIsoRight` and `exactLocalizationIsoLeft`.
Source: Stacks, Tags 0152 and 070K
(blueprint: lem-sf-exact-localization-derived-triangle). -/
noncomputable def exactLocalizationDerivedMor₃ (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0)
    (hseq : ∀ M, (ShortComplex.mk (a.app M) (b.app M) (hab M)).ShortExact) :
    G.rightDerivedFunctorOfQuasiIsoResolutions h ⋙ H.mapDerivedCategory ⟶
      F.mapDerivedCategory ⋙ shiftFunctor (DerivedCategory D) (1 : ℤ) :=
  transportShortComplexMor₃ (T := exactLocalizationShortComplex F S G H h a b hab)
    (p := exactLocalizationIsoLeft F S G adj h) (q := exactLocalizationIsoMiddle G h)
    (r := exactLocalizationIsoRight G H h)
    (fun _ ↦ HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun _ ↦ hseq _))
    (exactLocalizationShortComplex_naturality F S G adj H h a b hab)

theorem exactLocalizationDerivedMor₁_app (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) (K : DerivedCategory C) :
    (exactLocalizationDerivedMor₁ F S G adj H h a b hab).app K =
      (exactLocalizationIsoLeft F S G adj h K).hom ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app
          ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K))) ≫
        (exactLocalizationIsoMiddle G h K).inv :=
  rfl

theorem exactLocalizationDerivedMor₂_app (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0) (K : DerivedCategory C) :
    (exactLocalizationDerivedMor₂ F S G adj H h a b hab).app K =
      (exactLocalizationIsoMiddle G h K).hom ≫
        DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).app
          ((G.mapHomologicalComplex (.up ℤ)).obj (kInjectiveRepresentative h K))) ≫
        (exactLocalizationIsoRight G H h K).inv :=
  rfl

/-- Deriving an exact localization sequence using any supply of K-injective resolutions:
the canonical maps `exactLocalizationDerivedMor₁`, `exactLocalizationDerivedMor₂` and
`exactLocalizationDerivedMor₃`, induced by `a`, `b` and the connecting map of Tag 0152,
form a distinguished triangle `F(K) → RG(K) → H(RG(K)) → F(K)[1]` for every `K`.
Source: Stacks, Tags 0152, 070I and 070K; blueprint proof (1)
(blueprint: lem-sf-exact-localization-derived-triangle).

Proof: Choose a K-injective representative J of K. Apply `a` and `b` in each degree to
G(J). The supplied short exact sequences form a short exact sequence of complexes. Its
distinguished triangle and its natural connecting map are those of Tag 0152. The counit
identifies S(G(J)) with J. Exactness of F and H identifies their derived functors with
termwise application. The computation isomorphism of the universal right-derived pair
identifies the middle complex G(J) with RG. All identifications are natural
(`exactLocalizationShortComplex_naturality`). Transporting the triangle of Tag 0152
along them gives the claim. No product, boundedness or degreewise injectivity
hypothesis is used. -/
theorem exactLocalization_derived_triangle [PreservesFiniteLimits S]
    [PreservesFiniteColimits S] (a : S ⋙ F ⟶ 𝟭 D) (b : 𝟭 D ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0)
    (hseq : ∀ M, (ShortComplex.mk (a.app M) (b.app M) (hab M)).ShortExact)
    (K : DerivedCategory C) :
    Triangle.mk ((exactLocalizationDerivedMor₁ F S G adj H h a b hab).app K)
      ((exactLocalizationDerivedMor₂ F S G adj H h a b hab).app K)
      ((exactLocalizationDerivedMor₃ F S G adj H h a b hab hseq).app K) ∈
        distTriang (DerivedCategory D) :=
  transportShortComplex_distinguished _ _ K

end ExactLocalization

end CategoryTheory
