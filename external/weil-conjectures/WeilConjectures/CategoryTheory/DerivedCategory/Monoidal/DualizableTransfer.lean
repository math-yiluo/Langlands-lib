/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Transferring dualizability along exact monoidal functors

Let `G : C ⥤ D` be an exact monoidal functor between braided monoidal closed Grothendieck
abelian categories with functorial flat resolutions, with an exact left adjoint `L` such that
`G` commutes with internal homs (equivalently, the projection maps of `L ⊣ G` are isomorphisms).
This is the situation of the pullback along a weakly étale morphism of pro-étale sheaves.

We show that for a K-flat complex `P` of `C` whose image `G P` is K-flat, there is a single
morphism of complexes `χ` such that `Q P` is dualizable in `D(C)` if and only if `χ` is a
quasi-isomorphism, and `Q (G P)` is dualizable in `D(D)` if and only if `G χ` is a
quasi-isomorphism (`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_iff` and
`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`). The morphism `χ` is the
chain-level model of the comparison `[P, 𝟙] ⊗ P ⟶ [P, P]` of the criterion
`DerivedCategory.isDualizable_Qh_obj_iff`. As `G` is exact, dualizability is therefore preserved
by `G`, and it is detected by a family of such functors which jointly reflects
quasi-isomorphisms.

## Main definitions

- `CochainComplex.monoidalClosed`: the monoidal closed structure on cochain complexes given by
  the internal hom complexes `CochainComplex.internalHom`.
- `DerivedCategory.DualizabilityDatum P`: the chain-level data of the criterion.

## Main statements

- `CochainComplex.isKInjective_map_of_adjunction`: a functor with an exact left adjoint
  preserves K-injective complexes.
- `DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_iff`,
  `DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace CochainComplex

section MonoidalClosed

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The monoidal closed structure on cochain complexes: the internal hom out of `P` is the
internal hom complex `CochainComplex.internalHom P`. -/
@[instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (CochainComplex C ℤ) where
  closed P := ⟨internalHom P, tensorHomAdjunction P⟩

end MonoidalClosed

section KInjective

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] (adj : L ⊣ G)

include adj in
/-- A functor `G` with an exact left adjoint `L` preserves K-injective complexes: a morphism
`K ⟶ G I` from an acyclic complex is the transpose of a morphism `L K ⟶ I`, which is
null-homotopic as `L K` is acyclic. -/
lemma isKInjective_map_of_adjunction (I : CochainComplex C ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I) where
  nonempty_homotopy_zero {K} f hK := by
    let adj' := adj.mapHomologicalComplex (.up ℤ)
    have hLK : ((L.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
      intro n
      exact (hK n).map L
    let h := IsKInjective.homotopyZero ((adj'.homEquiv _ _).symm f) hLK
    have hf : f = adj'.unit.app K ≫ (G.mapHomologicalComplex (.up ℤ)).map
        ((adj'.homEquiv _ _).symm f) :=
      ((adj'.homEquiv _ _).apply_symm_apply f).symm.trans (adj'.homEquiv_unit _ _ _)
    rw [hf]
    exact ⟨((G.mapHomotopy h).compLeft (adj'.unit.app K)).trans (.ofEq (by simp))⟩

end KInjective

end CochainComplex

namespace DerivedCategory

open HomotopyCategory CochainComplex MonoidalClosed HomotopyCategory.MonoidalCategory

section Datum

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance instHasColimitsOfSize_monoidalDualizableTransfer
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

/-- The chain-level data of the dualizability criterion `DerivedCategory.isDualizable_Qh_obj_iff`
for a complex `P`: K-injective resolutions `u : 𝟙 ⟶ I₁` and `i : P ⟶ I`, a map
`j : I₁ ⊗ P ⟶ I` with `u ▷ P ≫ j ∼ λ ≫ i`, and the transpose
`χ : iHom(P, I₁) ⊗ P ⟶ iHom(P, I)` of `P ⊗ (iHom(P, I₁) ⊗ P) ⟶ (P ⊗ iHom(P, I₁)) ⊗ P ⟶ I₁ ⊗ P
⟶ I`, up to homotopy. -/
structure DualizabilityDatum (P : CochainComplex C ℤ) where
  /-- a K-injective resolution of the unit -/
  I₁ : CochainComplex C ℤ
  /-- a K-injective resolution of `P` -/
  I : CochainComplex C ℤ
  isKInjective₁ : I₁.IsKInjective
  isKInjective : I.IsKInjective
  /-- the resolution of the unit -/
  u : 𝟙_ (CochainComplex C ℤ) ⟶ I₁
  quasiIso_u : QuasiIso u
  /-- the resolution of `P` -/
  i : P ⟶ I
  quasiIso_i : QuasiIso i
  /-- the action of the unit on `P`, in the resolutions -/
  j : I₁ ⊗ P ⟶ I
  hj : (HomotopyCategory.quotient C (.up ℤ)).map (u ▷ P ≫ j) =
    (HomotopyCategory.quotient C (.up ℤ)).map ((λ_ P).hom ≫ i)
  /-- the chain-level model of `[P, 𝟙] ⊗ P ⟶ [P, P]` -/
  χ : internalHomObj P I₁ ⊗ P ⟶ internalHomObj P I
  hχ : (HomotopyCategory.quotient C (.up ℤ)).map
      (P ◁ χ ≫ (CochainComplex.tensorHomAdjunction P).counit.app I) =
    (HomotopyCategory.quotient C (.up ℤ)).map
      ((α_ _ _ _).inv ≫ (CochainComplex.tensorHomAdjunction P).counit.app I₁ ▷ P ≫ j)

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
lemma quotient_associator_inv (K L M : CochainComplex C ℤ) :
    (α_ ((HomotopyCategory.quotient C (.up ℤ)).obj K) ((HomotopyCategory.quotient C (.up ℤ)).obj L)
      ((HomotopyCategory.quotient C (.up ℤ)).obj M)).inv =
      (HomotopyCategory.quotient C (.up ℤ)).map (α_ K L M).inv := by
  rw [← cancel_mono (α_ _ _ _).hom, Iso.inv_hom_id, quotient_associator_hom,
    ← Functor.map_comp, Iso.inv_hom_id]
  exact ((HomotopyCategory.quotient C (.up ℤ)).map_id _).symm

omit [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
lemma isLocal_quotient_obj_of_isKInjective (I : CochainComplex C ℤ) [I.IsKInjective] :
    (quasiIso C (.up ℤ)).isLocal ((HomotopyCategory.quotient C (.up ℤ)).obj I) := by
  rw [quasiIso_eq_trW_subcategoryAcyclic, ObjectProperty.isLocal_trW]
  exact (isKInjective_iff_rightOrthogonal I).1 inferInstance

omit [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
lemma isIso_Qh_map_quotient_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map φ)) ↔ QuasiIso φ := by
  rw [← isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (quotientCompQhIso C) φ

/-- **The chain-level dualizability criterion.** For a K-flat complex `P` and a
`DualizabilityDatum P`, `Q P` is dualizable if and only if `χ` is a quasi-isomorphism. -/
theorem DualizabilityDatum.isDualizable_Q_obj_iff {P : CochainComplex C ℤ}
    (d : DualizabilityDatum P)
    (hP : (quasiIso C (.up ℤ)).kFlat ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :
    IsDualizable (Q.obj P) ↔ QuasiIso d.χ := by
  have := d.isKInjective₁
  have := d.isKInjective
  have := d.quasiIso_u
  have := d.quasiIso_i
  have : IsIso (Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map d.u)) :=
    (isIso_Qh_map_quotient_map_iff _).2 inferInstance
  have : IsIso (Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map d.i)) :=
    (isIso_Qh_map_quotient_map_iff _).2 inferInstance
  rw [← isIso_Qh_map_quotient_map_iff]
  refine Iff.trans ⟨fun h ↦ h.of_iso ((quotientCompQhIso C).app P).symm,
    fun h ↦ h.of_iso ((quotientCompQhIso C).app P)⟩ ?_
  refine isDualizable_Qh_obj_iff hP (isLocal_quotient_obj_of_isKInjective _)
    (isLocal_quotient_obj_of_isKInjective _) ((HomotopyCategory.quotient C (.up ℤ)).map d.u)
    ((HomotopyCategory.quotient C (.up ℤ)).map d.i)
    ((HomotopyCategory.quotient C (.up ℤ)).map d.j) ?_
    ((HomotopyCategory.quotient C (.up ℤ)).map d.χ) ?_
  · have h := d.hj
    have hlu : (λ_ ((HomotopyCategory.quotient C (.up ℤ)).obj P)).hom =
        (HomotopyCategory.quotient C (.up ℤ)).map (λ_ P).hom :=
      HomotopyCategory.MonoidalCategory.leftUnitor_hom_app P
    rw [Functor.map_comp, Functor.map_comp, quotient_map_whiskerRight', ← hlu] at h
    exact h
  · have h := d.hχ
    rw [HomotopyCategory.tensorHomAdjunction_counit_app,
      HomotopyCategory.tensorHomAdjunction_counit_app, ← quotient_map_whiskerLeft',
      ← quotient_map_whiskerRight']
    erw [quotient_associator_inv P (internalHomObj P d.I₁) P]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact h

end Datum

section Homotopic

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive]

/-- If two morphisms of complexes are homotopic, so are their images under `G`, after
precomposition with any morphism. -/
lemma quotient_map_comp_map_eq {X : CochainComplex D ℤ} {Y Z : CochainComplex C ℤ}
    (A : X ⟶ (G.mapHomologicalComplex (.up ℤ)).obj Y) {x y : Y ⟶ Z}
    (h : (HomotopyCategory.quotient C (.up ℤ)).map x =
      (HomotopyCategory.quotient C (.up ℤ)).map y) :
    (HomotopyCategory.quotient D (.up ℤ)).map (A ≫ (G.mapHomologicalComplex (.up ℤ)).map x) =
      (HomotopyCategory.quotient D (.up ℤ)).map (A ≫ (G.mapHomologicalComplex (.up ℤ)).map y) := by
  rw [Functor.map_comp, Functor.map_comp, ← Functor.mapHomotopyCategory_map, h,
    Functor.mapHomotopyCategory_map]

end Homotopic

section Transfer

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u'} [Category.{v} D] [Abelian D] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasDerivedCategory.{v} D] [Abelian.HasFunctorialFlatResolution D]
  (G : C ⥤ D) [G.Additive] [G.Monoidal] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  {L : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ G)
  [∀ X : C, IsIso (ihomComparison G X)]

local instance instHasColimitsOfSize_monoidalDualizableTransfer_2
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C
local instance instHasColimitsOfSize_monoidalDualizableTransfer_3
    : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeShrink D

attribute [local instance] CochainComplex.monoidalClosed

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} D]
  [Abelian.HasFunctorialFlatResolution D] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
include adj in
/-- The functor induced by `G` on cochain complexes commutes with internal hom complexes: its
left adjoint satisfies the projection formula degreewise. -/
lemma isIso_ihomComparison_mapHomologicalComplex (P : CochainComplex C ℤ) :
    IsIso (ihomComparison (G.mapHomologicalComplex (.up ℤ)) P) := by
  have (X : C) : IsIso (Functor.Monoidal.projectionMap adj X) :=
    Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adj X
  have := adj.leftAdjoint_preservesColimits
  have := Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex G adj P
  exact Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap
    (adj.mapHomologicalComplex (.up ℤ)) P


-- Checking the fields of the mapped datum unfolds the monoidal structure of
-- `G.mapHomologicalComplex`.
variable {G} in
/-- The image of a `DualizabilityDatum P` under `G`: the resolutions are mapped by `G` (which
preserves quasi-isomorphisms and, having an exact left adjoint, K-injective complexes), and the
model `χ` of `[P, 𝟙] ⊗ P ⟶ [P, P]` is `G χ`, up to the isomorphisms
`G iHom(P, Y) ≅ iHom(G P, G Y)`. -/
noncomputable def DualizabilityDatum.map {P : CochainComplex C ℤ} (d : DualizabilityDatum P) :
    DualizabilityDatum ((G.mapHomologicalComplex (.up ℤ)).obj P) := by
  let G' := G.mapHomologicalComplex (.up ℤ)
  have := isIso_ihomComparison_mapHomologicalComplex G adj P
  have := d.isKInjective₁
  have := d.isKInjective
  have := d.quasiIso_u
  have := d.quasiIso_i
  let c (Y : CochainComplex C ℤ) : G'.obj (internalHomObj P Y) ⟶
      internalHomObj (G'.obj P) (G'.obj Y) :=
    (ihomComparison G' P).app Y
  exact
  { I₁ := G'.obj d.I₁
    I := G'.obj d.I
    isKInjective₁ := isKInjective_map_of_adjunction G adj _
    isKInjective := isKInjective_map_of_adjunction G adj _
    u := ε G' ≫ G'.map d.u
    quasiIso_u := inferInstance
    i := G'.map d.i
    quasiIso_i := inferInstance
    j := μ G' _ _ ≫ G'.map d.j
    hj := by
      have e₁ : (ε G' ≫ G'.map d.u) ▷ G'.obj P ≫ μ G' _ _ ≫ G'.map d.j =
          (ε G' ▷ G'.obj P ≫ μ G' _ _) ≫ G'.map (d.u ▷ P ≫ d.j) := by
        rw [comp_whiskerRight, Category.assoc, Category.assoc, μ_natural_left_assoc,
          Functor.map_comp]
      have e₂ : (λ_ (G'.obj P)).hom ≫ G'.map d.i =
          (ε G' ▷ G'.obj P ≫ μ G' _ _) ≫ G'.map ((λ_ P).hom ≫ d.i) := by
        rw [left_unitality, Functor.map_comp]
        simp only [Category.assoc]
      rw [e₁, e₂]
      exact quotient_map_comp_map_eq G _ d.hj
    χ := inv (c d.I₁) ▷ G'.obj P ≫ μ G' _ _ ≫ G'.map d.χ ≫ c d.I
    hχ := by
      have hc (Y : CochainComplex C ℤ) : G'.obj P ◁ c Y ≫
          (CochainComplex.tensorHomAdjunction (G'.obj P)).counit.app (G'.obj Y) =
          μ G' P _ ≫ G'.map ((CochainComplex.tensorHomAdjunction P).counit.app Y) :=
        ihomComparison_ev G' P Y
      have hc₁ : G'.obj P ◁ inv (c d.I₁) ≫ μ G' P _ ≫
          G'.map ((CochainComplex.tensorHomAdjunction P).counit.app d.I₁) =
          (CochainComplex.tensorHomAdjunction (G'.obj P)).counit.app (G'.obj d.I₁) := by
        erw [← hc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
          MonoidalCategory.whiskerLeft_id, Category.id_comp]
      let W := G'.obj P ◁ (inv (c d.I₁) ▷ G'.obj P) ≫ G'.obj P ◁ μ G' _ _ ≫ μ G' _ _
      have eA : G'.obj P ◁ (inv (c d.I₁) ▷ G'.obj P ≫ μ G' _ _ ≫ G'.map d.χ ≫ c d.I) ≫
          (CochainComplex.tensorHomAdjunction (G'.obj P)).counit.app (G'.obj d.I) =
          W ≫ G'.map (P ◁ d.χ ≫ (CochainComplex.tensorHomAdjunction P).counit.app d.I) := by
        simp only [W, MonoidalCategory.whiskerLeft_comp, Category.assoc, hc, Functor.map_comp]
        erw [μ_natural_right_assoc]
      have eB : (α_ _ _ _).inv ≫
          (CochainComplex.tensorHomAdjunction (G'.obj P)).counit.app (G'.obj d.I₁) ▷ G'.obj P ≫
          μ G' _ _ ≫ G'.map d.j = W ≫ G'.map ((α_ _ _ _).inv ≫
            (CochainComplex.tensorHomAdjunction P).counit.app d.I₁ ▷ P ≫ d.j) := by
        simp only [W, Functor.map_comp, Category.assoc, associativity_inv_assoc,
          ← μ_natural_left_assoc, associator_inv_naturality_middle_assoc,
          ← comp_whiskerRight_assoc, hc₁]
        rfl
      rw [eA, eB]
      exact quotient_map_comp_map_eq G _ d.hχ }

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
include adj in
/-- **Transfer of the dualizability criterion along `G`.** For a `DualizabilityDatum P` and `P`
such that `G P` is K-flat, `Q (G P)` is dualizable if and only if `G χ` is a
quasi-isomorphism. -/
theorem DualizabilityDatum.isDualizable_Q_obj_map_iff {P : CochainComplex C ℤ}
    (d : DualizabilityDatum P)
    (hGP : (quasiIso D (.up ℤ)).kFlat
      ((HomotopyCategory.quotient D (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj P))) :
    IsDualizable (Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) ↔
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map d.χ) := by
  have := isIso_ihomComparison_mapHomologicalComplex G adj P
  rw [(d.map adj).isDualizable_Q_obj_iff hGP]
  dsimp only [DualizabilityDatum.map]
  rw [quasiIso_iff_comp_left, quasiIso_iff_comp_left, quasiIso_iff_comp_right]

end Transfer

section Existence

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance instHasColimitsOfSize_monoidalDualizableTransfer_4
    : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

omit [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] in
/-- A K-flat complex admits a `DualizabilityDatum`: take K-injective resolutions of the unit and
of `P`; the map `j` exists as `u ▷ P` is a quasi-isomorphism and the target is K-injective, and
`χ` is a transpose in the homotopy category. -/
theorem DualizabilityDatum.nonempty (P : CochainComplex C ℤ)
    (hP : (quasiIso C (.up ℤ)).kFlat ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :
    Nonempty (DualizabilityDatum P) := by
  obtain ⟨I₁, _, u, -, hu⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective (𝟙_ (CochainComplex C ℤ))
  obtain ⟨I, _, i, -, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective P
  have : QuasiIso u := hu
  have : QuasiIso i := hi
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hs : quasiIso C (.up ℤ) (q.map (u ▷ P)) := by
    rw [quotient_map_whiskerRight']
    exact hP.whiskerRight ((quotient_map_mem_quasiIso_iff _).2 hu)
  obtain ⟨j₀, hj₀⟩ := (isLocal_quotient_obj_of_isKInjective I _ hs).2 (q.map ((λ_ P).hom ≫ i))
  obtain ⟨j, rfl⟩ := q.map_surjective j₀
  let adj := HomotopyCategory.tensorHomAdjunction (q.obj P)
  obtain ⟨χ, hχ⟩ := q.map_surjective (adj.homEquiv _ _
    ((α_ _ _ _).inv ≫ adj.counit.app (q.obj I₁) ▷ q.obj P ≫ q.map j))
  refine ⟨⟨I₁, I, inferInstance, inferInstance, u, inferInstance, i, inferInstance, j,
    (Functor.map_comp _ _ _).trans hj₀, χ, ?_⟩⟩
  have e : q.map (P ◁ χ ≫ (CochainComplex.tensorHomAdjunction P).counit.app I) =
      (adj.homEquiv _ _).symm (q.map χ) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, quotient_map_whiskerLeft']
    erw [HomotopyCategory.tensorHomAdjunction_counit_app]
    rfl
  rw [e, hχ, Equiv.symm_apply_apply, HomotopyCategory.tensorHomAdjunction_counit_app,
    Functor.map_comp, Functor.map_comp, quotient_map_whiskerRight']
  erw [quotient_associator_inv]
  rfl

end Existence

end DerivedCategory
