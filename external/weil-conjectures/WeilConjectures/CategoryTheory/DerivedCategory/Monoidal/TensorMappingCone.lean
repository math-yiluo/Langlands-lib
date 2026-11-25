/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.Linear

/-!
# Derived tensor product with a cone of scalars

Let `A` be a monoidal abelian category with a derived tensor product, linear over a commutative
ring `R`, and let `r : R`. The two-term complex `C_r = cone(r : 𝟙 ⟶ 𝟙)` is K-flat, so that for
every cochain complex `X` the derived tensor product `X ⊗ᴸ C_r` is computed by the tensor product
of complexes, which is the mapping cone of `r : X ⟶ X`.

## Main definitions

- `DerivedCategory.scalarCone`: the complex `cone(r : 𝟙 ⟶ 𝟙)`.
- `DerivedCategory.tensorScalarConeIso'`: the isomorphism of complexes
  `X ⊗ cone(r : 𝟙 ⟶ 𝟙) ≅ cone(r : X ⟶ X)`.

-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits MonoidalCategory

namespace DerivedCategory

open CochainComplex HomComplex mappingCone

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A]
  [MonoidalCategory A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]

local instance instHasColimitsOfSize_tensorMappingCone
    : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

omit [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] [MonoidalCategory A]
  [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [MonoidalLinear R A] in
lemma single_map_smul {X Y : A} (f : X ⟶ Y) (r : R) :
    (HomologicalComplex.single A (.up ℤ) 0).map (r • f) =
      r • (HomologicalComplex.single A (.up ℤ) 0).map f :=
  Functor.map_smul (F := (CochainComplex.singleFunctors A).functor 0) r f

/-- The two-term complex `cone(r : 𝟙 ⟶ 𝟙)`. -/
noncomputable abbrev scalarCone (r : R) : CochainComplex A ℤ :=
  mappingCone ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A)))

omit [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A] [MonoidalLinear R A] in
lemma single_map_smul_id (r : R) :
    (HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A)) =
      r • 𝟙 (𝟙_ (CochainComplex A ℤ)) := by
  rw [single_map_smul, CategoryTheory.Functor.map_id]
  rfl

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] [MonoidalLinear R A] in
lemma kFlat_scalarCone (r : R) :
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
      ((HomotopyCategory.quotient A (.up ℤ)).obj (scalarCone r)) := by
  have h₁ : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat
      ((HomotopyCategory.quotient A (.up ℤ)).obj (𝟙_ (CochainComplex A ℤ))) :=
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.prop_unit
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished
      ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A))))
    h₁ h₁

/-- Tensoring with `scalarCone r` is computed by the tensor product of complexes. -/
instance isIso_μ_scalarCone (X : CochainComplex A ℤ) (r : R) :
    IsIso (Functor.LaxMonoidal.μ (Q : CochainComplex A ℤ ⥤ DerivedCategory A) X
      (scalarCone r)) := by
  have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_right Qh
    (HomotopyCategory.quasiIso A (.up ℤ)) ((HomotopyCategory.quotient A (.up ℤ)).obj X) _
    (kFlat_scalarCone r)
  have h : IsIso (Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient A (.up ℤ)).obj X)
      ((HomotopyCategory.quotient A (.up ℤ)).obj (scalarCone r))) := this
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ Qh _ _ ≫ Qh.map _) ≫ _)
  infer_instance

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
lemma mapBifunctorMap_id_smul_id (X Y : CochainComplex A ℤ) (r : R) :
    HomologicalComplex.mapBifunctorMap (𝟙 X) (r • 𝟙 Y) (curriedTensor A) (.up ℤ) =
      r • 𝟙 (X ⊗ Y) := by
  ext n p q hpq
  simp only [HomologicalComplex.ι_mapBifunctorMap, CategoryTheory.Functor.map_id,
    NatTrans.id_app, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, id_comp,
    curriedTensor_obj_map, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
    Linear.smul_comp]
  rw [Linear.comp_smul]
  erw [id_comp, comp_id]

/-- The isomorphism `X ⊗ cone(r : 𝟙 ⟶ 𝟙) ≅ cone(r : X ⟶ X)`. -/
noncomputable def tensorScalarConeIso' (X : CochainComplex A ℤ) (r : R) :
    X ⊗ scalarCone r ≅ mappingCone (r • 𝟙 X) :=
  mapBifunctorMappingCone₂Iso X ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A)))
    (curriedTensor A) ≪≫
    { hom := mappingCone.map _ _ (ρ_ X).hom (ρ_ X).hom (by
        rw [single_map_smul_id]; erw [mapBifunctorMap_id_smul_id]
        rw [Linear.smul_comp, Linear.comp_smul]
        erw [id_comp, comp_id])
      inv := mappingCone.map _ _ (ρ_ X).inv (ρ_ X).inv (by
        rw [single_map_smul_id]; erw [mapBifunctorMap_id_smul_id]
        rw [Linear.smul_comp, Linear.comp_smul]
        erw [id_comp, comp_id])
      hom_inv_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id]
      inv_hom_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id] }

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
@[reassoc]
lemma tensorScalarConeIso'_hom_naturality {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (r : R) :
    (f ▷ scalarCone r) ≫ (tensorScalarConeIso' Y r).hom =
      (tensorScalarConeIso' X r).hom ≫ mappingCone.map (r • 𝟙 X) (r • 𝟙 Y) f f (by simp) := by
  have h₀ : f ▷ scalarCone r = HomologicalComplex.mapBifunctorMap f
      (mappingCone.map ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A)))
        ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A))) (𝟙 _) (𝟙 _) (by simp))
        (curriedTensor A) (.up ℤ) := by
    rw [mappingCone.map_id]
    rfl
  simp only [tensorScalarConeIso', Iso.trans_hom, assoc]
  rw [h₀, mapBifunctorMappingCone₂Iso_hom_naturality_assoc]
  congr 1
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  congr 1
  · exact MonoidalCategory.rightUnitor_naturality f
  · exact MonoidalCategory.rightUnitor_naturality f

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
@[reassoc]
lemma inr_tensorScalarConeIso'_hom (X : CochainComplex A ℤ) (r : R) :
    (ρ_ X).inv ≫ X ◁ inr ((HomologicalComplex.single A (.up ℤ) 0).map (r • 𝟙 (𝟙_ A))) ≫
      (tensorScalarConeIso' X r).hom = inr (r • 𝟙 X) := by
  simp only [tensorScalarConeIso', Iso.trans_hom]
  erw [mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom_assoc]
  simp [mappingCone.map]

/-- The isomorphism `Q X ⊗ᴸ Q (cone(r : 𝟙 ⟶ 𝟙)) ≅ Q (cone(r : X ⟶ X))`. -/
noncomputable def tensorScalarConeIso (X : CochainComplex A ℤ) (r : R) :
    Q.obj X ⊗ Q.obj (scalarCone r) ≅ Q.obj (mappingCone (r • 𝟙 X)) :=
  asIso (Functor.LaxMonoidal.μ Q X (scalarCone r)) ≪≫ Q.mapIso (tensorScalarConeIso' X r)

@[reassoc]
lemma tensorScalarConeIso_hom_naturality {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (r : R) :
    (Q.map f ▷ Q.obj (scalarCone r)) ≫ (tensorScalarConeIso Y r).hom =
      (tensorScalarConeIso X r).hom ≫
        Q.map (mappingCone.map (r • 𝟙 X) (r • 𝟙 Y) f f (by simp)) := by
  simp only [tensorScalarConeIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Q.map_comp, ← Q.map_comp,
    tensorScalarConeIso'_hom_naturality]

section Reduction

variable {r : R} {M : A} {p : 𝟙_ A ⟶ M} (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
  (hS : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)

/-- The quasi-isomorphism `cone(r : 𝟙 ⟶ 𝟙) ⟶ M` for a short exact sequence
`0 ⟶ 𝟙 ⟶ 𝟙 ⟶ M ⟶ 0` whose first map is `r`. -/
noncomputable abbrev scalarConeDesc :
    scalarCone r ⟶ (HomologicalComplex.single A (.up ℤ) 0).obj M :=
  descShortComplex
    ((ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).map (HomologicalComplex.single A (.up ℤ) 0))

omit [IsGrothendieckAbelian.{v} A] [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [MonoidalLinear R A] in
include hS in
lemma isIso_Q_map_scalarConeDesc : IsIso (Q.map (scalarConeDesc w)) := by
  have := quasiIso_descShortComplex (hS.map_of_exact (HomologicalComplex.single A (.up ℤ) 0))
  infer_instance

/-- The isomorphism `Q X ⊗ᴸ M ≅ Q (cone(r : X ⟶ X))` for a short exact sequence
`0 ⟶ 𝟙 ⟶ 𝟙 ⟶ M ⟶ 0` whose first map is `r`. -/
noncomputable def reductionIso (X : CochainComplex A ℤ) :
    Q.obj X ⊗ Q.obj ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≅
      Q.obj (mappingCone (r • 𝟙 X)) :=
  have := isIso_Q_map_scalarConeDesc w hS
  whiskerLeftIso (Q.obj X) (asIso (Q.map (scalarConeDesc w))).symm ≪≫
    tensorScalarConeIso X r

@[reassoc]
lemma reductionIso_hom_naturality {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    (Q.map f ▷ _) ≫ (reductionIso w hS Y).hom =
      (reductionIso w hS X).hom ≫
        Q.map (mappingCone.map (r • 𝟙 X) (r • 𝟙 Y) f f (by simp)) := by
  simp only [reductionIso, Iso.trans_hom, whiskerLeftIso_hom, assoc]
  rw [← tensorScalarConeIso_hom_naturality, whisker_exchange_assoc]

/-- Under `reductionIso`, the reduction `X ⟶ X ⊗ᴸ M` is the inclusion `X ⟶ cone(r)`. -/
lemma reduction_reductionIso_hom (X : CochainComplex A ℤ) :
    (ρ_ (Q.obj X)).inv ≫ Q.obj X ◁ (Functor.LaxMonoidal.ε Q ≫
        Q.map ((HomologicalComplex.single A (.up ℤ) 0).map p)) ≫ (reductionIso w hS X).hom =
      Q.map (inr (r • 𝟙 X)) := by
  have := isIso_Q_map_scalarConeDesc w hS
  have h₁ : Q.map ((HomologicalComplex.single A (.up ℤ) 0).map p) =
      Q.map (inr _) ≫ Q.map (scalarConeDesc w) := by
    rw [← Q.map_comp]
    exact congrArg Q.map (inr_descShortComplex
      ((ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).map (HomologicalComplex.single A (.up ℤ) 0))).symm
  rw [h₁]
  simp only [reductionIso, tensorScalarConeIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    asIso_inv, asIso_hom, Functor.mapIso_hom, MonoidalCategory.whiskerLeft_comp, assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc (Q.obj X) (Q.map (scalarConeDesc w)),
    IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, id_comp,
    Functor.LaxMonoidal.μ_natural_right_assoc]
  erw [Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← Q.map_comp, ← Q.map_comp, inr_tensorScalarConeIso'_hom]

end Reduction

section ChangeOfScalar

variable {r₁ r₂ s : R} (hr : r₂ * s = r₁)
  {M₁ M₂ : A} {p₁ : 𝟙_ A ⟶ M₁} {p₂ : 𝟙_ A ⟶ M₂} (w₁ : (r₁ • 𝟙 (𝟙_ A)) ≫ p₁ = 0)
  (w₂ : (r₂ • 𝟙 (𝟙_ A)) ≫ p₂ = 0)
  (hS₁ : (ShortComplex.mk (r₁ • 𝟙 (𝟙_ A)) p₁ w₁).ShortExact)
  (hS₂ : (ShortComplex.mk (r₂ • 𝟙 (𝟙_ A)) p₂ w₂).ShortExact)
  (q : M₁ ⟶ M₂) (hq : p₁ ≫ q = p₂)

omit [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] [MonoidalCategory A]
  [MonoidalClosed A] [MonoidalPreadditive A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [MonoidalLinear R A] in
include hr in
lemma smul_comp_smul_eq (X : A) : (s • 𝟙 X) ≫ (r₂ • 𝟙 X) = (r₁ • 𝟙 X) ≫ 𝟙 X := by
  rw [comp_id, Linear.smul_comp, id_comp, smul_smul, mul_comm, hr]

/-- The morphism of short complexes `(r₁, p₁) ⟶ (r₂, p₂)` given by `s`, `𝟙` and `q`. -/
@[simps]
noncomputable def scalarShortComplexMap :
    ShortComplex.mk (r₁ • 𝟙 (𝟙_ A)) p₁ w₁ ⟶ ShortComplex.mk (r₂ • 𝟙 (𝟙_ A)) p₂ w₂ where
  τ₁ := s • 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := q
  comm₁₂ := smul_comp_smul_eq hr _
  comm₂₃ := by simp [hq]

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
omit [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [MonoidalLinear R A] in
include hr in
lemma single_smul_comm :
    (HomologicalComplex.single A (.up ℤ) 0).map (r₁ • 𝟙 (𝟙_ A)) ≫ 𝟙 _ =
      (HomologicalComplex.single A (.up ℤ) 0).map (s • 𝟙 (𝟙_ A)) ≫
        (HomologicalComplex.single A (.up ℤ) 0).map (r₂ • 𝟙 (𝟙_ A)) := by
  rw [← CategoryTheory.Functor.map_comp, smul_comp_smul_eq hr, comp_id, comp_id]

omit [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A] in
include hr in
/-- The map `cone(r₁ : 𝟙 ⟶ 𝟙) ⟶ cone(r₂ : 𝟙 ⟶ 𝟙)` given by `s` is compatible with
`tensorScalarConeIso'`. -/
lemma whiskerLeft_tensorScalarConeIso'_hom (X : CochainComplex A ℤ) :
    X ◁ mappingCone.map ((HomologicalComplex.single A (.up ℤ) 0).map (r₁ • 𝟙 (𝟙_ A)))
        ((HomologicalComplex.single A (.up ℤ) 0).map (r₂ • 𝟙 (𝟙_ A)))
        ((HomologicalComplex.single A (.up ℤ) 0).map (s • 𝟙 (𝟙_ A))) (𝟙 _)
        (single_smul_comm hr) ≫
        (tensorScalarConeIso' X r₂).hom =
      (tensorScalarConeIso' X r₁).hom ≫ mappingCone.map (r₁ • 𝟙 X) (r₂ • 𝟙 X) (s • 𝟙 X)
        (𝟙 X) (smul_comp_smul_eq hr X).symm := by
  have h := mapBifunctorMappingCone₂Iso_hom_naturality (curriedTensor A) (𝟙 X)
    ((HomologicalComplex.single A (.up ℤ) 0).map (r₁ • 𝟙 (𝟙_ A)))
    ((HomologicalComplex.single A (.up ℤ) 0).map (r₂ • 𝟙 (𝟙_ A)))
    ((HomologicalComplex.single A (.up ℤ) 0).map (s • 𝟙 (𝟙_ A))) (𝟙 _)
    (single_smul_comm hr)
  simp only [tensorScalarConeIso', Iso.trans_hom, assoc]
  erw [reassoc_of% h]
  congr 1
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  congr 1
  · rw [single_map_smul, CategoryTheory.Functor.map_id]
    erw [mapBifunctorMap_id_smul_id]
    rw [Linear.smul_comp, Linear.comp_smul]
    erw [id_comp, comp_id]
  · ext n p q hpq
    simp

include hr hq in
/-- `reductionIso` is compatible with a change of the scalar `r₁ = r₂ s`. -/
lemma whiskerLeft_reductionIso_hom (X : CochainComplex A ℤ) :
    (Q.obj X ◁ Q.map ((HomologicalComplex.single A (.up ℤ) 0).map q)) ≫
        (reductionIso w₂ hS₂ X).hom =
      (reductionIso w₁ hS₁ X).hom ≫ Q.map (mappingCone.map (r₁ • 𝟙 X) (r₂ • 𝟙 X) (s • 𝟙 X)
        (𝟙 X) (smul_comp_smul_eq hr X).symm) := by
  have := isIso_Q_map_scalarConeDesc w₁ hS₁
  have := isIso_Q_map_scalarConeDesc w₂ hS₂
  have hd := mappingCone.descShortComplex_naturality
    ((HomologicalComplex.single A (.up ℤ) 0).mapShortComplex.map
      (scalarShortComplexMap hr w₁ w₂ q hq))
  have hd' : Q.map ((HomologicalComplex.single A (.up ℤ) 0).map q) ≫
      inv (Q.map (scalarConeDesc w₂)) = inv (Q.map (scalarConeDesc w₁)) ≫
        Q.map (mappingCone.map ((HomologicalComplex.single A (.up ℤ) 0).map (r₁ • 𝟙 (𝟙_ A)))
        ((HomologicalComplex.single A (.up ℤ) 0).map (r₂ • 𝟙 (𝟙_ A)))
        ((HomologicalComplex.single A (.up ℤ) 0).map (s • 𝟙 (𝟙_ A))) (𝟙 _)
        (single_smul_comm hr)) := by
    rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp, ← Q.map_comp, ← Q.map_comp]
    congr 1
    simp only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₂,
      Functor.mapShortComplex_map_τ₃, scalarShortComplexMap_τ₁, scalarShortComplexMap_τ₂,
      scalarShortComplexMap_τ₃, CategoryTheory.Functor.map_id] at hd
    exact hd.symm
  simp only [reductionIso, tensorScalarConeIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    asIso_inv, asIso_hom, Functor.mapIso_hom, assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hd', MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Q.map_comp, ← Q.map_comp,
    whiskerLeft_tensorScalarConeIso'_hom hr]

end ChangeOfScalar

end DerivedCategory
