/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Coherence of derived scalar extension on the pro-étale site

For ring sheaves `R`, `S`, `U` on the small pro-étale site of `Y`, derived scalar extension
`reductionDerivedChange` is pseudo-functorial:

* `reductionDerivedChange_comp_existsUnique`: for `φ ≫ ψ = χ` there is a unique natural
  isomorphism `L ψ ∘ L φ ≅ L χ` whose value on every complex is the ordinary balancing map
  `s ⊗ (r ⊗ x) ↦ s ψ(r) ⊗ x` read through the universal counits;
* `reductionDerivedChange_id_existsUnique`: for `φ = 𝟙 R` there is a unique natural
  isomorphism `L φ ≅ 𝟭` whose value on every complex is the multiplication map
  `a ⊗ x ↦ a • x` read through the universal counit.

Source: Stacks Tag 06YY (blueprint: lem-sf-field-stage-ordinary-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] reductionModulesHasDerivedCategory

variable (Y : Scheme.{u})

/-- The universal scalar-extension counit on complex representatives is natural.
Source: Stacks Tag 06YY (blueprint: lem-sf-field-stage-ordinary-realization).
Proof: it is the component of the natural transformation obtained by whiskering the
universal homotopy counit along the quotient functor. -/
theorem reductionScalarComplexCounit_naturality
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {P P' : CochainComplex (reductionModules Y R) ℤ} (p : P' ⟶ P) :
    (reductionDerivedChange Y φ).map (DerivedCategory.Q.map p) ≫
        reductionScalarComplexCounit Y φ P =
      reductionScalarComplexCounit Y φ P' ≫
        DerivedCategory.Q.map ((reductionChangeComplex Y φ).map p) := by
  have h := (complexCounitNat (reductionChange Y φ) (reductionDerivedChange Y φ)
    (reductionDerivedCounit Y φ)).naturality p
  rw [complexCounitNat_app, complexCounitNat_app] at h
  exact h

/-- Derived scalar extension along a composite is the composite of derived scalar
extensions, by a unique isomorphism given on every complex by ordinary balancing.
Source: Stacks Tag 06YY (blueprint: lem-sf-field-stage-ordinary-realization).
Proof: the K-flat statement is `derivedReductionComposition`. For an arbitrary complex
take a K-flat resolution; naturality of the counits and of balancing transport the
equation along it. Uniqueness already holds on K-flat complexes. -/
theorem reductionDerivedChange_comp_existsUnique
    {R S U : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ) :
    ∃! e : reductionDerivedChange Y φ ⋙ reductionDerivedChange Y ψ ≅
        reductionDerivedChange Y χ,
      ∀ P : CochainComplex (reductionModules Y R) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit Y χ P =
          (reductionDerivedChange Y ψ).map (reductionScalarComplexCounit Y φ P) ≫
            reductionScalarComplexCounit Y ψ ((reductionChangeComplex Y φ).obj P) ≫
            DerivedCategory.Q.map (reductionBalance Y φ ψ χ h P) := by
  obtain ⟨τ, ⟨hτ, hτP⟩, huniq⟩ := derivedReductionComposition Y φ ψ χ h
  have hall (P : CochainComplex (reductionModules Y R) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit Y χ P =
        (reductionDerivedChange Y ψ).map (reductionScalarComplexCounit Y φ P) ≫
          reductionScalarComplexCounit Y ψ ((reductionChangeComplex Y φ).obj P) ≫
          DerivedCategory.Q.map (reductionBalance Y φ ψ χ h P) := by
    obtain ⟨P', p, hk, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    have : IsIso (DerivedCategory.Q.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
    apply (cancel_epi ((reductionDerivedChange Y φ ⋙ reductionDerivedChange Y ψ).map
      (DerivedCategory.Q.map p))).1
    have n0 := τ.naturality (DerivedCategory.Q.map p)
    have n1 := reductionScalarComplexCounit_naturality Y φ p
    have n2 := reductionScalarComplexCounit_naturality Y ψ
      ((reductionChangeComplex Y φ).map p)
    have n3 := reductionBalance_naturality Y φ ψ χ h p
    have n4 := reductionScalarComplexCounit_naturality Y χ p
    rw [CategoryTheory.Functor.comp_map, reassoc_of% n0, n4, reassoc_of% (hτP P' hk),
      ← CategoryTheory.Functor.map_comp_assoc, n1, CategoryTheory.Functor.map_comp_assoc,
      reassoc_of% n2,
      ← CategoryTheory.Functor.map_comp DerivedCategory.Q, ← n3,
      CategoryTheory.Functor.map_comp]
  refine ⟨asIso τ, hall, ?_⟩
  intro e he
  apply Iso.ext
  exact huniq e.hom ⟨inferInstance, fun P _ ↦ he P⟩


section Identity

variable {Y} {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}

/-- A module sheaf includes into its restriction along the identity, by the identity on
sections. Source: Stacks Tag 03DA (blueprint: lem-sf-field-stage-ordinary-realization). -/
private def restrictIdInclusion (M : reductionModules Y R) :
    M ⟶ (reductionRestrict Y (𝟙 R)).obj M :=
  ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf _).map (𝟙 M.val)) (by
    intro V r x
    rfl)⟩

/-- Restriction along the identity maps back by the identity on sections.
Source: Stacks Tag 03DA (blueprint: lem-sf-field-stage-ordinary-realization). -/
private def restrictIdProjection (M : reductionModules Y R) :
    (reductionRestrict Y (𝟙 R)).obj M ⟶ M :=
  ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf _).map (𝟙 M.val)) (by
    intro V r x
    rfl)⟩

/-- Multiplication `a ⊗ x ↦ a • x` out of scalar extension along the identity. -/
private def changeIdCounit (M : reductionModules Y R) :
    (reductionChange Y (𝟙 R)).obj M ⟶ M :=
  ((ordinaryAdjunction_exists Y (𝟙 R)).choose.homEquiv M M).symm (restrictIdInclusion M)

/-- The unit `x ↦ 1 ⊗ x` into scalar extension along the identity. -/
private def changeIdUnit (M : reductionModules Y R) :
    M ⟶ (reductionChange Y (𝟙 R)).obj M :=
  reductionUnit Y (𝟙 R) M ≫ restrictIdProjection _

private theorem changeIdUnit_apply (M : reductionModules Y R) (V : Y.ProEtᵒᵖ)
    (x : M.val.obj V) :
    (changeIdUnit M).val.app V x = reductionTensorSection Y (𝟙 R) M V 1 x :=
  reductionUnit_apply Y (𝟙 R) M V x

private theorem changeIdCounit_apply (M : reductionModules Y R) (V : Y.ProEtᵒᵖ)
    (a : R.obj.obj V) (x : M.val.obj V) :
    (changeIdCounit M).val.app V (reductionTensorSection Y (𝟙 R) M V a x) = a • x := by
  have hb : (changeIdCounit M).val.app V (reductionTensorSection Y (𝟙 R) M V 1 x) = x := by
    have hh := (ordinaryAdjunction_exists Y (𝟙 R)).choose_spec M M (changeIdCounit M) V x
    rw [changeIdCounit, Equiv.apply_symm_apply] at hh
    exact (eq_of_heq hh).symm
  have ht := tensorSection_smul Y (𝟙 R) M V a 1 x
  rw [mul_one] at ht
  rw [← ht, map_smul, hb]

private theorem tensorSection_one_smul (M : reductionModules Y R) (V : Y.ProEtᵒᵖ)
    (r : R.obj.obj V) (x : M.val.obj V) :
    reductionTensorSection Y (𝟙 R) M V 1 (r • x) =
      reductionTensorSection Y (𝟙 R) M V r x := by
  rw [← reductionUnit_apply, map_smul]
  change (𝟙 R : R ⟶ R).hom.app V r •
      (show ((reductionChange Y (𝟙 R)).obj M).val.obj V from
        (reductionUnit Y (𝟙 R) M).val.app V x) = _
  rw [reductionUnit_apply, tensorSection_smul, mul_one]
  rfl

private theorem changeIdCounit_unit (M : reductionModules Y R) :
    changeIdUnit M ≫ changeIdCounit M = 𝟙 M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (changeIdCounit M).val.app V ((changeIdUnit M).val.app V x) = x
  rw [changeIdUnit_apply, changeIdCounit_apply, one_smul]

private theorem changeIdUnit_counit (M : reductionModules Y R) :
    changeIdCounit M ≫ changeIdUnit M = 𝟙 _ := by
  apply (SheafOfModules.toSheaf (reductionModuleRing Y R)).map_injective
  apply reductionTensor_hom_ext Y (𝟙 R) M
  intro V s x
  change (changeIdUnit M).val.app V ((changeIdCounit M).val.app V
    (reductionTensorSection Y (𝟙 R) M V s x)) = reductionTensorSection Y (𝟙 R) M V s x
  rw [changeIdCounit_apply, changeIdUnit_apply, tensorSection_one_smul]

private theorem changeIdCounit_naturality {M N : reductionModules Y R} (f : M ⟶ N) :
    (reductionChange Y (𝟙 R)).map f ≫ changeIdCounit N = changeIdCounit M ≫ f := by
  apply (SheafOfModules.toSheaf (reductionModuleRing Y R)).map_injective
  apply reductionTensor_hom_ext Y (𝟙 R) M
  intro V s x
  change (changeIdCounit N).val.app V (((reductionChange Y (𝟙 R)).map f).val.app V
      (reductionTensorSection Y (𝟙 R) M V s x)) =
    f.val.app V ((changeIdCounit M).val.app V (reductionTensorSection Y (𝟙 R) M V s x))
  rw [reductionTensor_map, changeIdCounit_apply, changeIdCounit_apply, map_smul]

private theorem changeIdUnit_naturality {M N : reductionModules Y R} (f : M ⟶ N) :
    f ≫ changeIdUnit N = changeIdUnit M ≫ (reductionChange Y (𝟙 R)).map f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (changeIdUnit N).val.app V (f.val.app V x) =
    ((reductionChange Y (𝟙 R)).map f).val.app V ((changeIdUnit M).val.app V x)
  rw [changeIdUnit_apply, changeIdUnit_apply, reductionTensor_map]

/-- The multiplication chain map `a ⊗ x ↦ a • x` out of scalar extension along the
identity. -/
private def changeIdComplexCounit (P : CochainComplex (reductionModules Y R) ℤ) :
    (reductionChangeComplex Y (𝟙 R)).obj P ⟶ P where
  f i := changeIdCounit (P.X i)
  comm' i j _ := (changeIdCounit_naturality (P.d i j)).symm

/-- The chain map `x ↦ 1 ⊗ x` into scalar extension along the identity. -/
private def changeIdComplexUnit :
    𝟭 (CochainComplex (reductionModules Y R) ℤ) ⟶ reductionChangeComplex Y (𝟙 R) where
  app P :=
    { f i := changeIdUnit (P.X i)
      comm' i j _ := (changeIdUnit_naturality (P.d i j)).symm }
  naturality P P' f := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    exact changeIdUnit_naturality (f.f i)

private theorem changeIdComplex_unit_counit (P : CochainComplex (reductionModules Y R) ℤ) :
    changeIdComplexUnit.app P ≫ changeIdComplexCounit P = 𝟙 P := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  exact changeIdCounit_unit (P.X i)

private theorem changeIdComplex_counit_unit (P : CochainComplex (reductionModules Y R) ℤ) :
    changeIdComplexCounit P ≫ changeIdComplexUnit.app P = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  exact changeIdUnit_counit (P.X i)

private theorem reductionDerivedChange_id_existsUnique_aux :
    ∃! e : reductionDerivedChange Y (𝟙 R) ≅ 𝟭 (reductionDerivedCategory Y R),
      ∀ P : CochainComplex (reductionModules Y R) ℤ,
        ∃ μ : (reductionChangeComplex Y (𝟙 R)).obj P ⟶ P,
          (∀ (i : ℤ) (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) (x : (P.X i).val.obj V),
            (μ.f i).val.app V (reductionTensorSection Y (𝟙 R) (P.X i) V a x) = a • x) ∧
          e.hom.app (DerivedCategory.Q.obj P) =
            reductionScalarComplexCounit Y (𝟙 R) P ≫ DerivedCategory.Q.map μ := by
  let L := reductionDerivedChange Y (𝟙 R)
  let eφ := complexCounitNat (reductionChange Y (𝟙 R)) L (reductionDerivedCounit Y (𝟙 R))
  have := complexCounitNat_kan (reductionChange Y (𝟙 R)) L (reductionDerivedCounit Y (𝟙 R))
  let β : DerivedCategory.Q ⋙ 𝟭 (reductionDerivedCategory Y R) ⟶
      reductionChangeComplex Y (𝟙 R) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight changeIdComplexUnit DerivedCategory.Q
  let τ := L.leftDerivedLift eφ (HomologicalComplex.quasiIso (reductionModules Y R) (.up ℤ))
    (𝟭 _) β
  have hτ (P : CochainComplex (reductionModules Y R) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit Y (𝟙 R) P =
        DerivedCategory.Q.map (changeIdComplexUnit.app P) := by
    have hf := L.leftDerived_fac_app eφ
      (HomologicalComplex.quasiIso (reductionModules Y R) (.up ℤ)) (𝟭 _) β P
    rw [complexCounitNat_app] at hf
    exact hf
  have hres (X : CochainComplex (reductionModules Y R) ℤ) :
      ∃ (P : CochainComplex (reductionModules Y R) ℤ) (p : P ⟶ X),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧ QuasiIso p := by
    obtain ⟨P, p, hk, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨P, p, hk, hp⟩
  have hiso : IsIso τ := by
    apply derived_natTrans_isIso (𝟭 _) L _ hres τ
    intro P hP
    have := scalarCounit_isIso Y (𝟙 R) P hP
    have : IsIso (changeIdComplexUnit.app P) :=
      ⟨changeIdComplexCounit P, changeIdComplex_unit_counit P,
        changeIdComplex_counit_unit P⟩
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫
        reductionScalarComplexCounit Y (𝟙 R) P) := by
      rw [hτ P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (reductionScalarComplexCounit Y (𝟙 R) P)
  have hform (P : CochainComplex (reductionModules Y R) ℤ) :
      (asIso τ).symm.hom.app (DerivedCategory.Q.obj P) =
        reductionScalarComplexCounit Y (𝟙 R) P ≫
          DerivedCategory.Q.map (changeIdComplexCounit P) := by
    rw [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [reassoc_of% (hτ P), ← CategoryTheory.Functor.map_comp, changeIdComplex_unit_counit,
      CategoryTheory.Functor.map_id]
    rfl
  have hgen (P : CochainComplex (reductionModules Y R) ℤ)
      (μ : (reductionChangeComplex Y (𝟙 R)).obj P ⟶ P)
      (hμ : ∀ (i : ℤ) (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) (x : (P.X i).val.obj V),
        (μ.f i).val.app V (reductionTensorSection Y (𝟙 R) (P.X i) V a x) = a • x) :
      μ = changeIdComplexCounit P := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    apply (SheafOfModules.toSheaf (reductionModuleRing Y R)).map_injective
    apply reductionTensor_hom_ext Y (𝟙 R) (P.X i)
    intro V s x
    change (μ.f i).val.app V (reductionTensorSection Y (𝟙 R) (P.X i) V s x) =
      (changeIdCounit (P.X i)).val.app V (reductionTensorSection Y (𝟙 R) (P.X i) V s x)
    rw [hμ, changeIdCounit_apply]
  refine ⟨(asIso τ).symm, fun P ↦ ⟨changeIdComplexCounit P,
    fun i V a x ↦ changeIdCounit_apply (P.X i) V a x, hform P⟩, ?_⟩
  intro e he
  apply Iso.ext
  apply derived_natTrans_ext L (𝟭 _) (fun _ ↦ True)
    (fun X ↦ ⟨X, 𝟙 X, trivial, inferInstance⟩)
  intro P _
  obtain ⟨μ, hμ, heμ⟩ := he P
  rw [heμ, hform, hgen P μ hμ]

end Identity

/-- Derived scalar extension along a ring endomorphism equal to the identity is the
identity, by a unique isomorphism given on every complex by multiplication `a ⊗ x ↦ a • x`.
Source: Stacks Tag 06YY (blueprint: lem-sf-field-stage-ordinary-realization).
Proof: the unit `x ↦ 1 ⊗ x` and multiplication are inverse chain maps. The universal
property of the left derived functor lifts the unit to a transformation `𝟭 ⟶ L`, which
is invertible on K-flat complexes and hence everywhere. Its inverse is multiplication
through the counit; multiplication is determined by its values on local tensor
generators, which gives uniqueness. -/
theorem reductionDerivedChange_id_existsUnique
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ R) (hφ : φ = 𝟙 R) :
    ∃! e : reductionDerivedChange Y φ ≅ 𝟭 (reductionDerivedCategory Y R),
      ∀ P : CochainComplex (reductionModules Y R) ℤ,
        ∃ μ : (reductionChangeComplex Y φ).obj P ⟶ P,
          (∀ (i : ℤ) (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) (x : (P.X i).val.obj V),
            (μ.f i).val.app V (reductionTensorSection Y φ (P.X i) V a x) = a • x) ∧
          e.hom.app (DerivedCategory.Q.obj P) =
            reductionScalarComplexCounit Y φ P ≫ DerivedCategory.Q.map μ := by
  subst hφ
  exact reductionDerivedChange_id_existsUnique_aux

end AlgebraicGeometry.Scheme
