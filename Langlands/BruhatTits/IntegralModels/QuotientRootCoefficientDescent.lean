import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent

/-! # Descent of a single reductive-quotient root along a coefficient change -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section GenericFactor

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

variable {D' : RelativeComponentModelData R K G}
  {S₀ : CommGroupScheme (Spec (CommRingCat.of K))} {i₀ : S₀.toGrp ⟶ G}
  (𝒯 : IntegralTorusData D' S₀ i₀)
  {S' : CommGroupScheme (Spec (CommRingCat.of L))}
  {i' : S'.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
  (T' : IntegralTorusData (D'.baseChange A L) S' i')
  (f : (GroupScheme.baseChange (Spec.algebraMap K L)).obj S₀.toGrp ⟶ S'.toGrp)

/-- The generic map from the base change of the torus of `𝒯` to the generic fibre
of a torus `T'` of the base-changed model, determined by a generic map `f`. -/
def baseChangeComparisonGenericMap :
    (GroupScheme.baseChange (Spec.algebraMap A L)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus.toGrp) ⟶
      (GroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus.toGrp :=
  (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
      𝒯.torus.toGrp).hom ≫
    (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.hom ≫ f ≫
      T'.genericIso.inv

/-- If `f` factors the base change of the generic inclusion of `𝒯` through the
generic inclusion of `T'`, the comparison generic map factors the base-changed
inclusion of `𝒯` through the inclusion of `T'`. -/
theorem baseChangeComparisonGenericMap_comp_inclusion
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀) :
    baseChangeComparisonGenericMap A L 𝒯 T' f ≫
        (GroupScheme.baseChange (Spec.algebraMap A L)).map T'.inclusion =
      (GroupScheme.baseChange (Spec.algebraMap A L)).map (𝒯.baseChangeInclusion A L) := by
  apply (cancel_mono (D'.neutral.baseChangeGenericIso A L).hom).mp
  have h1 : (GroupScheme.baseChange (Spec.algebraMap A L)).map T'.inclusion ≫
      (D'.neutral.baseChangeGenericIso A L).hom = T'.genericIso.hom ≫ i' :=
    T'.generic_comm
  rw [Category.assoc, h1]
  simp only [baseChangeComparisonGenericMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hf, IntegralModel.baseChangeGenericIso_eq_square]
  simp only [IntegralModel.baseChangeSquareIso, Iso.trans_hom, Functor.mapIso_hom]
  have hn : (GroupScheme.baseChange (Spec.algebraMap A L)).map (𝒯.baseChangeInclusion A L) ≫
      (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
        D'.neutral.group).hom =
      (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
        𝒯.torus.toGrp).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map
          ((GroupScheme.baseChange (Spec.algebraMap R K)).map 𝒯.inclusion) :=
    Descent.squareComparison_naturality _ _ _ _ _ 𝒯.inclusion
  have h2 : (GroupScheme.baseChange (Spec.algebraMap K L)).map
        ((GroupScheme.baseChange (Spec.algebraMap R K)).map 𝒯.inclusion) ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map D'.neutral.genericIso.hom =
      (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.hom ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀ := by
    rw [← Functor.map_comp, 𝒯.generic_comm, Functor.map_comp]
  rw [← Category.assoc ((GroupScheme.baseChange (Spec.algebraMap A L)).map
    (𝒯.baseChangeInclusion A L)), hn]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) h2.symm

/-- Characters through the comparison generic map: if the base change of an
integral character `m` of `𝒯` is `ρ ≫ ψ`, then the base change of the generic
character of `m` is `f` followed by the generic character of `ψ`. -/
theorem baseChange_genericCharacter_eq_of_baseChangeComparisonGenericMap
    (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus ⟶ T'.torus)
    (hρ : (GroupScheme.baseChange (Spec.algebraMap A L)).map (CommGroupScheme.groupHom ρ) =
      baseChangeComparisonGenericMap A L 𝒯 T' f)
    (m : characterLattice 𝒯.torus) (ψ : characterLattice T'.torus)
    (hm : characterLattice.baseChange (Spec.algebraMap R A) 𝒯.torus m = ρ ≫ ψ) :
    characterLattice.baseChange (Spec.algebraMap K L) S₀ (𝒯.genericCharacter m) =
      Additive.ofMul f ≫ T'.genericCharacter ψ := by
  have t1 := Descent.characterBaseChange_tower (Spec.algebraMap R A) (Spec.algebraMap A L)
    (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L) 𝒯.torus m
  have t2 := Descent.characterBaseChange_tower (Spec.algebraMap R K) (Spec.algebraMap K L)
    (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus m
  rw [hm, characterLattice.baseChange_precomp] at t1
  have hr : characterLattice.baseChange (Spec.algebraMap K L ≫ Spec.algebraMap R K)
        𝒯.torus m =
      (Descent.commPullbackComparison _ _ _ (coefficientSquare_spec A L) 𝒯.torus).inv ≫
        (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
    rw [t1, Iso.inv_hom_id_assoc]
  have hgen : 𝒯.genericCharacter m =
      (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
        Additive.ofMul 𝒯.genericIso.inv) ≫
        characterLattice.baseChange (Spec.algebraMap R K) 𝒯.torus m := rfl
  have key : (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.inv ≫
      (Descent.pullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
        (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus.toGrp).hom ≫
      (Descent.pullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
        𝒯.torus.toGrp).inv ≫
      baseChangeComparisonGenericMap A L 𝒯 T' f = f ≫ T'.genericIso.inv := by
    simp only [baseChangeComparisonGenericMap, Descent.squareComparison, Iso.trans_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hρ' : (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ =
      Additive.ofMul (baseChangeComparisonGenericMap A L 𝒯 T' f) :=
    congrArg Additive.ofMul hρ
  calc characterLattice.baseChange (Spec.algebraMap K L) S₀ (𝒯.genericCharacter m)
      = (CommGroupScheme.baseChange (Spec.algebraMap K L)).map
          (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
            Additive.ofMul 𝒯.genericIso.inv) ≫
          (Descent.commPullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus).hom ≫
          (Descent.commPullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
            𝒯.torus).inv ≫
          (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        rw [hgen, characterLattice.baseChange_precomp, t2, hr]
    _ = ((CommGroupScheme.baseChange (Spec.algebraMap K L)).map
          (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
            Additive.ofMul 𝒯.genericIso.inv) ≫
          (Descent.commPullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus).hom ≫
          (Descent.commPullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
            𝒯.torus).inv ≫
          (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ) ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        simp only [Category.assoc]
    _ = (show (CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S₀ ⟶
            (CommGroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus from
          Additive.ofMul (f ≫ T'.genericIso.inv)) ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        congr 1
        rw [hρ']
        exact congrArg Additive.ofMul key
    _ = Additive.ofMul f ≫ T'.genericCharacter ψ :=
        Category.assoc
          (show (CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S₀ ⟶ S' from
            Additive.ofMul f)
          (show S' ⟶ (CommGroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus from
            Additive.ofMul T'.genericIso.inv)
          (characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ)

/-- Over a Henselian discrete valuation ring with separably closed residue field,
the base change of a split integral torus maps into a closed split integral torus
of the base-changed neutral model, compatibly with both inclusions and with
generic fibre the comparison generic map. -/
theorem exists_torusHom_of_baseChange
    [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (hT : IsSplitTorus 𝒯.torus.toGrp)
    {i'' : S'.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
    (A' : IntegralSplitTorusData (D'.baseChange A L).neutral i'')
    (hA' : IsClosedSubgroup A'.inclusion)
    (hf : f ≫ i'' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀) :
    ∃ (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus ⟶ A'.torus),
      CommGroupScheme.groupHom ρ ≫ A'.inclusion = 𝒯.baseChangeInclusion A L ∧
        (GroupScheme.baseChange (Spec.algebraMap A L)).map (CommGroupScheme.groupHom ρ) =
          baseChangeComparisonGenericMap A L 𝒯 A'.toIntegralTorusData f :=
  exists_torusHom_of_generic_factor (D'.baseChange A L).neutral
    ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus) A'.torus
    (𝒯.isSplitTorus_baseChange A L hT) A'.isSplit (𝒯.baseChangeInclusion A L) A'.inclusion hA'
    _ (baseChangeComparisonGenericMap_comp_inclusion A L 𝒯 A'.toIntegralTorusData f hf)

end GenericFactor

section Residue

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

local notation "resExt" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

/-- The base-changed torus in the base-changed quotient is the residue-field base
change of the original torus in the original quotient. -/
theorem IntegralTorusData.groupHom_specialFibreCommSquareIso_comp_baseChange_quotient
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (Q : SpecialFibreQuotientData D) :
    CommGroupScheme.groupHom (specialFibreCommSquareIso A T.torus).hom ≫
        ((T.baseChange A L).specialFibreInclusion ≫ (Q.baseChange A L).projection) =
      (GroupScheme.baseChange resExt).map (T.specialFibreInclusion ≫ Q.projection) := by
  change (specialFibreSquareIso A T.torus.toGrp).hom ≫
      ((GroupScheme.baseChange (IntegralModel.residueBaseMap A)).map
          ((GroupScheme.baseChange (Spec.algebraMap R A)).map T.inclusion) ≫
        (specialFibreSquareIso A D.neutral.group).inv ≫
          (GroupScheme.baseChange resExt).map Q.projection) =
    (GroupScheme.baseChange resExt).map
      ((GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map T.inclusion ≫
        Q.projection)
  rw [← specialFibreSquareIso_naturality_assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

set_option maxHeartbeats 2000000 in
/-- **Descent of one quotient root along a coefficient change.** Let `T'` be a
split integral torus of the base-changed model and `ρ` a map from the base change
of the split integral torus `T` into `T'`, compatible with both inclusions. Let
`m` be a nonzero integral character of `T` whose base change is `ρ ≫ ψ`. If the
special character of `ψ` is a root of `T'` in the base-changed quotient, then
the special character of `m` is a root of `T` in the original quotient. -/
theorem IntegralTorusData.specialCharacter_mem_roots_of_baseChange
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) [LocallyOfFiniteType Q.quotient.X.hom]
    {S' : CommGroupScheme (Spec (CommRingCat.of L))}
    {i' : S'.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
    (T' : IntegralTorusData (D.baseChange A L) S' i') (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus ⟶ T'.torus)
    (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.baseChangeInclusion A L)
    (m : characterLattice T.torus) (ψ : characterLattice T'.torus)
    (hm : characterLattice.baseChange (Spec.algebraMap R A) T.torus m = ρ ≫ ψ)
    (hm0 : m ≠ 0)
    (hψ : T'.specialCharacterEquiv hT' ψ ∈
      roots (T'.specialFibreInclusion ≫ (Q.baseChange A L).projection)) :
    T.specialCharacterEquiv hT m ∈ roots (T.specialFibreInclusion ≫ Q.projection) := by
  have hTs : IsSplitTorus T.specialFibre.toGrp := hT.baseChange _
  have hT's : IsSplitTorus T'.specialFibre.toGrp := hT'.baseChange _
  have hTb : IsSplitTorus (T.baseChange A L).torus.toGrp := T.isSplitTorus_baseChange A L hT
  have hTbs : IsSplitTorus (T.baseChange A L).specialFibre.toGrp := hTb.baseChange _
  let ρs := (CommGroupScheme.baseChange (IntegralModel.residueBaseMap A)).map ρ
  have hincl : (T.baseChange A L).specialFibreInclusion =
      CommGroupScheme.groupHom ρs ≫ T'.specialFibreInclusion := by
    change (GroupScheme.baseChange (IntegralModel.residueBaseMap A)).map
        (T.baseChangeInclusion A L) = _
    rw [← hρ, Functor.map_comp]
    rfl
  have hchar : (T.baseChange A L).specialCharacterEquiv hTb
      (characterLattice.baseChange (Spec.algebraMap R A) T.torus m) =
        ρs ≫ T'.specialCharacterEquiv hT' ψ := by
    rw [IntegralTorusData.specialCharacterEquiv_apply,
      IntegralTorusData.specialCharacterEquiv_apply, hm, characterLattice.baseChange_precomp]
  have hne : (T.baseChange A L).specialCharacterEquiv hTb
      (characterLattice.baseChange (Spec.algebraMap R A) T.torus m) ≠ 0 := by
    intro h0
    apply hm0
    have h1 : characterLattice.baseChange (Spec.algebraMap R A) T.torus m = 0 :=
      ((T.baseChange A L).specialCharacterEquiv hTb).map_eq_zero_iff.mp h0
    exact (characterLattice.baseChangeEquiv (Spec.algebraMap R A) T.torus hT).map_eq_zero_iff.mp h1
  have h1 : (T.baseChange A L).specialCharacterEquiv hTb
      (characterLattice.baseChange (Spec.algebraMap R A) T.torus m) ∈
        roots ((T.baseChange A L).specialFibreInclusion ≫ (Q.baseChange A L).projection) := by
    rw [hincl, Category.assoc, mem_roots_comp_iff hT's hTbs ρs]
    exact ⟨hne, _, hψ, hchar.symm⟩
  rw [T.baseChange_specialCharacterEquiv_apply A L hT m] at h1
  have hcomm : (GroupScheme.baseChange resExt).map (T.specialFibreInclusion ≫ Q.projection) ≫
      (Iso.refl ((GroupScheme.baseChange resExt).obj Q.quotient)).hom =
      CommGroupScheme.groupHom (specialFibreCommSquareIso A T.torus).hom ≫
        ((T.baseChange A L).specialFibreInclusion ≫ (Q.baseChange A L).projection) := by
    rw [Iso.refl_hom, Category.comp_id,
      T.groupHom_specialFibreCommSquareIso_comp_baseChange_quotient A L Q]
  have h3 := roots_mem_of_transport_iff (specialFibreCommSquareIso A T.torus)
    (Iso.refl _) hcomm (characterLattice.baseChange resExt _ (T.specialCharacterEquiv hT m))
  have h2 := mem_roots_baseChange_iff (K := IsLocalRing.ResidueField A) Q.quotient
    T.specialFibre hTs (T.specialFibreInclusion ≫ Q.projection) (T.specialCharacterEquiv hT m)
  exact h2.mp (h3.mp h1)

end Residue

end Langlands.BruhatTits.IntegralModels
