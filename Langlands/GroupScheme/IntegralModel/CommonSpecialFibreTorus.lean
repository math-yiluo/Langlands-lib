import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # Common maximal residue tori from bounded generic torus points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [ValuationRing R] [HenselianLocalRing R]
  [IsAlgClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M N : IntegralModel R K G}
  [Smooth M.group.X.hom] [Smooth N.group.X.hom]
  {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]

/-- A source bound on the units of a prescribed maximal split torus constructs
closed copies of one integral split torus in both smooth models, with the
literal model-map square and maximality of both residue inclusions. -/
theorem Hom.exists_common_splitTorus_of_bounded
    (ψ : M.Hom N (𝟙 G)) (hG : IsConnectedReductive G)
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    {iT : T.toGrp ⟶ G} (hiT : IsMaximalSplitTorus iT)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      M.integralPoints) :
    ∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of R)))
      (e : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮).toGrp ≅ T.toGrp)
      (jM : 𝒮.toGrp ⟶ M.group) (jN : 𝒮.toGrp ⟶ N.group),
      IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup jM ∧ IsClosedSubgroup jN ∧
        M.genericTorusMap 𝒮 jM = e.hom ≫ iT ∧
        jM ≫ ψ.hom = jN ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj 𝒮)
          ((GroupScheme.baseChange (residueBaseMap R)).map jM) ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj 𝒮)
          ((GroupScheme.baseChange (residueBaseMap R)).map jN) := by
  classical
  have hbN : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      N.integralPoints := by
    intro g hg
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      ψ.map_mem_integralPoints (hb hg)
  obtain ⟨I, hI, ⟨e⟩⟩ := hiT.1.1
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨jM, hjM, hgenM⟩ :=
    SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded
      M v hv e iT hiT.1.2 hb
  obtain ⟨jN, hjN, hgenN⟩ :=
    SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded
      N v hv e iT hiT.1.2 hbN
  let 𝒮 := SplitTorusClosure.torus R I
  let eK : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮).toGrp ≅
      T.toGrp := SplitTorusClosure.genericSplitIso R K I ≪≫ e.symm
  have h𝒮 : IsSplitTorus 𝒮.toGrp := SplitTorusClosure.isSplitTorus_torus I
  have : Flat 𝒮.toGrp.X.hom := SplitTorusClosure.flat_torus R I
  have hmaxM : IsMaximalSplitTorus (M.genericTorusMap 𝒮 jM) := by
    rw [hgenM, ← Category.assoc]
    exact hiT.iso_comp eK
  have hmaxN : IsMaximalSplitTorus (N.genericTorusMap 𝒮 jN) := by
    rw [hgenN, ← Category.assoc]
    exact hiT.iso_comp eK
  refine ⟨𝒮, eK, jM, jN, h𝒮, hjM, hjN, ?_, ?_, ?_, ?_⟩
  · simpa only [eK, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hgenM
  · exact ψ.comp_eq_of_genericTorusMap_eq (hgenM.trans hgenN.symm)
  · exact isMaximalTorus_specialFibre_of_generic hG M h𝒮 hjM hmaxM
  · exact isMaximalTorus_specialFibre_of_generic hG N h𝒮 hjN hmaxN

/-- The constructed torus gives a common maximal torus of the actual
special-fibre map. No kernel or quotient hypotheses are required. -/
theorem Hom.exists_common_maximalTorus_specialFibre_of_bounded
    (ψ : M.Hom N (𝟙 G)) (hG : IsConnectedReductive G)
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    {iT : T.toGrp ⟶ G} (hiT : IsMaximalSplitTorus iT)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      M.integralPoints) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (s : S.toGrp ⟶ M.specialFibre),
      IsMaximalTorus s ∧ IsMaximalTorus (s ≫ ψ.specialFibreMap) := by
  obtain ⟨𝒮, e, jM, jN, h𝒮, hjM, hjN, hgen, hcomp, hmaxM, hmaxN⟩ :=
    ψ.exists_common_splitTorus_of_bounded hG v hv hiT hb
  refine ⟨(CommGroupScheme.baseChange (residueBaseMap R)).obj 𝒮,
    (GroupScheme.baseChange (residueBaseMap R)).map jM, hmaxM, ?_⟩
  simpa only [Hom.specialFibreMap, ← Functor.map_comp, hcomp] using hmaxN

/-- A bounded maximal split generic torus supplies an actual common maximal
torus on special fibres of any identity-generic morphism of smooth models. -/
def BoundedTorusCommonSpecialFibreStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (_hG : IsConnectedReductive G)
    (M N : IntegralModel R K G)
    [Smooth M.group.X.hom] [Smooth N.group.X.hom]
    (ψ : M.Hom N (𝟙 G))
    (Γ₀ : Type u) [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (_hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (iT : T.toGrp ⟶ G),
    IsMaximalSplitTorus iT →
    (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤ M.integralPoints →
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (s : S.toGrp ⟶ M.specialFibre),
      IsMaximalTorus s ∧ IsMaximalTorus (s ≫ ψ.specialFibreMap)

/-- Construct the common torus using the two closed integral torus copies,
their generic rigidity square and maximality of each smooth residue fibre. -/
theorem boundedTorusCommonSpecialFibre : BoundedTorusCommonSpecialFibreStatement.{u} := by
  intro R K _ _ _ _ _ _ _ _ _ G hG M N _ _ ψ Γ₀ _ v hv T iT hiT hb
  exact ψ.exists_common_maximalTorus_specialFibre_of_bounded hG v hv hiT hb

end Langlands.GroupScheme.IntegralModel
