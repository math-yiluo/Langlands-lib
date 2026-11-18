import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviOriginalOrbitXiBound
import Langlands.Representation.Jacquet.StandardInducedRayThreshold

/-! # All-coefficient Xi bounds for the original unitary induced fibers -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
  (hbasis : SimultaneousStandardBasisAt i ν K0)
  (hcover : StandardLeviCartanCovering F i ν (RationalPointFamily.rootSet i ν I) K0)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

/-- All smooth coefficients of each original unitary unramified induced
fiber are bounded by the original ambient Xi. -/
abbrev HasStandardUnitaryInducedCoefficientXiBound : Prop :=
  ∀ ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I),
    (∀ m, ‖(ψ.val m : ℂ)‖ = 1) →
      HasXiBoundedCoefficients (rationalXi hKc hPK)
        (standardUnramifiedInducedObject hG hi hν I π.obj ψ).representation

include hK0c hbasis hcover hsq in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- Every original normalized induced unitary fiber has all its smooth
matrix coefficients bounded by the original ambient Xi. The original
structural data and square integrability supply the source bound and
projected source compact; no coherent-section extension is required. -/
theorem hasXiBoundedCoefficients_standardUnitaryInduced :
    HasStandardUnitaryInducedCoefficientXiBound hG hi hν I hKc hPK π := by
  intro ψ hψ
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let KM := rationalProjectedLeviCompact hG hi hν I (K := K)
  let : CompactSpace KM := isCompact_iff_compactSpace.mp
    (isCompact_rationalProjectedLeviCompact hG hi hν I hKc)
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  let h := isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)
  let hU := isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)
  let hP := isClosed_standardParabolicPoints_rootSet hG hi hν I
  let hm := continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) h
  let hPKP := exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK
  let hGu := fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g
  let hδP := modularCharacter_standardParabolicPoints hG hi hν I rfl
    (RationalPointFamily.rootSet_subset i ν I)
  let Bψ := π.obj.twist ψ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ ψ)
  have hBψ : Bψ.IsAdmissible := (SmoothRep.isAdmissible_twist_iff _ _ π.obj).mpr π.property.2
  let E := CompactInduction.coefficientTensorEquiv h hU Bψ K hKc hP hm hPKP hGu hδP hBψ
  intro v ℓ
  let t : NormalizedCoefficientTensor h hU Bψ := v ⊗ₜ[ℂ] ℓ
  let Ft := E.symm t
  let Ec := productInducedCompactEquiv (RationalPointFamily.leviRationalNormCharacters i ν I)
    h K hP hKc (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    hm hU (factorization_subtype hPKP) ψ π.obj
  let F₀ := Ec Ft
  obtain ⟨c, hc, hb⟩ := norm_twist_coefficientMap_le_xi_arbitraryCompact
    h hU π.obj K hKc (RationalPointFamily.leviRationalNormCharacters i ν I)
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I) hP hm hPKP hGu hδP
    π.property.2 (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc)
    hPK KM (isIwasawaPair_rationalProjectedLeviCompact hG hi hν I hPK)
    (isOpen_rationalProjectedLeviCompact hG hi hν I)
    (standardLeviMinimalModulusOf_eq_one_sourceCompact hG hi hν
      (RationalPointFamily.rootSet_subset i ν I)
      (isOpen_rationalProjectedLeviCompact hG hi hν I)
      (isCompact_rationalProjectedLeviCompact hG hi hν I hKc))
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    (hasXiBoundedCoefficients_standardLeviProjectedCompact hG hi hν I hKc hPK
      hK0c hbasis hcover π C hC mu hsq) F₀
  have hsec : twistedSection h hU π.obj K
      (RationalPointFamily.leviRationalNormCharacters i ν I) hP hKc
      (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
      hm (factorization_subtype hPKP) ψ F₀ = Ft := Ec.symm_apply_apply Ft
  refine ⟨c, hc, fun g => ?_⟩
  have hg := hb ψ hψ g
  rw [hsec] at hg
  change ‖normalizedCoefficientMap h hU Bψ (E (E.symm t)) g‖ ≤
    c * rationalXi hKc hPK g at hg
  rw [E.apply_symm_apply] at hg
  exact hg

end Langlands.HarishChandraSchwartz
