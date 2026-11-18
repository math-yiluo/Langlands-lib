import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm

/-! # Existence of the constant terms of the actual orbit coefficients

Proof of `RationalOrbitConstantTermExistenceStatement`: every orbit coefficient
`f_ω = E^G_P ψ_ω` is a coefficient of the normalized induced representation `I_P^G A` of a
representative `A` of `ω`, which is admissible; Proposition I.6.2
(`standardConstantTerm_spec`) then gives its constant term along `P'`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

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
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

/-- Every coefficient `E^G_P Φ` of an admissible representation `R` of `M_I(F)` lies in
Waldspurger's coefficient space `A(I_P^G R)` of the normalized induced representation. -/
theorem rationalInducedCoefficientMap_mem_coefficientFunctionSpace
    (R : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hR : R.IsAdmissible)
    (Φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) R) :
    (⇑(rationalInducedCoefficientMap hG hi hν I hKc hPK R hR Φ) : rationalPoints G → ℂ) ∈
      coefficientFunctionSpace ((normalizedInductionFunctor
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))).obj R) := by
  have hmem : rationalInducedCoefficientMap hG hi hν I hKc hPK R hR Φ ∈
      LinearMap.range (normalizedCoefficientMap (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) R) := by
    rw [← range_rationalInducedCoefficientMap hG hi hν I hKc hPK R hR]
    exact LinearMap.mem_range_self _ Φ
  obtain ⟨t, ht⟩ := hmem
  rw [coefficientFunctionSpace_eq_map]
  exact ⟨_, ⟨t, rfl⟩, by rw [← ht]; rfl⟩

/-- **Existence of the constant terms of the orbit coefficients** (Proposition I.6.2 for the
induced representations): every `f_ω = E^G_P ψ_ω` has a constant term along `P'`. -/
theorem rationalOrbitConstantTermExistence :
    RationalOrbitConstantTermExistenceStatement hG hi hν I hKc hPK π C hC mu hsq I' hA := by
  intro ζ hζ K0 B hB hmem ψ ω
  obtain ⟨R, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    (RationalPointFamily.leviRationalNormCharacters i ν I) π C hC mu hsq ω
  rw [rationalInducedOrbitCoefficientMap_representative hG hi hν I hKc hPK π C hC mu hsq ψ R]
  have := compactSpace_leftQuotient_standardParabolicPoints_rootSet hG hi hν I hKc hPK
  have hX := normalizedInductionFunctor_obj_isAdmissible
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    R.val.obj R.val.property.2
  exact (standardConstantTerm_spec hG hi hν hζ hB hA hmem _ hX
    (rationalInducedCoefficientMap_mem_coefficientFunctionSpace hG hi hν I hKc hPK R.val.obj
      R.val.property.2 (ψ.val R))).1

end Langlands.HarishChandraSchwartz
