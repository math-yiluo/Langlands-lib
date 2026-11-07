import Langlands.GroupScheme.Rational.StandardParabolicEndpointsNegation
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.Representation.Jacquet.FixedVectorsGenerationProof

/-! # Standard-parabolic factorization and Jacquet fixed-vector generation -/

set_option autoImplicit false

noncomputable section

universe uF uR uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Standard Levi points normalize standard unipotent points directly from
the defining intersections, without a root-system or cocharacter-existence input. -/
theorem standardLeviPoints_le_normalizer_standardUnipotentPoints
    (J : Set (characterLattice S)) :
    standardLeviPoints i ν J ≤ Subgroup.normalizer (standardUnipotentPoints i ν J) := by
  intro m hm
  apply Subgroup.mem_normalizer_iff.mpr
  intro n
  constructor
  · exact StandardLeviIntersection.conj_mem_standardUnipotent i ν
      (standardLevi_le_standardParabolic i ν J _ hm)
  · intro hn
    have h := StandardLeviIntersection.conj_mem_standardUnipotent i ν
      (standardLevi_le_standardParabolic i ν J _
        ((standardLeviPoints i ν J).inv_mem hm)) hn
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- The minimal standard parabolic lies in every standard parabolic.
The root-negation and root-sign comparisons are imported as unconditional proofs. -/
theorem standardParabolic_empty_le_standard
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice S)) :
    standardParabolic i ν ∅ ≤ standardParabolic i ν J := by
  intro Q g hg
  apply (mem_standardParabolic i ν).mpr
  intro zeta hzeta
  have hle := (relativeRootSignInclusions F G hG S i hi ν zeta).1.mpr
    (fun α hα hnonneg =>
      ((isStandardCocharacter_empty_self i ν).root_pairing_implications_of_subset
        i ν hν (relativeRootNegation F G hG S i hi) hzeta
        (Set.empty_subset J) hα).1 hnonneg)
  exact hle Q (standardParabolic_empty_le i ν Q hg)

/-- A minimal-standard `M N K₀` factorization gives the same factorization for
any standard index admitting a standard cocharacter. No topology is required. -/
theorem standard_factorization_of_minimal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (K₀ : Subgroup (rationalPoints G))
    (hfactor : ∀ g : rationalPoints G,
      ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅,
      ∃ k ∈ K₀, g = m * n * k) :
    ∀ g : rationalPoints G,
      ∃ m ∈ standardLeviPoints i ν J,
      ∃ n ∈ standardUnipotentPoints i ν J,
      ∃ k ∈ K₀, g = m * n * k := by
  obtain ⟨zeta, hzeta⟩ := hstandard
  obtain ⟨_, hLevi, hUni⟩ :=
    standard_eq_dynamic_of_relativeRootNegation relativeRootNegation
      F G hG S i hi ν hν J zeta hzeta
  intro g
  obtain ⟨m, hm, n, hn, k, hk, hg⟩ := hfactor g
  have hmn : m * n ∈ standardParabolicPoints i ν J :=
    standardParabolic_empty_le_standard i ν hG hi hν J _
      ((standardParabolicPoints i ν ∅).mul_mem
        (standardLevi_le_standardParabolic i ν ∅ _ hm)
        (standardUnipotent_le_standardParabolic i ν ∅ _ hn))
  obtain ⟨v, hv, l, hl, hvl⟩ :=
    StandardLeviIntersection.exists_standardUnipotent_mul_standardLevi i ν
      ⟨hzeta, hLevi.ge, hUni.ge⟩ hmn
  have hn' : l⁻¹ * v * l ∈ standardUnipotentPoints i ν J := by
    simpa only [inv_inv] using
      (StandardLeviIntersection.conj_mem_standardUnipotent i ν
        (standardLevi_le_standardParabolic i ν J _
          ((standardLeviPoints i ν J).inv_mem hl)) hv)
  refine ⟨l, hl, l⁻¹ * v * l, hn', k, hk, ?_⟩
  calc
    g = (v * l) * k := by rw [hvl]; exact hg
    _ = l * (l⁻¹ * v * l) * k := by group

end Langlands.GroupScheme

namespace Langlands.Jacquet

open Langlands.GroupScheme

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The actual unnormalized standard Jacquet action, using the normalization
deduced from the defining standard subgroup intersections. -/
def standardJacquetAction
    {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R (rationalPoints G) V) (J : Set (characterLattice S)) :
    Representation R (standardLeviPoints i ν J)
      (Coinvariants ρ (standardUnipotentPoints i ν J)) :=
  action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)

/-- Fixed-vector generation passes to the actual standard Jacquet action from
the minimal-standard factorization. Coefficients and carriers have independent
universes, and no admissibility or finite-generation hypothesis is used. -/
theorem fixedVectors_generate_standardJacquet_of_minimal_factorization
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (K K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer K)
    (hfactor : ∀ g : rationalPoints G,
      ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅,
      ∃ k ∈ K₀, g = m * n * k)
    {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R (rationalPoints G) V)
    (hgen : ∀ T : Subrepresentation ρ, fixedVectors ρ K ≤ T.toSubmodule → T = ⊤)
    (T : Subrepresentation (standardJacquetAction i ν ρ J))
    (hT : fixedVectors (standardJacquetAction i ν ρ J)
      (K.comap (standardLeviPoints i ν J).subtype) ≤ T.toSubmodule) :
    T = ⊤ :=
  fixedVectors_generate_of_factorization ρ
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) K K₀
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J) hnormal
    (standard_factorization_of_minimal i ν hG hi hν J hstandard K₀ hfactor) hgen T hT

end Langlands.Jacquet
