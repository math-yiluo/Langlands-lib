import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedTemperedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviProjectionHeight
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.Representation.Plancherel.RationalMatrixNormComparison

/-! # Tempered representations and normalized induction on actual rational points

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus and a
generic cocharacter, this module defines tempered representations of `G(F)` and of the actual
standard Levi subgroups `M_J(F)` (Waldspurger III.2), proves that the notion does not depend on the
closed matrix representation defining `σ`, and proves Waldspurger's Lemma III.2.3 for the actual
normalized parabolic induction `I_{P_J}^G`: the induction of a tempered admissible representation
of `M_J(F)` is tempered. The inputs of the Library's abstract Lemma III.2.3 are verified on actual
points: the height bound for Levi components, the unimodularity of `U_J(F)` and of `G(F)`, the
modulus of `P_J(F)` and the `LeviData` of `RationalXiLevi`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalTemperedSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalTemperedT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalTemperedNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

section Height

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- **Heights of Levi components of `P_J(F)`**: for a closed matrix representation `ρ` there is
`c` with `σ(m_P(q)) ≤ c + σ(q)` for every `q ∈ P_J(F)`, where `m_P` is the Levi projection of
`P_J(F) = M_J(F) ⋉ U_J(F)`. By `standardCocharacter`, `P_J, M_J, U_J` are the dynamic subgroups
of a cocharacter, and the Library's `exists_rationalMatrixNorm_levi_le` applies. -/
theorem exists_rationalHeight_projection_le (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hρ : IsClosedSubgroup ρ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ q : standardParabolicPoints i ν J,
      rationalHeight (F := F) ρ
          ((isSemidirectDecomposition_standard hG hi hν hJ).projection q : rationalPoints G) ≤
        c + rationalHeight (F := F) ρ q := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  set χ := CommGroupScheme.groupHom ζ ≫ i
  obtain ⟨C, hC⟩ := MatrixRepresentation.exists_rationalMatrixNorm_levi_le F χ ρ hρ
  set h := isSemidirectDecomposition_standard hG hi hν hJ
  have hPmem : ∀ x : rationalPoints G, x ∈ standardParabolicPoints i ν J →
      x ∈ (Dynamic.parabolic χ).rationalPoints := by
    intro x hx
    change x ∈ (standardParabolic i ν J).carrier _ at hx
    rw [hP] at hx
    exact hx
  have hMmem : ∀ x : rationalPoints G, x ∈ standardLeviPoints i ν J →
      x ∈ (Dynamic.centralizer χ).rationalPoints := by
    intro x hx
    change x ∈ (standardLevi i ν J).carrier _ at hx
    rw [hM] at hx
    exact hx
  have hUmem : ∀ x : rationalPoints G, x ∈ standardUnipotentPoints i ν J →
      x ∈ (Dynamic.unipotent χ).rationalPoints := by
    intro x hx
    change x ∈ (standardUnipotent i ν J).carrier _ at hx
    rw [hU] at hx
    exact hx
  have key : ∀ q : standardParabolicPoints i ν J,
      MatrixRepresentation.rationalMatrixNorm F ρ (h.projection q : rationalPoints G) ≤
        C * MatrixRepresentation.rationalMatrixNorm F ρ q := fun q =>
    hC q (h.projection q) (hPmem _ q.2) (hMmem _ (h.projection q).2)
      (hUmem _ (h.projection_inv_mul_mem q))
  have hC1 : 1 ≤ C := by
    have h1 := key 1
    rw [map_one] at h1
    simpa using h1
  refine ⟨Real.log C, Real.log_nonneg hC1, fun q => ?_⟩
  unfold rationalHeight
  rw [← Real.log_mul (by linarith) (rationalMatrixNorm_pos ρ _).ne']
  exact Real.log_le_log (rationalMatrixNorm_pos ρ _) (key q)

/-- **Lemma II.3.1-type bound on Levi components** in the form of the Library's
`LeviSigmaBound`: for a compact subgroup `K`, there is `c` with
`σ(m_P(q)) ≤ c (1 + σ(q k))` for all `q ∈ P_J(F)` and `k ∈ K`. -/
theorem rationalLeviSigmaBound (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hρ : IsClosedSubgroup ρ)
    {K : Set (rationalPoints G)} (hKc : IsCompact K) :
    LeviSigmaBound (isSemidirectDecomposition_standard hG hi hν hJ) K
      (rationalHeight (F := F) ρ) (fun m => rationalHeight (F := F) ρ m) := by
  obtain ⟨c₀, hc₀, hc⟩ := exists_rationalHeight_projection_le ρ hG hi hν hJ hρ
  obtain ⟨B, hB⟩ := (hKc.image (continuous_rationalHeight (F := F) ρ)).bddAbove
  set B' := max B 0
  refine ⟨1 + c₀ + B', fun q k hk => ?_⟩
  have hk' : rationalHeight (F := F) ρ k⁻¹ ≤ B' := by
    rw [rationalHeight_inv]
    exact (hB ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hq : rationalHeight (F := F) ρ q ≤
      rationalHeight (F := F) ρ ((q : rationalPoints G) * k) + B' := by
    have e : (q : rationalPoints G) = (q : rationalPoints G) * k * k⁻¹ := by group
    calc rationalHeight (F := F) ρ q
        = rationalHeight (F := F) ρ ((q : rationalPoints G) * k * k⁻¹) := by rw [← e]
      _ ≤ rationalHeight (F := F) ρ ((q : rationalPoints G) * k) +
          rationalHeight (F := F) ρ k⁻¹ := rationalHeight_mul_le ρ _ _
      _ ≤ _ := by linarith
  have h0 := rationalHeight_nonneg (F := F) ρ ((q : rationalPoints G) * k)
  have hB0 : 0 ≤ B' := le_max_right _ _
  have := hc q
  nlinarith

end Height

section Tempered

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] in
/-- Tempered growth is preserved when the height `σ'` is replaced by a height `σ` with
`1 + σ' ≤ C (1 + σ)`. -/
theorem HasTemperedGrowth.of_one_add_le {X : Type*} {Ξ σ σ' : X → ℝ} {φ : X → ℂ}
    (hΞ : ∀ g, 0 ≤ Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hσ' : ∀ g, 0 ≤ σ' g) {C : ℝ}
    (hC : ∀ g, 1 + σ' g ≤ C * (1 + σ g)) (h : HasTemperedGrowth Ξ σ' φ) :
    HasTemperedGrowth Ξ σ φ := by
  obtain ⟨c, r, hb⟩ := h
  refine ⟨max c 0 * max C 1 ^ max r 0, max r 0, fun g => ?_⟩
  have h1 : 1 ≤ 1 + σ' g := le_add_of_nonneg_right (hσ' g)
  have h2 : 0 ≤ 1 + σ g := by linarith [hσ g]
  have hpos : 0 ≤ (1 + σ' g) ^ r := Real.rpow_nonneg (by linarith) _
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hle : 1 + σ' g ≤ max C 1 * (1 + σ g) :=
    (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  calc ‖φ g‖ ≤ c * Ξ g * (1 + σ' g) ^ r := hb g
    _ ≤ max c 0 * Ξ g * (1 + σ' g) ^ r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ g)) hpos
    _ ≤ max c 0 * Ξ g * (1 + σ' g) ^ max r 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _))
          (mul_nonneg hc0 (hΞ g))
    _ ≤ max c 0 * Ξ g * (max C 1 * (1 + σ g)) ^ max r 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hle (le_max_right _ _))
          (mul_nonneg hc0 (hΞ g))
    _ = max c 0 * max C 1 ^ max r 0 * Ξ g * (1 + σ g) ^ max r 0 := by
        rw [Real.mul_rpow (zero_le_one.trans (le_max_right _ _)) h2]
        ring

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- **Comparison of heights**: for a closed matrix representation `ρ` and any matrix
representation `τ` there is `C` with `1 + σ_τ ≤ C (1 + σ_ρ)` on `G(F)` (from the Library's
`rationalMatrixNormComparison`, `‖τ(g)‖ ≤ c ‖ρ(g)‖^d`). -/
theorem exists_one_add_rationalHeight_le {N M : ℕ} [Nonempty (Fin N)] [Nonempty (Fin M)]
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (τ : MatrixRepresentation G (Fin M)) :
    ∃ C : ℝ, ∀ g : rationalPoints G,
      1 + rationalHeight (F := F) τ g ≤ C * (1 + rationalHeight (F := F) ρ g) := by
  obtain ⟨d, c, hc, hb⟩ := Plancherel.rationalMatrixNormComparison F G (Fin N) (Fin M) ρ hρ τ
  refine ⟨1 + |Real.log c| + d, fun g => ?_⟩
  have hρpos := rationalMatrixNorm_pos ρ g
  have h1 : rationalHeight (F := F) τ g ≤ Real.log c + d * rationalHeight (F := F) ρ g := by
    unfold rationalHeight
    calc Real.log (MatrixRepresentation.rationalMatrixNorm F τ g)
        ≤ Real.log (c * MatrixRepresentation.rationalMatrixNorm F ρ g ^ d) :=
          Real.log_le_log (rationalMatrixNorm_pos τ g) (hb g)
      _ = Real.log c + d * Real.log (MatrixRepresentation.rationalMatrixNorm F ρ g) := by
          rw [Real.log_mul hc.ne' (pow_ne_zero _ hρpos.ne'), Real.log_pow]
  have h2 := rationalHeight_nonneg (F := F) ρ g
  have h3 := le_abs_self (Real.log c)
  have h4 : (0 : ℝ) ≤ |Real.log c| := abs_nonneg _
  have h5 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

variable {K : Subgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- **Tempered representations of `G(F)`** (Waldspurger III.2, printed p. 265): every coefficient
`g ↦ ℓ(π(g) v)` of the smooth representation `A` of `G(F)` (`v` a vector, `ℓ` a smooth functional)
satisfies `|ℓ(π(g) v)| ≤ c Ξ(g) (1 + σ(g))^r` for some `c, r`, where `Ξ = rationalXi hKc hPK` and
`σ = rationalHeight ρ`. For admissible `A` this is Waldspurger's `A(π) ⊂ A_w(G)`. -/
def IsRationalTempered (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) : Prop :=
  HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ) A.representation

/-- **Tempered representations of an actual standard Levi subgroup `M_J(F)`**: the coefficients of
`A` have tempered growth for `Ξ^{M_J} = rationalLeviXi hKc hM` and the restriction of
`σ = rationalHeight ρ` to `M_J(F)`. -/
def IsRationalLeviTempered
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) : Prop :=
  HasTemperedCoefficients (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m)
    A.representation

theorem rationalXi_nonneg (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (g : rationalPoints G) : 0 ≤ rationalXi hKc hPK g :=
  integral_nonneg fun _ => iwasawaWeight_nonneg _

theorem rationalLeviXi_nonneg
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))) (m : standardLeviPoints i ν J) :
    0 ≤ rationalLeviXi hKc hM m :=
  integral_nonneg fun _ => iwasawaWeight_nonneg _

/-- **Independence of the matrix representation**: for closed matrix representations `ρ` and
`ρ'`, temperedness for `σ_ρ` and for `σ_{ρ'}` agree. -/
theorem isRationalTempered_iff (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N' : ℕ} [Nonempty (Fin N')] (ρ' : MatrixRepresentation G (Fin N'))
    (hρ : IsClosedSubgroup ρ) (hρ' : IsClosedSubgroup ρ')
    (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) :
    IsRationalTempered hKc ρ hPK A ↔ IsRationalTempered hKc ρ' hPK A := by
  obtain ⟨C, hC⟩ := exists_one_add_rationalHeight_le ρ' hρ' ρ
  obtain ⟨C', hC'⟩ := exists_one_add_rationalHeight_le ρ hρ ρ'
  constructor
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le (rationalXi_nonneg hKc hPK) (rationalHeight_nonneg ρ')
      (rationalHeight_nonneg ρ) hC
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le (rationalXi_nonneg hKc hPK) (rationalHeight_nonneg ρ)
      (rationalHeight_nonneg ρ') hC'

/-- Independence of the matrix representation for tempered representations of `M_J(F)`. -/
theorem isRationalLeviTempered_iff
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    {N' : ℕ} [Nonempty (Fin N')] (ρ' : MatrixRepresentation G (Fin N'))
    (hρ : IsClosedSubgroup ρ) (hρ' : IsClosedSubgroup ρ')
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) :
    IsRationalLeviTempered hKc ρ hM A ↔ IsRationalLeviTempered hKc ρ' hM A := by
  obtain ⟨C, hC⟩ := exists_one_add_rationalHeight_le ρ' hρ' ρ
  obtain ⟨C', hC'⟩ := exists_one_add_rationalHeight_le ρ hρ ρ'
  constructor
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le (rationalLeviXi_nonneg hKc hM)
      (fun m => rationalHeight_nonneg ρ' m) (fun m => rationalHeight_nonneg ρ m) (fun m => hC m)
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le (rationalLeviXi_nonneg hKc hM)
      (fun m => rationalHeight_nonneg ρ m) (fun m => rationalHeight_nonneg ρ' m) (fun m => hC' m)

end Tempered

section Induction

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The actual standard unipotent subgroup `U_J(F)` is unimodular, for `J` the root set of a
finite set `I` of simple roots (the Library's
`standardUnipotent_isUnimodular_of_standardCocharacterStatement`). -/
theorem isUnimodularModulus_standardUnipotentPoints (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I : Finset (Aubert.General.RationalPointFamily.SimpleRoot i ν))
    (hI : Aubert.General.RationalPointFamily.rootSet i ν I = J) :
    Aubert.General.IsUnimodularModulus (standardUnipotentPoints i ν J)
      (isClosed_standardUnipotentPoints i ν J) := by
  subst hI
  open Aubert.General.RationalPointFamily in
  exact standardUnipotent_isUnimodular_of_standardCocharacterStatement
    i ν standardCocharacter hG hi hν I _

/-- For connected reductive `G`, Mathlib's modular character of the actual standard parabolic
`P_J(F)` is the Haar modulus of conjugation on `U_J(F)`: the Library's
`RationalParabolicModulusStatement`, proved by `rationalParabolicModulus_of_reductiveUnimodularity`
with `rationalReductiveUnimodularity` and `dynamicCentralizerReductive`. -/
theorem modularCharacter_standardParabolicPoints (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I : Finset (Aubert.General.RationalPointFamily.SimpleRoot i ν))
    (hI : Aubert.General.RationalPointFamily.rootSet i ν I = J)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    [LocallyCompactSpace (standardParabolicPoints i ν J)]
    (q : standardParabolicPoints i ν J) :
    Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν J)
        (isClosed_standardUnipotentPoints i ν J) (standardParabolicPoints i ν J)
        (isSemidirectDecomposition_standard hG hi hν hJ).le_normalizer q : ℝ≥0) := by
  subst hI
  have := hi.isSplitSubtorus.mono
  have hmod := Aubert.General.RationalPointFamily.rationalParabolicModulus_of_reductiveUnimodularity
    Aubert.General.RationalPointFamily.rationalReductiveUnimodularity
    GroupScheme.dynamicCentralizerReductive
  have hP := Aubert.General.RationalPointFamily.isClosed_standard_parabolic i ν
    standardCocharacter hG hi hν I
  have hc := Aubert.General.RationalPointFamily.continuous_standard_projection i ν
    standardCocharacter hG hi hν I
  exact (hmod F G hG S i hi ν hν standardCocharacter I
    (isClosed_standardUnipotentPoints i ν _) hP hc).2 q

/-- **Waldspurger, Lemme III.2.3** (printed p. 266) on actual rational points, for an actual
standard parabolic `P_J = M_J U_J ⊇ P₀` of a connected reductive group (`J` the root set of a
finite set `I` of simple roots). Let `K` be a compact open subgroup with `G(F) = P₀(F) K` and
`M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`, and `ρ` a closed matrix representation with
`ρ(K) ⊆ GL_N(𝒪)`. If the coefficients of an admissible smooth representation `A` of `M_J(F)` have
tempered growth for `Ξ^{M_J}` (`rationalLeviXi`) and `σ|_{M_J}`, then the coefficients of the
actual normalized induced representation `I_{P_J}^G A` have tempered growth for `Ξ`
(`rationalXi`) and `σ` (`rationalHeight ρ`). -/
theorem rationalHasTemperedCoefficients_normalizedInduction (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (I : Finset (Aubert.General.RationalPointFamily.SimpleRoot i ν))
    (hI : Aubert.General.RationalPointFamily.rootSet i ν I = J)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν J)))
    (hρ : IsClosedSubgroup ρ)
    (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) (hA : A.IsAdmissible)
    (hT : HasTemperedCoefficients (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m) A.representation) :
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      ((Aubert.General.normalizedInductionFunctor (isSemidirectDecomposition_standard hG hi hν hJ)
        (isClosed_standardUnipotentPoints i ν J)).obj A).representation := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have hPc : IsClosed (standardParabolicPoints i ν J : Set (rationalPoints G)) := by
    subst hI
    exact Aubert.General.RationalPointFamily.isClosed_standard_parabolic i ν
      standardCocharacter hG hi hν I
  have : LocallyCompactSpace (standardParabolicPoints i ν J) := hPc.locallyCompactSpace
  have hle := standardParabolicPoints_empty_le hG hi hν hJ
  have hσK : ∀ k ∈ (K : Subgroup (rationalPoints G)), ∀ g : rationalPoints G,
      rationalHeight (F := F) ρ (k * g) = rationalHeight (F := F) ρ g := by
    intro k hk g
    have h := rationalHeight_mul_mul ρ (hKρ hk) (rationalHeightSubgroup (F := F) ρ).one_mem g
    rwa [mul_one] at h
  exact hasTemperedCoefficients_normalizedInduction_of_tempered
    (isSemidirectDecomposition_standard hG hi hν hJ) (isClosed_standardUnipotentPoints i ν J) A K
    hKc hPc (continuous_projection_standard hG hi hν hJ _)
    (fun g => by
      obtain ⟨p, hp, k, hk, e⟩ := hPK g
      exact ⟨p, hle hp, k, hk, e⟩)
    (fun g => Aubert.General.RationalPointFamily.rationalReductiveUnimodularity F G hG
      standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I hI hJ) hA
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I hI)
    (rationalLeviData hG hi hν hJ K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    (rationalHeight_nonneg ρ) (fun m => rationalHeight_nonneg ρ m)
    hσK
    (rationalLeviSigmaBound ρ hG hi hν hJ hρ hKc) hT

/-- **Lemme III.2.3 for every closed matrix representation**: under the hypotheses of
`rationalHasTemperedCoefficients_normalizedInduction` for one closed `ρ` with
`ρ(K) ⊆ GL_N(𝒪)`, temperedness of `A` for any closed `ρ'` implies temperedness of
`I_{P_J}^G A` for `ρ'` (`isRationalTempered_iff`, `isRationalLeviTempered_iff`). -/
theorem IsRationalLeviTempered.normalizedInduction (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (I : Finset (Aubert.General.RationalPointFamily.SimpleRoot i ν))
    (hI : Aubert.General.RationalPointFamily.rootSet i ν I = J)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν J)))
    (hρ : IsClosedSubgroup ρ)
    (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
    {N' : ℕ} [Nonempty (Fin N')] {ρ' : MatrixRepresentation G (Fin N')}
    (hρ' : IsClosedSubgroup ρ')
    {A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)} (hA : A.IsAdmissible)
    (hT : IsRationalLeviTempered hKc ρ' hM A) :
    IsRationalTempered hKc ρ' hPK
      ((Aubert.General.normalizedInductionFunctor (isSemidirectDecomposition_standard hG hi hν hJ)
        (isClosed_standardUnipotentPoints i ν J)).obj A) :=
  (isRationalTempered_iff hKc ρ hPK ρ' hρ hρ' _).mp
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν hJ I hI K hKc hPK hM hρ hKρ
      A hA ((isRationalLeviTempered_iff hKc ρ hM ρ' hρ hρ' A).mpr hT))

end Induction

end Langlands.HarishChandraSchwartz
