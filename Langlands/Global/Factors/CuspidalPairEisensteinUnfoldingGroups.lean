import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingCells
import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Global.RankinSelberg.UnfoldingCoefficient
import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Langlands.Global.GeneralLinearBlockSemidirectPeriod

/-! # Pattern subgroups of the adelic upper unitriangular group

On the adelic points `N₀(𝔸)` of the upper unitriangular subgroup functor of `GL_n`, this module
gives the matrix of a point, the embedding of the rational upper unitriangular matrices onto the
rational subgroup `N₀(F)`, and for a subset `J` of the coordinates the closed pattern subgroup
`Λ_J(𝔸)` of points whose matrix has vanishing entries from `J` to its complement, with its
rational subgroup `Λ_J(F)`. The quotient `Λ_J(F) \ Λ_J(𝔸)` has finite Haar volume, by a column
by column rational reduction into a compact set. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField MeasureTheory Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RankinSelbergGlobal.Unfolding RowEchelon PrimitiveAdelicHeight

local instance unfoldingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance unfoldingSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

instance unipotentAdelicLocallyCompact : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- The matrix of a point of `N₀(𝔸)`. -/
def toMat : unipotentAdelic F n →* AdelicGL F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).toMonoidHom.comp (unipotentAdelic F n).subtype

theorem toMat_apply (x : unipotentAdelic F n) :
    toMat F n x = GeneralLinearGroupPoints.adelicEquiv F n (x : Points F n) := rfl

theorem continuous_toMat : Continuous (toMat F n) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp continuous_subtype_val

theorem toMat_injective : Function.Injective (toMat F n) := fun _ _ h =>
  Subtype.ext ((GeneralLinearGroupPoints.adelicEquiv F n).injective h)

theorem isUnitriangular_toMat (x : unipotentAdelic F n) :
    IsUnitriangular (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) :=
  (mem_unipotentAdelic_iff F x.val).mp x.property

theorem toMat_mem_upperUnipotent (x : unipotentAdelic F n) :
    toMat F n x ∈ GeneralLinear.upperUnipotent n (Adeles F) :=
  isUnitriangular_toMat F n x

/-- The point of `N₀(𝔸)` with a given upper unitriangular matrix. -/
def ofMat (g : AdelicGL F n) (hg : g ∈ GeneralLinear.upperUnipotent n (Adeles F)) :
    unipotentAdelic F n :=
  ⟨(GeneralLinearGroupPoints.adelicEquiv F n).symm g, (mem_unipotentAdelic_iff F _).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact hg)⟩

@[simp] theorem toMat_ofMat (g : AdelicGL F n) (hg : g ∈ GeneralLinear.upperUnipotent n (Adeles F)) :
    toMat F n (ofMat F n g hg) = g := by
  simp [toMat, ofMat]

theorem ofMat_toMat (x : unipotentAdelic F n) :
    ofMat F n (toMat F n x) (toMat_mem_upperUnipotent F n x) = x :=
  toMat_injective F n (toMat_ofMat F n _ _)

/-- The rational upper unitriangular matrices, as points of `N₀(𝔸)`. -/
def ratHom : GeneralLinear.upperUnipotent n F →* unipotentAdelic F n where
  toFun δ := ⟨AdelicGroupPoints.rational F (Scheme F n)
      ((GeneralLinearGroupPoints.rationalEquiv F n).symm δ), (mem_unipotentAdelic_iff F _).mpr (by
    rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]
    exact (show IsUnitriangular ((δ : Matrix.GeneralLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) from δ.2).map (algebraMap F (Adeles F)))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' δ δ' := by
    apply Subtype.ext
    simp

theorem toMat_ratHom (δ : GeneralLinear.upperUnipotent n F) :
    toMat F n (ratHom F n δ) = AdelicGL.rational F n δ := by
  change GeneralLinearGroupPoints.adelicEquiv F n (AdelicGroupPoints.rational F (Scheme F n)
    ((GeneralLinearGroupPoints.rationalEquiv F n).symm δ)) = _
  rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]

theorem ratHom_injective : Function.Injective (ratHom F n) := by
  intro δ δ' h
  have := congrArg (toMat F n) h
  rw [toMat_ratHom, toMat_ratHom] at this
  exact Subtype.ext (AdelicGL.rational_injective F n this)

/-- The rational subgroup `N₀(F)` of `N₀(𝔸)`. -/
abbrev Γ₀ : Subgroup (unipotentAdelic F n) :=
  AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)

theorem mem_Γ₀_iff (x : unipotentAdelic F n) :
    x ∈ Γ₀ F n ↔ ∃ δ : GeneralLinear.upperUnipotent n F, ratHom F n δ = x := by
  constructor
  · rintro ⟨q, rfl⟩
    have hq := (mem_rationalPoints_upperUnipotent_iff F q.val).mp q.property
    refine ⟨⟨GeneralLinearGroupPoints.rationalEquiv F n q.val, hq⟩, Subtype.ext ?_⟩
    change AdelicGroupPoints.rational F (Scheme F n)
      ((GeneralLinearGroupPoints.rationalEquiv F n).symm
        (GeneralLinearGroupPoints.rationalEquiv F n q.val)) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨δ, rfl⟩
    refine ⟨⟨(GeneralLinearGroupPoints.rationalEquiv F n).symm δ,
      (mem_rationalPoints_upperUnipotent_iff F _).mpr ?_⟩, rfl⟩
    rw [MulEquiv.apply_symm_apply]
    exact δ.2

theorem ratHom_mem_Γ₀ (δ : GeneralLinear.upperUnipotent n F) : ratHom F n δ ∈ Γ₀ F n :=
  (mem_Γ₀_iff F n _).mpr ⟨δ, rfl⟩

theorem isDiscrete_Γ₀ : IsDiscrete (Γ₀ F n : Set (unipotentAdelic F n)) :=
  AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)

/-! ### Pattern subgroups -/

/-- The pattern subgroup `Λ_J(𝔸)` of `N₀(𝔸)`. -/
def pattern (J : Finset (Fin n)) : Subgroup (unipotentAdelic F n) :=
  (stabilizer (R := Adeles F) J).comap (toMat F n)

theorem mem_pattern_iff (J : Finset (Fin n)) (x : unipotentAdelic F n) :
    x ∈ pattern F n J ↔ ∀ i ∈ J, ∀ j, j ∉ J →
      (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) i j = 0 :=
  ⟨fun h => h.2, fun h => ⟨toMat_mem_upperUnipotent F n x, h⟩⟩

theorem isClosed_pattern (J : Finset (Fin n)) :
    IsClosed (pattern F n J : Set (unipotentAdelic F n)) := by
  have : T2Space (Adeles F) := GeneralLinearBlockSemidirect.adeleRing_t2Space F
  have hset : (pattern F n J : Set (unipotentAdelic F n)) =
      ⋂ i ∈ J, ⋂ j ∈ (Jᶜ : Finset (Fin n)),
        (fun x : unipotentAdelic F n =>
          (toMat F n x : Matrix (Fin n) (Fin n) (Adeles F)) i j) ⁻¹' {0} := by
    ext x
    simp only [SetLike.mem_coe, mem_pattern_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_compl]
  rw [hset]
  refine isClosed_biInter fun i _ => isClosed_biInter fun j _ => ?_
  refine isClosed_singleton.preimage ?_
  exact ((continuous_apply j).comp (continuous_apply i)).comp
    (Units.continuous_val.comp (continuous_toMat F n))

instance (J : Finset (Fin n)) : IsClosed (pattern F n J : Set (unipotentAdelic F n)) :=
  isClosed_pattern F n J

/-- The rational subgroup `Λ_J(F)` of the pattern subgroup. -/
def patternLattice (J : Finset (Fin n)) : Subgroup (pattern F n J) :=
  (Γ₀ F n).comap (pattern F n J).subtype

theorem isDiscrete_patternLattice (J : Finset (Fin n)) :
    IsDiscrete (patternLattice F n J : Set (pattern F n J)) := by
  have hd : IsDiscrete ((fun x : pattern F n J => (x : unipotentAdelic F n)) ⁻¹'
      (Γ₀ F n : Set (unipotentAdelic F n))) :=
    (isDiscrete_Γ₀ F n).preimage continuous_subtype_val.continuousOn Subtype.val_injective
  exact hd

theorem ratHom_mem_pattern_iff (J : Finset (Fin n)) (δ : GeneralLinear.upperUnipotent n F) :
    ratHom F n δ ∈ pattern F n J ↔ (δ : Matrix.GeneralLinearGroup (Fin n) F) ∈ stabilizer J := by
  rw [mem_pattern_iff, toMat_ratHom]
  refine ⟨fun h => ⟨δ.2, fun i hi j hj => ?_⟩, fun h i hi j hj => ?_⟩
  · have := h i hi j hj
    rw [AdelicGL.rational_apply] at this
    exact (AdeleRing.algebraMap_injective (𝓞 F) F) (this.trans (map_zero _).symm)
  · rw [AdelicGL.rational_apply, h.2 i hi j hj, map_zero]

/-- The image of `Λ_J(F)` in `N₀(𝔸)`. -/
def patternRational (J : Finset (Fin n)) : Subgroup (unipotentAdelic F n) :=
  Γ₀ F n ⊓ pattern F n J

theorem mem_patternRational_iff_image (J : Finset (Fin n)) (x : unipotentAdelic F n) :
    x ∈ patternRational F n J ↔ ∃ l : patternLattice F n J, ((l : pattern F n J) :
      unipotentAdelic F n) = x := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨x, h2⟩, h1⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l.2, (l : pattern F n J).2⟩

/-! ### Reduction into a compact set -/

/-- A column step of the reduction, keeping the pattern of `J`. -/
theorem exists_pattern_column_step (J : Finset (Fin n)) {D : Set (Adeles F)}
    (hD : ∀ a : Adeles F, ∃ f : F, algebraMap F (Adeles F) f + a ∈ D)
    {M : Matrix (Fin n) (Fin n) (Adeles F)} (hM : IsUnitriangular M)
    {mu : Matrix (Fin n) (Fin n) F} (hmu : IsUnitriangular mu)
    (hmuJ : ∀ i ∈ J, ∀ j, j ∉ J → mu i j = 0) (m : Fin n) :
    ∃ mu' : Matrix (Fin n) (Fin n) F, IsUnitriangular mu' ∧ (∀ i ∈ J, ∀ j, j ∉ J → mu' i j = 0) ∧
      (∀ i j, j < m → (mu'.map (algebraMap F (Adeles F)) * M) i j =
        (mu.map (algebraMap F (Adeles F)) * M) i j) ∧
      ∀ i, i < m → ¬(i ∈ J ∧ m ∉ J) → (mu'.map (algebraMap F (Adeles F)) * M) i m ∈ D := by
  classical
  choose c hc using fun i => hD ((mu.map (algebraMap F (Adeles F)) * M) i m)
  set E : Matrix (Fin n) (Fin n) F := Matrix.of fun i j =>
    if j = m ∧ i < m ∧ ¬(i ∈ J ∧ m ∉ J) then c i else 0 with hEdef
  have hE : ∀ i j, (E.map (algebraMap F (Adeles F)) * M) i j =
      if i < m ∧ ¬(i ∈ J ∧ m ∉ J) then algebraMap F (Adeles F) (c i) * M m j else 0 := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single m]
    · rw [Matrix.map_apply, hEdef, Matrix.of_apply]
      by_cases hi : i < m ∧ ¬(i ∈ J ∧ m ∉ J)
      · rw [ite_eq_left ⟨rfl, hi⟩, ite_eq_left hi]
      · rw [ite_eq_right fun h => hi h.2, ite_eq_right hi, map_zero, zero_mul]
    · intro k _ hkm
      rw [Matrix.map_apply, hEdef, Matrix.of_apply, ite_eq_right fun h => hkm h.1, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h
  have hmap : (mu + E).map (algebraMap F (Adeles F)) =
      mu.map (algebraMap F (Adeles F)) + E.map (algebraMap F (Adeles F)) :=
    Matrix.map_add _ (map_add (algebraMap F (Adeles F))) mu E
  refine ⟨mu + E, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i hi j hj => ?_, fun i j hj => ?_,
    fun i hi hiJ => ?_⟩
  · rw [Matrix.add_apply, hmu.1 hij, hEdef, Matrix.of_apply, zero_add, ite_eq_right]
    rintro ⟨rfl, h, _⟩
    exact lt_irrefl _ (lt_trans hij h)
  · rw [Matrix.add_apply, hmu.2 i, hEdef, Matrix.of_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, h, _⟩
    exact lt_irrefl _ h
  · rw [Matrix.add_apply, hmuJ i hi j hj, hEdef, Matrix.of_apply, zero_add, ite_eq_right]
    rintro ⟨rfl, _, h⟩
    exact h ⟨hi, hj⟩
  · rw [hmap, Matrix.add_mul, Matrix.add_apply, hE]
    split_ifs with h
    · rw [hM.1 hj, mul_zero, add_zero]
    · rw [add_zero]
  · rw [hmap, Matrix.add_mul, Matrix.add_apply, hE, ite_eq_left ⟨hi, hiJ⟩, hM.2 m, mul_one, add_comm]
    exact hc i

/-- Iterating the column steps: every adelic unitriangular matrix is carried, by left
multiplication with a rational unitriangular matrix with the pattern of `J`, to a matrix whose
entries above the diagonal outside the positions from `J` to its complement lie in `D`. -/
theorem exists_pattern_mul_mem (J : Finset (Fin n)) {D : Set (Adeles F)}
    (hD : ∀ a : Adeles F, ∃ f : F, algebraMap F (Adeles F) f + a ∈ D)
    {M : Matrix (Fin n) (Fin n) (Adeles F)} (hM : IsUnitriangular M) :
    ∃ mu : Matrix (Fin n) (Fin n) F, IsUnitriangular mu ∧ (∀ i ∈ J, ∀ j, j ∉ J → mu i j = 0) ∧
      ∀ i j, i < j → ¬(i ∈ J ∧ j ∉ J) → (mu.map (algebraMap F (Adeles F)) * M) i j ∈ D := by
  suffices h : ∀ m : ℕ, ∃ mu : Matrix (Fin n) (Fin n) F, IsUnitriangular mu ∧
      (∀ i ∈ J, ∀ j, j ∉ J → mu i j = 0) ∧
      ∀ i j : Fin n, i < j → j.val < m → ¬(i ∈ J ∧ j ∉ J) →
        (mu.map (algebraMap F (Adeles F)) * M) i j ∈ D by
    obtain ⟨mu, hmu, hmuJ, h⟩ := h n
    exact ⟨mu, hmu, hmuJ, fun i j hij hJ => h i j hij j.isLt hJ⟩
  intro m
  induction m with
  | zero => exact ⟨1, isUnitriangular_one, fun i hi j hj => by
      rw [Matrix.one_apply_ne]; rintro rfl; exact hj hi, fun i j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨mu, hmu, hmuJ, h⟩ := ih
    by_cases hm : m < n
    · obtain ⟨mu', hmu', hmuJ', hsame, hnew⟩ :=
        exists_pattern_column_step F n J hD hM hmu hmuJ ⟨m, hm⟩
      refine ⟨mu', hmu', hmuJ', fun i j hij hj hJ => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · rw [hsame i j (Fin.lt_def.mpr hj)]
        exact h i j hij hj hJ
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        exact hnew i hij hJ
    · exact ⟨mu, hmu, hmuJ, fun i j hij _ hJ =>
        h i j hij (lt_of_lt_of_le j.isLt (not_lt.mp hm)) hJ⟩

instance patternLocallyCompact (J : Finset (Fin n)) : LocallyCompactSpace (pattern F n J) :=
  (isClosed_pattern F n J).locallyCompactSpace

instance unipotentAdelicSecondCountable : SecondCountableTopology (unipotentAdelic F n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance patternSecondCountable (J : Finset (Fin n)) : SecondCountableTopology (pattern F n J) :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The point of `N₀(𝔸)` with a given unitriangular matrix, continuously in the matrix. -/
def ofUnitriangular (M : {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M}) :
    unipotentAdelic F n :=
  ofMat F n (unitriangularUnit M.1 M.2) M.2

theorem continuous_ofUnitriangular : Continuous (ofUnitriangular F n) := by
  have hf : Continuous fun M : {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M} =>
      unitriangularUnit M.1 M.2 :=
    Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩
  exact ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp hf).subtype_mk _

theorem toMat_ofUnitriangular (M : {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M}) :
    (toMat F n (ofUnitriangular F n M) : Matrix (Fin n) (Fin n) (Adeles F)) = M.1 := by
  simp [ofUnitriangular, unitriangularUnit]

/-- **Compact reduction for pattern subgroups.** -/
theorem exists_isCompact_pattern_cover (J : Finset (Fin n)) :
    ∃ K : Set (pattern F n J), IsCompact K ∧
      ∀ x : pattern F n J, ∃ c ∈ patternLattice F n J, c * x ∈ K := by
  classical
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  have : T2Space (Adeles F) := GeneralLinearBlockSemidirect.adeleRing_t2Space F
  let Ω : Set {M : Matrix (Fin n) (Fin n) (Adeles F) // IsUnitriangular M} :=
    {M | ∀ i j, i < j → M.1 i j ∈ D ∪ {0}}
  have hΩ : IsCompact Ω := by
    have hbox := isCompact_unitriangularBox F (n := n) (hDc.union (isCompact_singleton (x := (0 : Adeles F))))
    have hemb : Topology.IsEmbedding (fun M : {M : Matrix (Fin n) (Fin n) (Adeles F) //
        IsUnitriangular M} => M.1) := Topology.IsEmbedding.subtypeVal
    rw [hemb.isCompact_iff]
    convert hbox using 1
    ext M
    simp only [Set.mem_image, Set.mem_ofPred_eq, Ω, unitriangularBox]
    constructor
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N.2, hN⟩
    · rintro ⟨hM, hMD⟩
      exact ⟨⟨M, hM⟩, hMD, rfl⟩
  let KH : Set (unipotentAdelic F n) := ofUnitriangular F n '' Ω
  have hKH : IsCompact KH := hΩ.image (continuous_ofUnitriangular F n)
  refine ⟨Subtype.val ⁻¹' KH,
    (isClosed_pattern F n J).isClosedEmbedding_subtypeVal.isCompact_preimage hKH, fun x => ?_⟩
  have hx := isUnitriangular_toMat F n x.1
  obtain ⟨mu, hmu, hmuJ, hred⟩ := exists_pattern_mul_mem F n J hD hx
  let δ : GeneralLinear.upperUnipotent n F := ⟨unitriangularUnit mu hmu, hmu⟩
  have hδ : (δ : Matrix.GeneralLinearGroup (Fin n) F) ∈ stabilizer J := ⟨hmu, hmuJ⟩
  refine ⟨⟨ratHom F n δ, (ratHom_mem_pattern_iff F n J δ).mpr hδ⟩, ratHom_mem_Γ₀ F n δ, ?_⟩
  have hmat : (toMat F n (ratHom F n δ * x.1) : Matrix (Fin n) (Fin n) (Adeles F)) =
      mu.map (algebraMap F (Adeles F)) * (toMat F n x.1 : Matrix (Fin n) (Fin n) (Adeles F)) := by
    rw [map_mul, toMat_ratHom, Units.val_mul]
    rfl
  have hprod : IsUnitriangular (mu.map (algebraMap F (Adeles F)) *
      (toMat F n x.1 : Matrix (Fin n) (Fin n) (Adeles F))) := (hmu.map _).mul hx
  refine ⟨⟨_, hprod⟩, fun i j hij => ?_, ?_⟩
  · by_cases hJ : i ∈ J ∧ j ∉ J
    · right
      change (mu.map (algebraMap F (Adeles F)) *
        (toMat F n x.1 : Matrix (Fin n) (Fin n) (Adeles F))) i j ∈ ({0} : Set (Adeles F))
      rw [← hmat, Set.mem_singleton_iff]
      exact (mem_pattern_iff F n J _).mp ((pattern F n J).mul_mem
        ((ratHom_mem_pattern_iff F n J δ).mpr hδ) x.2) i hJ.1 j hJ.2
    · left
      exact hred i j hij hJ
  · apply toMat_injective
    apply Units.ext
    rw [toMat_ofUnitriangular]
    exact hmat.symm

theorem countable_patternLattice (J : Finset (Fin n)) : Countable (patternLattice F n J) :=
  LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_patternLattice F n J)

theorem isFiniteMeasure_patternQuotient (J : Finset (Fin n)) :
    IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure (patternLattice F n J)
      (isDiscrete_patternLattice F n J)) := by
  obtain ⟨K, hK, hcover⟩ := exists_isCompact_pattern_cover F n J
  exact LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_isCompact _ _ hK hcover

theorem haar_pattern_isMulRightInvariant (J : Finset (Fin n)) :
    (Measure.haar : Measure (pattern F n J)).IsMulRightInvariant := by
  have := isFiniteMeasure_patternQuotient F n J
  exact LeftCosetSpace.isMulRightInvariant_haar_of_isFiniteMeasure _
    (isDiscrete_patternLattice F n J)

theorem haar_pattern_isInvInvariant (J : Finset (Fin n)) :
    (Measure.haar : Measure (pattern F n J)).IsInvInvariant := by
  have := haar_pattern_isMulRightInvariant F n J
  exact isInvInvariant_of_isMulRightInvariant _

end Langlands.Global.CuspidalPairEisenstein.Unfolding
