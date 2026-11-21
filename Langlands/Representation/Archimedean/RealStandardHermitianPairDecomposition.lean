import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLReduction
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealDiscretePresentation
import Langlands.Representation.Archimedean.RealGenericUnitaryInducingData
import Langlands.Representation.Archimedean.RealStandardHermitianDual
import Langlands.Representation.Archimedean.RealUnlinkedStandardPermutation

/-! # Hermitian pairs in real standard parameters -/

noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.RealLocalJacquet
open InductionStages (KFin)

private def reflectExponent (x : RealBlock) : RealBlock :=
  realBlockTwist (-2 * realBlockExponent x) x

private theorem exponent_reflect (x : RealBlock) :
    realBlockExponent (reflectExponent x) = -realBlockExponent x := by
  rw [reflectExponent, realBlockExponent_twist]
  ring

private theorem twist_zero (x : RealBlock) : realBlockTwist 0 x = x := by
  cases x <;> simp [realBlockTwist, RealCharacterCrossing.charData_eta, characterOfParams_eta]

private theorem twist_twist (a b : ℝ) (x : RealBlock) :
    realBlockTwist a (realBlockTwist b x) = realBlockTwist (b + a) x := by
  cases x <;>
    simp [realBlockTwist, RealJacquetFrobenius.charData, characterOfParams, add_assoc]

private theorem reflect_involutive : Function.Involutive reflectExponent := by
  intro x
  change realBlockTwist (-2 * realBlockExponent (reflectExponent x))
    (realBlockTwist (-2 * realBlockExponent x) x) = x
  rw [exponent_reflect, twist_twist]
  convert twist_zero x using 2
  ring

private theorem neg_conj_eq_add (t : ℂ) :
    conj (-t) = t + ((-2 * t.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
    ring
  · simp

private theorem normalize_hermitianDual (x : RealBlock)
    (hpos : ∀ d : ComplexCharacterData, x = .induced d → 0 < d.weight) :
    realBlockNormalize (realHermitianDualBlock x) = [reflectExponent x] := by
  cases x with
  | character d =>
    simp [realBlockNormalize, realBlockExpand, RealBlock.positiveWeight,
      realHermitianDualBlock, dualBlock, realBlockConjExponent, reflectExponent,
      realBlockTwist, realBlockExponent, RealCharacterData.inverse, neg_conj_eq_add]
  | induced d =>
    have hneg : -d.weight < 0 := neg_neg_of_pos (hpos d rfl)
    let t := d.exponent + ((-2 * d.exponent.re : ℝ) : ℂ)
    change realBlockNormalize (.induced (characterOfParams (-d.weight) (conj (-d.exponent)))) =
      [.induced (characterOfParams d.weight t)]
    rw [neg_conj_eq_add]
    let e := characterOfParams (-d.weight) t
    change realBlockNormalize (.induced e) = [.induced (characterOfParams d.weight t)]
    have he : e.weight < 0 := hneg
    simp only [realBlockNormalize, realBlockExpand, ite_eq_right he.ne, List.map_cons,
      List.map_nil, RealBlock.positiveWeight, ite_eq_left he, List.cons.injEq,
      RealBlock.induced.injEq, and_true]
    have heW : e.conj.weight = -(-d.weight) := rfl
    have heT : e.conj.exponent = t := rfl
    simpa only [heW, heT, neg_neg] using (characterOfParams_eta e.conj).symm

private theorem normalize_map_hermitianDual (ds : List RealBlock)
    (hpos : ∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight) :
    (ds.map realHermitianDualBlock).flatMap realBlockNormalize = ds.map reflectExponent := by
  induction ds with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.flatMap_cons,
      normalize_hermitianDual x (fun d hd => hpos d (by simp [hd])),
      ih (fun d hd => hpos d (List.mem_cons_of_mem _ hd)), List.singleton_append, List.map_cons]

private theorem reflect_perm (hunique : RealPositiveWeightStandardUniqueStatement)
    {n : ℕ} {ds : List RealBlock} (hrank : realRank ds = n)
    (hpos : ∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds)) :
    ds.Perm (ds.map reflectExponent) := by
  obtain ⟨heRank, A, hAi, hA⟩ := realStandard_hermitianDual_parameter hrank hirr hunit
  let es := ds.map realHermitianDualBlock
  let fs := es.flatMap realBlockNormalize
  have hF : RealInjectiveIntertwinerExists n fs ds :=
    (RealInjectiveIntertwinerExists.of_eq (realStandardModule_flatMap_normalize n es).symm
      rfl ⟨A, hAi, hA⟩)
  obtain ⟨B, hBi, hB⟩ := hF
  have hfRank : realRank fs = n := (realRank_flatMap_normalize es).trans heRank
  have hfParam : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) fs :=
    ⟨hfRank, B, hBi, hB⟩
  have hfI := (realStandardParameter_model hirr hgen hunit hfParam).2.1
  have hB0 : B ≠ 0 := by
    let hnt := hfI.1
    obtain ⟨v, hv⟩ := exists_ne (0 : kFiniteFunctions (realStandardModule n fs) (unitaryCompact ℝ n))
    intro hzero
    exact hv (hBi (by simp [hzero]))
  have hp := hunique n fs ds hfRank hrank
    (fun _ => weight_pos_of_mem_flatMap_normalize) hpos hfI hirr B hB
    ⟨hBi, hB.surjective hirr hB0⟩
  change ((ds.map realHermitianDualBlock).flatMap realBlockNormalize).Perm ds at hp
  rw [normalize_map_hermitianDual ds hpos] at hp
  exact hp.symm

private theorem untwist_is_unitary_discrete {x : RealBlock}
    (hx : ∀ d : ComplexCharacterData, x = .induced d → 0 < d.weight) :
    IsRealUnitaryDiscreteBlock (realBlockTwist (-realBlockExponent x) x) := by
  refine ⟨by rw [realBlockExponent_twist, add_neg_cancel], ?_⟩
  cases x with
  | character _ => trivial
  | induced d => exact hx d rfl

/-- A single unitary discrete block, or a pair of opposite real twists of one
such block. The twist in the pair has no upper bound in this definition. -/
def IsRealHermitianInducingFactor (blocks : List RealBlock) : Prop :=
  ∃ δ : RealBlock, IsRealUnitaryDiscreteBlock δ ∧
    (blocks = [δ] ∨ ∃ α : ℝ, 0 < α ∧
      blocks = [realBlockTwist α δ, realBlockTwist (-α) δ])

private theorem hermitian_factor_pair (x : RealBlock)
    (hx : ∀ d : ComplexCharacterData, x = .induced d → 0 < d.weight)
    (hne : realBlockExponent x ≠ 0) :
    ∃ blocks : List RealBlock, blocks.Perm [x, reflectExponent x] ∧
      IsRealHermitianInducingFactor blocks := by
  let t := realBlockExponent x
  let δ := realBlockTwist (-t) x
  have ht : t ≠ 0 := hne
  have hxδ : realBlockTwist t δ = x := by
    change realBlockTwist t (realBlockTwist (-t) x) = x
    rw [twist_twist, neg_add_cancel, twist_zero]
  have hyδ : realBlockTwist (-t) δ = reflectExponent x := by
    change realBlockTwist (-t) (realBlockTwist (-t) x) = realBlockTwist (-2 * t) x
    rw [twist_twist, show -t + -t = -2 * t by ring]
  have hδ : IsRealUnitaryDiscreteBlock δ := untwist_is_unitary_discrete hx
  rcases lt_or_gt_of_ne ht with ht | ht
  · refine ⟨[reflectExponent x, x], List.Perm.swap _ _ _, δ, hδ,
      Or.inr ⟨-t, neg_pos.mpr ht, ?_⟩⟩
    rw [hyδ, neg_neg, hxδ]
  · refine ⟨[x, reflectExponent x], List.Perm.refl _, δ, hδ, Or.inr ⟨t, ht, ?_⟩⟩
    rw [hxδ, hyδ]

private theorem hermitian_factors_of_perm (ds : List RealBlock)
    (hpos : ∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight)
    (hperm : ds.Perm (ds.map reflectExponent)) :
    ∃ factors : List (List RealBlock), factors.flatten.Perm ds ∧
      ∀ blocks ∈ factors, IsRealHermitianInducingFactor blocks := by
  classical
  generalize hn : ds.length = m
  induction m using Nat.strong_induction_on generalizing ds with
  | h m ih =>
    cases ds with
    | nil => exact ⟨[], by simp⟩
    | cons x xs =>
      have hxpos : ∀ d : ComplexCharacterData, x = .induced d → 0 < d.weight :=
        fun d hd => hpos d (by simp [hd])
      have hxspos : ∀ d : ComplexCharacterData, .induced d ∈ xs → 0 < d.weight :=
        fun d hd => hpos d (List.mem_cons_of_mem _ hd)
      by_cases hzero : realBlockExponent x = 0
      · have hreflect : reflectExponent x = x := by
          simp [reflectExponent, hzero, twist_zero]
        have hxperm : xs.Perm (xs.map reflectExponent) := by
          rw [List.map_cons, hreflect] at hperm
          exact hperm.cons_inv
        obtain ⟨factors, hflat, hfac⟩ := ih xs.length (by simp at hn; omega)
          xs hxspos hxperm rfl
        refine ⟨[x] :: factors, by simpa using hflat.cons x, ?_⟩
        intro blocks hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨x, ⟨hzero, by cases x with
            | character _ => trivial
            | induced d => exact hxpos d rfl⟩, Or.inl rfl⟩
        · exact hfac blocks hb
      · have hne : reflectExponent x ≠ x := by
          intro h
          have he := exponent_reflect x
          rw [h] at he
          exact hzero (by linarith)
        have hmem : reflectExponent x ∈ xs := by
          have hmem := hperm.mem_iff.mpr
            (List.mem_map_of_mem (show x ∈ x :: xs from List.mem_cons_self))
          exact (List.mem_cons.mp hmem).resolve_left hne
        let ys := xs.erase (reflectExponent x)
        have hy : xs.Perm (reflectExponent x :: ys) := List.perm_cons_erase hmem
        have hynorm : (x :: reflectExponent x :: ys).Perm
            (reflectExponent x :: x :: ys.map reflectExponent) := by
          simpa only [List.map_cons, reflect_involutive x] using
            (hy.cons x).symm.trans (hperm.trans ((hy.cons x).map reflectExponent))
        have hyp : ys.Perm (ys.map reflectExponent) :=
          (((List.Perm.swap x (reflectExponent x) ys).trans hynorm).cons_inv).cons_inv
        have hyspos : ∀ d : ComplexCharacterData, .induced d ∈ ys → 0 < d.weight :=
          fun d hd => hxspos d (List.mem_of_mem_erase hd)
        have hylen : ys.length < m := by
          have h := hy.length_eq
          simp only [List.length_cons] at h hn
          omega
        obtain ⟨factors, hflat, hfac⟩ := ih ys.length hylen ys hyspos hyp rfl
        obtain ⟨pair, hpair, hfactor⟩ := hermitian_factor_pair x hxpos hzero
        refine ⟨pair :: factors, ?_, ?_⟩
        · change (pair ++ factors.flatten).Perm (x :: xs)
          exact (hpair.append hflat).trans (hy.cons x).symm
        · intro blocks hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hfactor
          · exact hfac blocks hb

/-- Positive-weight parameter uniqueness groups the blocks of an irreducible, generic,
infinitesimally unitary real standard module into unitary discrete blocks and opposite
twist pairs, up to permutation. -/
def RealStandardHermitianPairDecompositionStatement : Prop :=
  RealPositiveWeightStandardUniqueStatement →
    ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      (∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight) →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
      IsRealGenericGKModule n (realStandardLie n ds) →
      IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
      ∃ factors : List (List RealBlock), factors.flatten.Perm ds ∧
        ∀ blocks ∈ factors, IsRealHermitianInducingFactor blocks

theorem realStandardHermitianPairDecomposition : RealStandardHermitianPairDecompositionStatement := by
  intro hunique n ds hrank hpos hirr hgen hunit
  exact hermitian_factors_of_perm ds hpos (reflect_perm hunique hrank hpos hirr hgen hunit)

private theorem unitary_discrete_twist_weight_pos {δ : RealBlock}
    (hδ : IsRealUnitaryDiscreteBlock δ) {a : ℝ} {d : ComplexCharacterData}
    (hd : .induced d = realBlockTwist a δ) : 0 < d.weight := by
  cases δ with
  | character c => cases hd
  | induced e =>
    cases hd
    exact hδ.2

private theorem reflect_twist {δ : RealBlock} (hδ : realBlockExponent δ = 0) (a : ℝ) :
    reflectExponent (realBlockTwist a δ) = realBlockTwist (-a) δ := by
  rw [reflectExponent, realBlockExponent_twist, hδ, zero_add, twist_twist]
  congr 1
  ring

private theorem hermitian_factor_normalized_dual_perm {A : List RealBlock}
    (hA : IsRealHermitianInducingFactor A) :
    ((A.map realHermitianDualBlock).flatMap realBlockNormalize).Perm A := by
  obtain ⟨δ, hδ, rfl | ⟨a, _, rfl⟩⟩ := hA
  · have hpos (d : ComplexCharacterData) (hd : .induced d ∈ [δ]) : 0 < d.weight := by
      rw [List.mem_singleton] at hd
      exact unitary_discrete_twist_weight_pos hδ (a := 0)
        (by simpa only [twist_zero] using hd)
    rw [normalize_map_hermitianDual _ hpos, List.map_cons, List.map_nil]
    simp [reflectExponent, hδ.1, twist_zero]
  · have hpos (d : ComplexCharacterData)
        (hd : .induced d ∈ [realBlockTwist a δ, realBlockTwist (-a) δ]) :
        0 < d.weight := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | hd
      · exact unitary_discrete_twist_weight_pos hδ hd
      · exact unitary_discrete_twist_weight_pos hδ hd
    rw [normalize_map_hermitianDual _ hpos]
    simp only [List.map_cons, List.map_nil, reflect_twist hδ.1, neg_neg]
    exact List.Perm.swap _ _ []

/-- An irreducible, pairwise unlinked Hermitian inducing factor is equivalent
to the standard module of its Hermitian-dual block list. -/
def RealHermitianInducingFactorDualEquivalenceStatement : Prop :=
  ∀ A : List RealBlock, IsRealHermitianInducingFactor A → A.Pairwise AreRealBlocksUnlinked →
    let n := realRank A
    let dual := A.map realHermitianDualBlock
    IsIrreducibleGKModule (realStandardRep n A) (realStandardLie n A) →
      ∃ E : KFin n A ≃ₗ[ℂ] KFin n dual,
        IsRealStandardIntertwiner n (realStandardRep n dual) (realStandardLie n dual) A
          E.toLinearMap

theorem realHermitianInducingFactor_dualEquiv :
    RealHermitianInducingFactorDualEquivalenceStatement := by
  intro A hA hu
  dsimp only
  intro hirr
  let n := realRank A
  let dual := A.map realHermitianDualBlock
  let normalized := dual.flatMap realBlockNormalize
  have hperm : normalized.Perm A := hermitian_factor_normalized_dual_perm hA
  have hrank : realRank normalized = n := realRank_perm hperm
  have hpair := hperm.symm.pairwise hu (fun h => h.symm)
  have hT := realUnlinkedStandardPermutation n normalized A hrank hpair hperm
  obtain ⟨T, hTi, hI⟩ := hT.of_eq (realStandardModule_flatMap_normalize n dual) rfl
  have hRankDual : realRank dual = n := (realRank_flatMap_normalize dual).symm.trans hrank
  let hnontrivial := realStandardNontrivial n dual hRankDual
  have hT0 : T ≠ 0 := by
    obtain ⟨f, hf⟩ := exists_ne (0 : KFin n dual)
    intro hzero
    exact hf (hTi (by simp [hzero]))
  have hbij : Function.Bijective T := ⟨hTi, hI.surjective hirr hT0⟩
  exact ⟨(LinearEquiv.ofBijective T hbij).symm, RealDiscretePresentation.isGKMap_symm hI hbij⟩

end Langlands.Archimedean
