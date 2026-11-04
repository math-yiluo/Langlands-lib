import Langlands.Representation.Aubert.BooleanIntervalComplex
import Langlands.Representation.Aubert.FilteredCutDiagram
import Langlands.Representation.Aubert.CutDiagramEquivalence
import Langlands.Group.RelativeWeylSolomonProof

/-!
# Boolean contraction of the surviving graded pieces

A graded piece `S.quotientDiagram U` of a filtered signed cut diagram is
contracted when, on a set of surviving cut sets, its coordinates are identified
with one coefficient module `X` by maps under which the actual transitions are
identities, and it vanishes off the survivors. If the survivors form a Boolean
interval, the graded piece is naturally equivalent to the published constant
interval diagram, so its homogeneous signed differentials are exact below the
top of the interval and injective at the start.

The Coxeter part identifies the survivors `K ⊆ S \ s` with `w` minimal in
`W_{S \ s} w W_I` as the interval between the left descents of `w` and
`S \ K`, and bounds `|K| ≤ |I|` when `W_K = w W_I w⁻¹`.
-/

noncomputable section

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
variable {Mx : CoxeterMatrix B} (cs : CoxeterSystem Mx W)

/-- The left descents of `w`: simple `j` with `ℓ(s_j w) ≤ ℓ(w)`. -/
def leftDescentSet [Fintype B] (w : W) : Finset B :=
  Finset.univ.filter fun j => ¬ cs.length w < cs.length (cs.simple j * w)

theorem mem_leftDescentSet [Fintype B] {w : W} {j : B} :
    j ∈ leftDescentSet cs w ↔ ¬ cs.length w < cs.length (cs.simple j * w) := by
  simp [leftDescentSet]

/-- Minimality in a double coset passes to a smaller left subgroup. -/
theorem isMinimal_of_subset_left {I J K : Finset B} {w : W} (h : IsMinimal cs J I w)
    (hKJ : K ⊆ J) : IsMinimal cs K I w :=
  fun a ha b hb => h a (standardSubgroup_mono cs hKJ ha) b hb

/-- For right-`I`-minimal `w`, minimality in `W_{S \ s} w W_I` says that `s`
contains every left descent of `w`. -/
theorem isMinimal_univ_sdiff_iff [Fintype B] [DecidableEq B] {I : Finset B} {w : W}
    (hR : ∀ i ∈ I, cs.length w < cs.length (w * cs.simple i)) (s : Finset B) :
    IsMinimal cs (Finset.univ \ s) I w ↔ leftDescentSet cs w ⊆ s := by
  rw [minimalityLengthCriterion_proof cs]
  constructor
  · rintro ⟨hL, -⟩ j hj
    by_contra hjs
    exact (mem_leftDescentSet cs).mp hj
      (hL j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjs⟩))
  · intro hsub
    refine ⟨fun j hj => ?_, hR⟩
    by_contra hlt
    exact (Finset.mem_sdiff.mp hj).2 (hsub ((mem_leftDescentSet cs).mpr hlt))

/-- Minimality in `W_J w W_I` gives right-`I`-minimality. -/
theorem right_length_lt_of_isMinimal {I J : Finset B} {w : W} (h : IsMinimal cs J I w) :
    ∀ i ∈ I, cs.length w < cs.length (w * cs.simple i) :=
  ((minimalityLengthCriterion_proof cs J I w).mp h).2

/-- If `w⁻¹ W_K w ⊆ W_I` at a representative minimal in `W_K w W_I`, then each
`s_k` is conjugate to a distinct `s_i`, so `|K| ≤ |I|`. -/
theorem card_le_of_conj_mem [Fintype B] {I K : Finset B} {w : W}
    (hmin : IsMinimal cs K I w)
    (hK : ∀ k ∈ K, w⁻¹ * cs.simple k * w ∈ standardSubgroup cs I) :
    K.card ≤ I.card := by
  have hmin' := isMinimal_inv cs hmin
  have hex : ∀ k ∈ K, ∃ i ∈ I, w⁻¹ * cs.simple k * w⁻¹⁻¹ = cs.simple i :=
    fun k hk => exists_conj_simple_eq_of_isMinimal cs hmin' hk
      (by rw [inv_inv]; exact hK k hk)
  choose! f hfI hf using hex
  refine Finset.card_le_card_of_injOn f (fun k hk => hfI k hk) ?_
  intro k hk k' hk' hkk'
  apply simple_reflection_injective cs
  have h1 := hf k hk
  have h2 := hf k' hk'
  rw [hkk'] at h1
  have h3 : w⁻¹ * cs.simple k * w⁻¹⁻¹ = w⁻¹ * cs.simple k' * w⁻¹⁻¹ := h1.trans h2.symm
  simpa using h3

/-- The standard subset conjugate to `W_I` by `w` is unique. -/
theorem eq_of_standardSubgroup_conj [Fintype B] {I K K' : Finset B} {w : W}
    (hK : ∀ a, a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I)
    (hK' : ∀ a, a ∈ standardSubgroup cs K' ↔ w⁻¹ * a * w ∈ standardSubgroup cs I) :
    K = K' :=
  standardSubgroup_injective cs (Subgroup.ext fun a => (hK a).trans (hK' a).symm)

section Actual

variable {G : Type v} [Group G] {T : Subgroup G}

theorem mem_inclusion_range_iff (L : Subgroup G) (a : RelativeWeyl.Weyl T) :
    a ∈ (RelativeWeyl.inclusion T L).range ↔
      ∃ n : RelativeWeyl.normalizer T, (n : G) ∈ L ∧ (QuotientGroup.mk n : RelativeWeyl.Weyl T) = a := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H n => exact ⟨⟨n, n.2.1⟩, n.2.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨QuotientGroup.mk ⟨n, n.2, hn⟩, rfl⟩

/-- Under the actual Levi Weyl identification, a conjugation `M K = m⁻¹ M_I m`
by a lift `m` of `w⁻¹` gives `W_K = w W_I w⁻¹`. -/
theorem mem_standardSubgroup_iff_of_leviConj {L : Finset B → Subgroup G}
    {cs : ActualCoxeterSystem T Mx} (hL : actualLeviWeylIdentification T L cs)
    {I K : Finset B} (m : RelativeWeyl.normalizer T) {w : RelativeWeyl.Weyl T}
    (hw : (QuotientGroup.mk m : RelativeWeyl.Weyl T) = w⁻¹)
    (hK : ∀ x : G, x ∈ L I ↔ (m : G)⁻¹ * x * m ∈ L K) (a : RelativeWeyl.Weyl T) :
    a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I := by
  rw [← hL K, ← hL I, mem_inclusion_range_iff, mem_inclusion_range_iff]
  have hw' : w = (QuotientGroup.mk m : RelativeWeyl.Weyl T)⁻¹ := by rw [hw, inv_inv]
  subst hw'
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨m * n * m⁻¹, ?_, ?_⟩
    · rw [hK]
      simpa [mul_assoc] using hn
    · simp
  · rintro ⟨n, hn, hna⟩
    refine ⟨m⁻¹ * n * m, ?_, ?_⟩
    · have := (hK n).mp hn
      simpa [mul_assoc] using this
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hna]
      simp [mul_assoc]

end Actual

end Langlands.Group.RelativeWeylIndexing

namespace Langlands.Aubert.CutComplex

open Langlands.Group.RelativeWeylIndexing

universe uI uM uX

namespace BooleanInterval

variable {ι : Type uI} [LinearOrder ι]

theorem map_apply_of_active (lower upper : Finset ι) (X : Type uX) [AddCommGroup X]
    [Module ℂ X] {s t : Finset ι} (hst : s ⊆ t) (hs : Active lower upper s)
    (y : (diagram lower upper X).Obj s) (ht : PLift (Active lower upper t)) :
    (diagram lower upper X).map hst y ht = y ⟨hs⟩ :=
  dite_eq_left hs

theorem map_apply_of_not_active (lower upper : Finset ι) (X : Type uX) [AddCommGroup X]
    [Module ℂ X] {s t : Finset ι} (hst : s ⊆ t) (hs : ¬ Active lower upper s)
    (y : (diagram lower upper X).Obj s) (ht : PLift (Active lower upper t)) :
    (diagram lower upper X).map hst y ht = 0 :=
  dite_eq_right hs

variable [Fintype ι]

/-- For right-`I`-minimal `w`, the survivors `K ⊆ S \ s` with `w` minimal in
`W_{S \ s} w W_I` are the interval from the left descents of `w` to `S \ K`. -/
theorem survivor_iff_active {W : Type*} [Group W] {Mx : CoxeterMatrix ι}
    (cs : CoxeterSystem Mx W) {I K : Finset ι} {w : W}
    (hR : ∀ i ∈ I, cs.length w < cs.length (w * cs.simple i)) (s : Finset ι) :
    (K ⊆ Finset.univ \ s ∧ IsMinimal cs (Finset.univ \ s) I w) ↔
      Active (leftDescentSet cs w) (Finset.univ \ K) s := by
  rw [isMinimal_univ_sdiff_iff cs hR s]
  change _ ↔ leftDescentSet cs w ⊆ s ∧ s ⊆ Finset.univ \ K
  rw [Finset.subset_sdiff, Finset.subset_sdiff]
  simp only [Finset.subset_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩

end BooleanInterval

namespace Diagram.Subdiagram

variable {ι : Type uI} [LinearOrder ι] {D : Diagram.{uI,uM} ι} (S U : D.Subdiagram)

/-- Identification of the surviving coordinates of the graded piece
`U.obj s / S.obj s` with one coefficient module `X`: surjections with kernel the
lower step, natural for the actual transitions, and vanishing of the graded
piece off the survivors. -/
structure BooleanContraction (Surv : Finset ι → Prop) (X : Type uX) [AddCommGroup X]
    [Module ℂ X] where
  coeff : ∀ s, Surv s → U.obj s →ₗ[ℂ] X
  coeff_surjective : ∀ s (hs : Surv s), Function.Surjective (coeff s hs)
  coeff_eq_zero_iff : ∀ s (hs : Surv s) (x : U.obj s), coeff s hs x = 0 ↔ x.1 ∈ S.obj s
  coeff_natural : ∀ {s t : Finset ι} (hst : s ⊆ t) (hs : Surv s) (ht : Surv t)
    (x : U.obj s), coeff t ht ⟨D.map hst x.1, U.map_mem hst x.1 x.2⟩ = coeff s hs x
  inactive : ∀ s, ¬ Surv s → ∀ x ∈ U.obj s, x ∈ S.obj s

/-- A coordinate of the graded piece is zero when the upper step lies in the
lower one. -/
theorem quotient_subsingleton_of_le {s : Finset ι} (hle : ∀ x ∈ U.obj s, x ∈ S.obj s) :
    Subsingleton (U.obj s ⧸ S.denominator U s) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := (S.denominator U s).mkQ_surjective a
  obtain ⟨y, rfl⟩ := (S.denominator U s).mkQ_surjective b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact hle _ (x - y).2

theorem degree_subsingleton_of_le (hle : ∀ s, ∀ x ∈ U.obj s, x ∈ S.obj s) (k : ℕ) :
    Subsingleton ((S.quotientDiagram U).Degree k) := by
  have : ∀ s : {s : Finset ι // s.card = k},
      Subsingleton ((S.quotientDiagram U).Obj s.1) :=
    fun s => S.quotient_subsingleton_of_le U (hle s.1)
  infer_instance

section Exactness

variable [Fintype ι]

/-- A graded piece with no surviving coordinate is exact in every degree. -/
theorem quotient_exact_of_le (hle : ∀ s, ∀ x ∈ U.obj s, x ∈ S.obj s) (k : ℕ) :
    LinearMap.range ((S.quotientDiagram U).degreeDifferential k) =
      LinearMap.ker ((S.quotientDiagram U).degreeDifferential (k + 1)) := by
  have := S.degree_subsingleton_of_le U hle (k + 1)
  exact Subsingleton.elim _ _

theorem quotient_injective_of_le (hle : ∀ s, ∀ x ∈ U.obj s, x ∈ S.obj s) (k : ℕ) :
    Function.Injective ((S.quotientDiagram U).degreeDifferential k) := by
  have := S.degree_subsingleton_of_le U hle k
  intro x y _
  exact Subsingleton.elim _ _

end Exactness

namespace BooleanContraction

variable {S U} {Surv : Finset ι → Prop} {X : Type uX} [AddCommGroup X] [Module ℂ X]
  (C : S.BooleanContraction U Surv X) {lower upper : Finset ι}
  (hSurv : ∀ s, Surv s ↔ BooleanInterval.Active lower upper s)

/-- The coordinate comparison of the graded piece with the constant interval
coefficient. -/
def toBoolean (s : Finset ι) :
    U.obj s ⧸ S.denominator U s →ₗ[ℂ] (PLift (BooleanInterval.Active lower upper s) → X) :=
  (S.denominator U s).liftQ
    (LinearMap.pi fun hs => C.coeff s ((hSurv s).mpr hs.down))
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      funext hs
      exact (C.coeff_eq_zero_iff s _ x).mpr hx)

theorem toBoolean_mk (s : Finset ι) (x : U.obj s)
    (hs : PLift (BooleanInterval.Active lower upper s)) :
    C.toBoolean hSurv s ((S.denominator U s).mkQ x) hs =
      C.coeff s ((hSurv s).mpr hs.down) x := rfl

theorem toBoolean_bijective (s : Finset ι) : Function.Bijective (C.toBoolean hSurv s) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := (S.denominator U s).mkQ_surjective q
    rw [LinearMap.mem_ker] at hq
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    by_cases hs : BooleanInterval.Active lower upper s
    · have h0 := congrFun hq ⟨hs⟩
      exact (C.coeff_eq_zero_iff s ((hSurv s).mpr hs) x).mp h0
    · exact C.inactive s (fun h => hs ((hSurv s).mp h)) x.1 x.2
  · intro y
    by_cases hs : BooleanInterval.Active lower upper s
    · obtain ⟨x, hx⟩ := C.coeff_surjective s ((hSurv s).mpr hs) (y ⟨hs⟩)
      refine ⟨(S.denominator U s).mkQ x, ?_⟩
      funext hs'
      rcases hs' with ⟨hs'⟩
      exact hx
    · refine ⟨0, ?_⟩
      funext hs'
      exact absurd hs'.down hs

/-- The graded piece is naturally equivalent to the constant interval diagram. -/
def booleanEquivalence :
    Equivalence (S.quotientDiagram U) (BooleanInterval.diagram lower upper X) where
  obj s := LinearEquiv.ofBijective (C.toBoolean hSurv s) (C.toBoolean_bijective hSurv s)
  natural {s t} h q := by
    obtain ⟨x, rfl⟩ := (S.denominator U s).mkQ_surjective q
    funext ht
    change C.toBoolean hSurv t ((S.quotientDiagram U).map h ((S.denominator U s).mkQ x)) ht =
      (BooleanInterval.diagram lower upper X).map h
        (C.toBoolean hSurv s ((S.denominator U s).mkQ x)) ht
    rw [S.quotientDiagram_map_mk U h x, C.toBoolean_mk hSurv t]
    by_cases hs : BooleanInterval.Active lower upper s
    · refine Eq.trans ?_ (BooleanInterval.map_apply_of_active lower upper X h hs
        (C.toBoolean hSurv s ((S.denominator U s).mkQ x)) ht).symm
      exact (C.coeff_natural h _ _ x).trans (C.toBoolean_mk hSurv s x ⟨hs⟩).symm
    · refine Eq.trans ?_ (BooleanInterval.map_apply_of_not_active lower upper X h hs
        (C.toBoolean hSurv s ((S.denominator U s).mkQ x)) ht).symm
      apply (C.coeff_eq_zero_iff t _ _).mpr
      exact S.map_mem h x.1 (C.inactive s (fun h' => hs ((hSurv s).mp h')) x.1 x.2)

variable [Fintype ι]

include C hSurv

/-- Exactness of the graded piece below the top of the surviving interval. -/
theorem range_eq_ker (hlu : lower ⊆ upper) (k : ℕ) (hk : k + 1 < upper.card) :
    LinearMap.range ((S.quotientDiagram U).degreeDifferential k) =
      LinearMap.ker ((S.quotientDiagram U).degreeDifferential (k + 1)) :=
  ((C.booleanEquivalence hSurv).degreeDifferential_exact_iff k).mpr
    (BooleanInterval.exact_below_allowed lower upper X hlu k hk)

/-- Injectivity of the first graded differential for a nonempty top. -/
theorem injective_zero (hlu : lower ⊆ upper) (hcard : 0 < upper.card) :
    Function.Injective ((S.quotientDiagram U).degreeDifferential 0) :=
  ((C.booleanEquivalence hSurv).degreeDifferential_injective_iff 0).mpr
    (BooleanInterval.injective_before_allowed lower upper X hlu hcard)

end BooleanContraction

/-- The surviving cut sets of the graded piece at `w`: `K ⊆ S \ s` and `w`
minimal in `W_{S \ s} w W_I`. -/
def Survives [Fintype ι] {W : Type*} [Group W] {Mx : CoxeterMatrix ι}
    (cs : CoxeterSystem Mx W) (I K : Finset ι) (w : W) (s : Finset ι) : Prop :=
  K ⊆ Finset.univ \ s ∧ IsMinimal cs (Finset.univ \ s) I w

section Survivors

variable [Fintype ι] {S U} {W : Type*} [Group W] {Mx : CoxeterMatrix ι}
  (cs : CoxeterSystem Mx W) {I K : Finset ι} {w : W}
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

theorem card_le_terminal_of_survives
    (hconj : ∀ a, a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I)
    {s₀ : Finset ι} (hs₀ : Survives cs I K w s₀) :
    Fintype.card ι - I.card ≤ (Finset.univ \ K).card := by
  have hmin := isMinimal_of_subset_left cs hs₀.2 hs₀.1
  have hcard := card_le_of_conj_mem cs hmin
    (fun k hk => (hconj _).mp (simple_mem_standardSubgroup cs hk))
  rw [Finset.card_univ_sdiff]
  omega

/-- A contraction of a graded piece onto `X` over the survivors at `w`, where
`W_K = w W_I w⁻¹` and some cut set survives, is exact strictly before
`|S| - |I|`. -/
theorem range_eq_ker_of_survives
    (hconj : ∀ a, a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I)
    {s₀ : Finset ι} (hs₀ : Survives cs I K w s₀)
    (C : S.BooleanContraction U (Survives cs I K w) X)
    (k : ℕ) (hk : k + 1 < Fintype.card ι - I.card) :
    LinearMap.range ((S.quotientDiagram U).degreeDifferential k) =
      LinearMap.ker ((S.quotientDiagram U).degreeDifferential (k + 1)) := by
  have hR := right_length_lt_of_isMinimal cs hs₀.2
  have hSurv := BooleanInterval.survivor_iff_active cs (K := K) hR
  have hact := (hSurv s₀).mp hs₀
  exact C.range_eq_ker hSurv (hact.1.trans hact.2) k
    (lt_of_lt_of_le hk (card_le_terminal_of_survives cs hconj hs₀))

theorem injective_zero_of_survives
    (hconj : ∀ a, a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I)
    {s₀ : Finset ι} (hs₀ : Survives cs I K w s₀)
    (C : S.BooleanContraction U (Survives cs I K w) X)
    (hpos : 0 < Fintype.card ι - I.card) :
    Function.Injective ((S.quotientDiagram U).degreeDifferential 0) := by
  have hR := right_length_lt_of_isMinimal cs hs₀.2
  have hSurv := BooleanInterval.survivor_iff_active cs (K := K) hR
  have hact := (hSurv s₀).mp hs₀
  exact C.injective_zero hSurv (hact.1.trans hact.2)
    (lt_of_lt_of_le hpos (card_le_terminal_of_survives cs hconj hs₀))

end Survivors

end Diagram.Subdiagram

end Langlands.Aubert.CutComplex
