import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleUniverses
import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleAssembly

/-!
# Rank bounds for a supercuspidal seed in a selected centered segment

The argument uses actual induction equivalences and component certificates.
It assumes no L-factor formula or classification existence statement.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial

universe uG uX uY uF uV uW uV₀

section Component

variable {G : Type uG} [Group G]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- An irreducible component of an irreducible representation is equivalent
to that representation, with independent carrier universes. -/
theorem IsIrreducibleComponent.nonempty_equiv
    {ξ : Representation ℂ G X} {π : Representation ℂ G Y}
    (hc : IsIrreducibleComponent ξ π)
    (hξ : Representation.IsIrreducible ξ) : Nonempty (ξ.Equiv π) := by
  classical
  obtain ⟨hπ, U, f, hf⟩ := hc
  let := hξ
  let := hπ
  have : Nontrivial Y := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  have hU : U ≠ ⊥ := by
    intro hU
    subst U
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨x, hx⟩ := hf y
    have hx0 : x = 0 := Subtype.ext x.property
    apply hy
    rw [← hx, hx0, map_zero]
  have htop : U = ⊤ := (eq_bot_or_eq_top U).resolve_left hU
  subst U
  let q : ξ.IntertwiningMap π :=
    { toLinearMap :=
        { toFun := fun x => f ⟨x, trivial⟩
          map_add' := fun x y => f.map_add ⟨x, trivial⟩ ⟨y, trivial⟩
          map_smul' := fun c x => f.map_smul c ⟨x, trivial⟩ }
      isIntertwining' := fun g => by
        ext x
        exact DFunLike.congr_fun (f.isIntertwining' g) ⟨x, trivial⟩ }
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨x, hx⟩
  have hq0 : q ≠ 0 := by
    intro hq0
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨x, hx⟩ := hq y
    apply hy
    rw [← hx, hq0]
    rfl
  exact ⟨Representation.IntertwiningMap.ofBijective q
    ⟨(Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0, hq⟩⟩

end Component

section Combinatorics

/-- A selected block bounds the rank of a seed of one of its centered
segments. Equality with the ambient rank forces both lengths to be one. -/
theorem selectedCenteredSegment_rank_arithmetic {n : ℕ} (B : BlockShape n)
    (i : Fin B.length) {a d : ℕ}
    (hr : ∑ _j : Fin (d + 1), (a + 1) = B.size i) :
    a + 1 ≤ n ∧ (a + 1 = n → B.length = 1 ∧ d = 0) := by
  classical
  have hr' : (d + 1) * (a + 1) = B.size i := by simpa using hr
  have hseed : a + 1 ≤ B.size i := by nlinarith
  have hblock : B.size i ≤ n := by
    calc
      B.size i ≤ ∑ j, B.size j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (B.size j)) (Finset.mem_univ i)
      _ = n := B.sum_eq
  refine ⟨hseed.trans hblock, ?_⟩
  intro heq
  have hsize : B.size i = n := by omega
  have hd : d = 0 := by nlinarith
  have hevery : ∀ j : Fin B.length, j = i := by
    intro j
    by_contra hji
    have hpair : B.size i + B.size j ≤ n := by
      calc
        B.size i + B.size j = ∑ t ∈ ({i, j} : Finset (Fin B.length)), B.size t := by
          simp [Ne.symm hji]
        _ ≤ ∑ t, B.size t := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = n := B.sum_eq
    have hj := B.positive j
    omega
  have : Subsingleton (Fin B.length) :=
    ⟨fun j k => (hevery j).trans (hevery k).symm⟩
  have hlen : B.length ≤ 1 := by
    simpa using Fintype.card_le_one_iff_subsingleton.mpr
      (inferInstance : Subsingleton (Fin B.length))
  exact ⟨by have hi := i.isLt; omega, hd⟩

end Combinatorics

variable {p : ℕ} [Fact p.Prime]

/-- The two rank requirements for a supercuspidal pole partner of rank
`a + 1`; this proposition asserts no partner or polynomial existence. -/
def SupercuspidalPoleRankBounds (F : PadicField.{uF} p)
    {k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear k F.Carrier) V) (a : ℕ) : Prop :=
  a + 1 ≤ k ∧
    (¬ (letI := F.canonicalTopologicalData.topology; IsSupercuspidal τ) → a + 1 < k)

section Rank

variable (F : PadicField.{uF} p)

local instance poleRankTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- A centered segment of length one is equivalent to its smooth seed. -/
def centeredSegment_zero_equiv {a : ℕ}
    {V₀ : Type uV₀} [AddCommGroup V₀] [Module ℂ V₀]
    (π₀ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) V₀)
    (hsm : IsSmooth π₀) :
    (F.canonicalNormalizedProductInduced
      (succBlockShape (fun _ : Fin 1 => a)
        (show ∑ _ : Fin 1, (a + 1) = a + 1 by simp))
      (centeredSegmentBlocks F 0 π₀)).Equiv π₀ := by
  have hz : centeredSegmentBlocks F 0 π₀ = fun _ : Fin 1 => π₀ := by
    funext i
    have hi : (i : ℕ) = 0 := by omega
    simp only [centeredSegmentBlocks, Nat.cast_zero, hi, zero_div, sub_zero,
      realPowerTwist_zero]
  rw [hz]
  exact succSingleBlockNormalizedProductEquiv F (fun _ => a) (fun _ => π₀) (fun _ => hsm)

/-- A seed in a selected centered-segment component satisfies both target
rank bounds. If its rank is the full rank, the actual equivalences identify
the source with the supercuspidal seed. -/
theorem selectedCenteredSegment_rankBounds
    {k l : ℕ} (m : Fin l → ℕ) (hm : ∑ i, (m i + 1) = k + 1)
    {W : Fin l → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hsmσ : ∀ i, IsSmooth (σ i))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (k + 1) F.Carrier) V)
    (he : Nonempty ((F.canonicalNormalizedProductInduced (succBlockShape m hm) σ).Equiv τ))
    (i : Fin l) {a d : ℕ}
    (hr : ∑ _j : Fin (d + 1), (a + 1) = m i + 1)
    {V₀ : Type uV₀} [AddCommGroup V₀] [Module ℂ V₀]
    (π₀ : Representation ℂ (GeneralLinear (a + 1) F.Carrier) V₀)
    (hiπ₀ : Representation.IsIrreducible π₀) (hsπ₀ : IsSupercuspidal π₀)
    (hc : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F d π₀)) (σ i)) :
    SupercuspidalPoleRankBounds F τ a := by
  obtain ⟨hle, heq⟩ := selectedCenteredSegment_rank_arithmetic (succBlockShape m hm) i hr
  refine ⟨hle, fun hnot => lt_of_le_of_ne hle ?_⟩
  intro hsame
  have ha : a + 1 = k + 1 := hsame
  obtain ⟨hl, hd⟩ := heq ha
  change l = 1 at hl
  subst l
  have hi : i = 0 := Fin.eq_zero i
  subst i
  subst d
  have hak : a = k := by omega
  subst a
  have hmk : m 0 = k := by simpa using hm
  subst k
  obtain ⟨e⟩ := he
  let eσ := succSingleBlockNormalizedProductEquiv F m σ hsmσ
  let e₀ := centeredSegment_zero_equiv F π₀ hsπ₀.1.1
  have hirr : Representation.IsIrreducible
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => m 0) hr)
        (centeredSegmentBlocks F 0 π₀)) :=
    (Langlands.isIrreducible_iff_of_equiv e₀).mpr hiπ₀
  obtain ⟨ec⟩ := hc.nonempty_equiv hirr
  apply hnot
  exact isSupercuspidal_of_equiv (e₀.symm.trans (ec.trans (eσ.symm.trans e))) hsπ₀

end Rank

end Langlands.RankinSelberg
