import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.Representation.Hecke.DoubleCoset
import Langlands.Representation.Character.ModularContragredientProof
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Representation.Jacquet.IwahoriCellVolume
import Langlands.Representation.Plancherel.CompactIntertwiningCompression

/-!
# The twisted trace of a compact double-coset indicator

For a compact open subgroup `I` and an element `t`, the integrated action of
the indicator of `I t I` on an `I`-fixed vector is a finite sum over the cosets
of `I ∩ t I t⁻¹` in `I`, and hence a scalar multiple of the compression
`e_I ρ(t)`.  Consequently the twisted trace of the indicator is that scalar
times the trace of the compression followed by the twist on the `I`-fixed
vectors.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Hecke.TestFunction
open scoped Pointwise

universe uG uV

section ConjIntersection

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The subgroup `I ∩ t I t⁻¹` of `I`: the elements `k` of `I` with `t⁻¹ k t ∈ I`. -/
def conjIntersectionSubgroup (I : OpenSubgroup G) (t : G) : Subgroup I where
  carrier := {k | t⁻¹ * (k : G) * t ∈ I}
  mul_mem' {a b} ha hb := by
    change t⁻¹ * ((a : G) * b) * t ∈ I
    have e : t⁻¹ * ((a : G) * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
    rw [e]
    exact I.mul_mem ha hb
  one_mem' := by
    change t⁻¹ * (1 : G) * t ∈ I
    rw [mul_one, inv_mul_cancel]
    exact I.one_mem
  inv_mem' {a} ha := by
    change t⁻¹ * ((a : G)⁻¹) * t ∈ I
    have e : t⁻¹ * ((a : G)⁻¹) * t = (t⁻¹ * a * t)⁻¹ := by group
    rw [e]
    exact I.inv_mem ha

omit [IsTopologicalGroup G] in
theorem mem_conjIntersectionSubgroup {I : OpenSubgroup G} {t : G} (k : I) :
    k ∈ conjIntersectionSubgroup I t ↔ t⁻¹ * (k : G) * t ∈ I := Iff.rfl

/-- The cosets of `I ∩ t I t⁻¹` in a compact open `I` are finite in number. -/
theorem finite_quotient_conjIntersectionSubgroup (I : OpenSubgroup G)
    (hI : IsCompact (I : Set G)) (t : G) : Finite (I ⧸ conjIntersectionSubgroup I t) := by
  let H := I.toSubgroup
  have : CompactSpace H := isCompact_iff_compactSpace.mp hI
  have hopen : IsOpen ((fun x : G => t⁻¹ * x * t) ⁻¹' (I : Set G)) :=
    I.isOpen.preimage (by fun_prop)
  exact Subgroup.quotient_finite_of_isOpen (G := H) (conjIntersectionSubgroup I t)
    (hopen.preimage continuous_subtype_val)

end ConjIntersection

section IwahoriIndex

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Under an Iwahori factorization of `K` adapted to `g`, the cosets of
`K ∩ g K g⁻¹` in `K` are represented by the upper radical part of `K`, and their
number is the Iwahori index `[K ∩ N : g (K ∩ N) g⁻¹]`. -/
theorem natCard_quotient_conjIntersectionSubgroup [IsTopologicalGroup G]
    {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (h : Jacquet.IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N) :
    Nat.card (K ⧸ conjIntersectionSubgroup K g) = Jacquet.iwahoriIndex K N g := by
  classical
  have hgN : g ∈ Subgroup.normalizer (N : Set G) := hMN h.mem_levi
  let U := K.toSubgroup ⊓ N
  let H := (Jacquet.conjRadicalPiece K N g).subgroupOf U
  -- Two upper elements have the same `K ∩ g K g⁻¹`-coset exactly when they have
  -- the same `g (K ∩ N) g⁻¹`-coset.
  have hrel : ∀ a b : U, (a : G)⁻¹ * b ∈ Jacquet.conjRadicalPiece K N g ↔
      g⁻¹ * ((a : G)⁻¹ * b) * g ∈ K := fun a b =>
    Jacquet.mem_conjRadicalPiece_iff_of_mem hgN (N.mul_mem (N.inv_mem a.2.2) b.2.2)
  let toK : U → K := fun u => ⟨u, u.2.1⟩
  let F : U ⧸ H → K ⧸ conjIntersectionSubgroup K g :=
    Quotient.lift (fun u => (QuotientGroup.mk (toK u) : K ⧸ conjIntersectionSubgroup K g)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at hab'
      change g⁻¹ * ((a : G)⁻¹ * b) * g ∈ K
      exact (hrel a b).mp (by simpa using hab'))
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          apply QuotientGroup.eq.mpr
          have hab : (toK a)⁻¹ * toK b ∈ conjIntersectionSubgroup K g := QuotientGroup.eq.mp hxy
          rw [Subgroup.mem_subgroupOf]
          have := (hrel a b).mpr hab
          simpa using this
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor (k : G)⁻¹ (K.inv_mem k.2)
        refine ⟨QuotientGroup.mk (⟨u⁻¹, U.inv_mem hu⟩ : U), ?_⟩
        change (QuotientGroup.mk (toK ⟨u⁻¹, U.inv_mem hu⟩) : K ⧸ conjIntersectionSubgroup K g) =
          QuotientGroup.mk k
        apply QuotientGroup.eq.mpr
        change g⁻¹ * ((u⁻¹)⁻¹ * (k : G)) * g ∈ K
        have hk : (k : G) = u⁻¹ * m⁻¹ * l⁻¹ := by
          rw [← inv_inv (k : G), hprod]
          group
        have e : g⁻¹ * ((u⁻¹)⁻¹ * (k : G)) * g = (g⁻¹ * m⁻¹ * g) * (g⁻¹ * l⁻¹ * g) := by
          rw [hk]
          group
        rw [e]
        exact K.mul_mem (h.levi _ ((K.toSubgroup ⊓ M).inv_mem hm)).1
          (h.lower _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)).1
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  rfl

end IwahoriIndex

section DoubleCoset

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On an `I`-fixed vector the integrated indicator of `I t I` is the sum over the
cosets `k (I ∩ t I t⁻¹)` of `I` of `ρ(k t) v`, times the mass of `I`. -/
theorem integratedAction_doubleCosetIndicator_of_mem_fixedVectors (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (I : OpenSubgroup G) (hI : IsCompact (I : Set G)) (t : G)
    [Fintype (I ⧸ conjIntersectionSubgroup I t)]
    {v : V} (hv : v ∈ fixedVectors ρ I.toSubgroup) :
    Hecke.integratedAction μ ρ hρ (doubleCosetIndicator I hI t) v =
      ((μ (I : Set G)).toReal : ℂ) •
        ∑ q : I ⧸ conjIntersectionSubgroup I t, ρ (((q.out : I) : G) * t) v := by
  classical
  let rep : I ⧸ conjIntersectionSubgroup I t → G := fun q => ((q.out : I) : G) * t
  let s : I ⧸ conjIntersectionSubgroup I t → Set G := fun q => rep q • (I : Set G)
  have hmem_s : ∀ q x, x ∈ s q ↔ (rep q)⁻¹ * x ∈ I := fun q x => by
    simp only [s, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
  have hfix : ∀ q x, x ∈ s q → ρ x v = ρ (rep q) v := by
    intro q x hx
    have hk := (hmem_s q x).mp hx
    calc ρ x v = ρ (rep q) (ρ ((rep q)⁻¹ * x) v) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ (rep q) v := by rw [show ρ ((rep q)⁻¹ * x) v = v from hv ⟨_, hk⟩]
  have hsub : ∀ q x, x ∈ s q → x ∈ doubleCosetSet I t := by
    intro q x hx
    have hk := (hmem_s q x).mp hx
    rw [mem_doubleCosetSet]
    refine ⟨q.out, (q.out).property, (rep q)⁻¹ * x, hk, ?_⟩
    simp only [rep]
    group
  have hunique : ∀ (a : G) (ha : a ∈ I) (b : G), b ∈ I → ∀ q,
      a * t * b ∈ s q ↔ q = QuotientGroup.mk (⟨a, ha⟩ : I) := by
    intro a ha b hb q
    rw [hmem_s]
    have e : (rep q)⁻¹ * (a * t * b) = (t⁻¹ * (((q.out : I) : G)⁻¹ * a) * t) * b := by
      simp only [rep]
      group
    rw [e]
    change _ ∈ I.toSubgroup ↔ _
    rw [I.toSubgroup.mul_mem_cancel_right hb]
    have hq : q = QuotientGroup.mk (⟨a, ha⟩ : I) ↔
        (q.out)⁻¹ * (⟨a, ha⟩ : I) ∈ conjIntersectionSubgroup I t := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq
    rw [hq, mem_conjIntersectionSubgroup]
    rfl
  have hpres : ∀ x, doubleCosetIndicator I hI t x • ρ x v =
      ∑ q, (s q).indicator (fun _ => ρ (rep q) v) x := by
    intro x
    rw [doubleCosetIndicator_apply]
    by_cases hx : x ∈ doubleCosetSet I t
    · rw [Set.indicator_of_mem hx, one_smul]
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCosetSet I t x).mp hx
      have h0 := (hunique a ha b hb (QuotientGroup.mk (⟨a, ha⟩ : I))).mpr rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk (⟨a, ha⟩ : I))]
      · rw [Set.indicator_of_mem h0]
        exact hfix _ _ h0
      · intro q _ hq
        exact Set.indicator_of_notMem (fun h => hq ((hunique a ha b hb q).mp h)) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Set.indicator_of_notMem hx, zero_smul]
      symm
      apply Finset.sum_eq_zero
      intro q _
      exact Set.indicator_of_notMem (fun h => hx (hsub q x h)) _
  rw [Hecke.integratedAction_eq_sum_of_presentation μ ρ hρ _ v Finset.univ s
      (fun q => ρ (rep q) v) (fun q _ => (I.isOpen.smul (rep q)).measurableSet)
      (fun q _ _ => (hI.smul (rep q)).measure_lt_top) hpres, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [s, rep, measure_smul]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The average over `I` of `ρ(t) v`, for `v` fixed by `I`, is the mean over the
cosets of `I ∩ t I t⁻¹` in `I`. -/
theorem averageMap_rho_eq_sum (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (I : OpenSubgroup G) (hI : IsCompact (I : Set G)) (t : G)
    [Fintype (I ⧸ conjIntersectionSubgroup I t)]
    {v : V} (hv : v ∈ fixedVectors ρ I.toSubgroup) :
    Compact.averageMap ρ hρ I hI (ρ t v) =
      (Fintype.card (I ⧸ conjIntersectionSubgroup I t) : ℂ)⁻¹ •
        ∑ q : I ⧸ conjIntersectionSubgroup I t, ρ (((q.out : I) : G) * t) v := by
  rw [Plancherel.averageMap_eq_finiteMean_cosets ρ hρ I hI (conjIntersectionSubgroup I t) (ρ t v)]
  · simp only [Compact.finiteMean, map_mul, Module.End.mul_apply]
  · intro l
    have hl : t⁻¹ * ((l : I) : G) * t ∈ I := l.property
    calc ρ ((l : I) : G) (ρ t v) = ρ t (ρ (t⁻¹ * ((l : I) : G) * t) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 1
          group
      _ = ρ t v := by rw [show ρ (t⁻¹ * ((l : I) : G) * t) v = v from hv ⟨_, hl⟩]

/-- On an `I`-fixed vector the integrated indicator of `I t I` is the mass of `I`
times the number of cosets of `I ∩ t I t⁻¹` in `I`, times the compression
`e_I ρ(t)`. -/
theorem integratedAction_doubleCosetIndicator_eq_smul_averageMap (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (I : OpenSubgroup G) (hI : IsCompact (I : Set G)) (t : G)
    [Fintype (I ⧸ conjIntersectionSubgroup I t)]
    {v : V} (hv : v ∈ fixedVectors ρ I.toSubgroup) :
    Hecke.integratedAction μ ρ hρ (doubleCosetIndicator I hI t) v =
      (((μ (I : Set G)).toReal : ℂ) * Fintype.card (I ⧸ conjIntersectionSubgroup I t)) •
        Compact.averageMap ρ hρ I hI (ρ t v) := by
  rw [integratedAction_doubleCosetIndicator_of_mem_fixedVectors μ ρ hρ I hI t hv,
    averageMap_rho_eq_sum ρ hρ I hI t hv, smul_smul, mul_assoc]
  have hcard : (Fintype.card (I ⧸ conjIntersectionSubgroup I t) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_inv_cancel₀ hcard, mul_one]

variable [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The integrated indicator of `I t I` factors through the average over `I`. -/
theorem integratedAction_doubleCosetIndicator_averageMap (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (I : OpenSubgroup G) (hI : IsCompact (I : Set G)) (t : G) (v : V) :
    Hecke.integratedAction μ ρ hρ (doubleCosetIndicator I hI t)
        (Compact.averageMap ρ hρ I hI v) =
      Hecke.integratedAction μ ρ hρ (doubleCosetIndicator I hI t) v := by
  apply Jacquet.map_averageMap_of_forall_eq ρ hρ I hI
  intro k
  rw [Character.integratedAction_right_input_modular μ ρ hρ k.val]
  have hk : (k.val)⁻¹ ∈ I.toSubgroup := I.inv_mem k.property
  have hmod : Distribution.renardModular ((k.val)⁻¹) = 1 :=
    (Distribution.RenardModular.regularity G).2.2.2 I.toSubgroup hI _ hk
  have hf : rightTranslate (k.val)⁻¹ (doubleCosetIndicator I hI t) =
      doubleCosetIndicator I hI t := by
    ext x
    rw [rightTranslate_apply]
    exact (doubleCosetIndicator_mem I hI t).2 ⟨(k.val)⁻¹, hk⟩ x
  rw [hmod, hf]
  simp

/-- The twisted trace of the indicator of `I t I`, for an endomorphism `A`
preserving the `I`-fixed vectors, is the mass of `I` times the number of cosets
of `I ∩ t I t⁻¹` in `I`, times the trace on the `I`-fixed vectors of the
compression `e_I ρ(t)` followed by `A`. -/
theorem twistedDistribution_doubleCosetIndicator (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (I : OpenSubgroup G) (hI : IsCompact (I : Set G)) (t : G)
    [Fintype (I ⧸ conjIntersectionSubgroup I t)]
    (A : Module.End ℂ V)
    (hA : ∀ w ∈ fixedVectors ρ I.toSubgroup, A w ∈ fixedVectors ρ I.toSubgroup) :
    twistedDistribution μ ρ hρ A (doubleCosetIndicator I hI t) =
      (((μ (I : Set G)).toReal : ℂ) * Fintype.card (I ⧸ conjIntersectionSubgroup I t)) *
        LinearMap.trace ℂ (fixedVectors ρ I.toSubgroup)
          (A.restrict hA * Jacquet.compressedAction ρ hρ.1 I hI t) := by
  have : FiniteDimensional ℂ (fixedVectors ρ I.toSubgroup) := hρ.2 I
  set c : ℂ := ((μ (I : Set G)).toReal : ℂ) * Fintype.card (I ⧸ conjIntersectionSubgroup I t)
    with hc
  let P : V →ₗ[ℂ] fixedVectors ρ I.toSubgroup :=
    (Compact.averageMap ρ hρ.1 I hI).codRestrict _
      (Compact.averageMap_mem_fixedVectors ρ hρ.1 I hI)
  let gmap : fixedVectors ρ I.toSubgroup →ₗ[ℂ] V :=
    c • ((fixedVectors ρ I.toSubgroup).subtype ∘ₗ Jacquet.compressedAction ρ hρ.1 I hI t)
  rw [twistedDistribution_apply,
    FiniteRankEnd.trace_eq_of_factorization _ (P ∘ₗ A) gmap ?_]
  · have hcomp : (P ∘ₗ A) ∘ₗ gmap =
        c • (A.restrict hA * Jacquet.compressedAction ρ hρ.1 I hI t) := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      have hmem : A (Compact.averageMap ρ hρ.1 I hI (ρ t (w : V))) ∈
          fixedVectors ρ I.toSubgroup :=
        hA _ (Compact.averageMap_mem_fixedVectors ρ hρ.1 I hI _)
      change Compact.averageMap ρ hρ.1 I hI
          (A (c • Compact.averageMap ρ hρ.1 I hI (ρ t (w : V)))) =
        c • A (Compact.averageMap ρ hρ.1 I hI (ρ t (w : V)))
      rw [map_smul, map_smul, Compact.averageMap_id ρ hρ.1 I hI _ hmem]
    rw [hcomp, map_smul, smul_eq_mul]
  · apply LinearMap.ext
    intro x
    change Hecke.integratedAction μ ρ hρ.1 (doubleCosetIndicator I hI t) (A x) =
      c • Compact.averageMap ρ hρ.1 I hI
        (ρ t (Compact.averageMap ρ hρ.1 I hI (A x)))
    rw [← integratedAction_doubleCosetIndicator_averageMap μ ρ hρ.1 I hI t (A x)]
    exact integratedAction_doubleCosetIndicator_eq_smul_averageMap μ ρ hρ.1 I hI t
      (Compact.averageMap_mem_fixedVectors ρ hρ.1 I hI (A x))

end DoubleCoset

end Langlands.BaseChange
