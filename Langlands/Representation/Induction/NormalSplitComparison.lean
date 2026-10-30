import Langlands.Representation.Induction.NormalCoinvariantProof
import Langlands.Representation.Induction.SplitQuotientProof

/-! Canonical normal coinvariants followed by restriction to a split quotient. -/

noncomputable section

namespace Langlands.Induction

universe uG uL uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)

include hBasis in
private theorem compactNormalMap_bijective (H N : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hN : IsClosed (N : Set G)) (hNH : N ≤ H)
    (σ : Representation ℂ H V) (hσ : IsSmooth σ) :
    Function.Bijective (compactNormalCoinvariantsMap H N hNH σ) := by
  obtain ⟨e, he, _⟩ := compactInductionNormalCoinvariants G hBasis H N hH hN hNH
  let A := Langlands.SmoothRep.of σ hσ
  have hEq : (compactNormalCoinvariantsMap H N hNH σ : _ → _) = e A := by
    funext q
    induction q using Representation.Coinvariants.induction_on with
    | h f =>
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact (he A f x).symm
  rw [hEq]
  exact (e A).bijective

/-- The canonical pointwise normal-coinvariant map, made into an equivalence
using the published compact-induction normal-coinvariant theorem. -/
def compactNormalCanonicalEquiv (H N : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hN : IsClosed (N : Set G)) (hNH : N ≤ H)
    (σ : Representation ℂ H V) (hσ : IsSmooth σ) :
    Representation.Equiv ((compactInduced H σ).toCoinvariants N)
      (compactInduced H (σ.toCoinvariants (N.subgroupOf H))) :=
  (compactNormalCoinvariantsMap H N hNH σ).ofBijective
    (compactNormalMap_bijective hBasis H N hH hN hNH σ hσ)

@[simp] theorem compactNormalCanonicalEquiv_mk (H N : Subgroup G) [N.Normal]
    (hH : IsClosed (H : Set G)) (hN : IsClosed (N : Set G)) (hNH : N ≤ H)
    (σ : Representation ℂ H V) (hσ : IsSmooth σ) (f : CompactFunctions H σ) :
    compactNormalCanonicalEquiv hBasis H N hH hN hNH σ hσ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f) =
      compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H)) f := rfl

variable (r : G →* L) (s : L →* G) (hr : Continuous r) (hs : Continuous s)
variable (hrs : ∀ l, r (s l) = l) (H : Subgroup G)
variable (hH : IsClosed (H : Set G)) (hN : IsClosed (r.ker : Set G)) (hker : r.ker ≤ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
private theorem coinvariantKernel_trivial (h : H) (hh : r (h : G) = 1)
    (z : Representation.Coinvariants (σ.comp (r.ker.subgroupOf H).subtype)) :
    σ.toCoinvariants (r.ker.subgroupOf H) h z = z := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    let n : r.ker.subgroupOf H := ⟨h, MonoidHom.mem_ker.mpr hh⟩
    exact Representation.Coinvariants.mk_self_apply
      (σ.comp (r.ker.subgroupOf H).subtype) n v

/-- The actual normal-coinvariant comparison, restricted to the section,
is compact induction on the split quotient. -/
def normalSplitCompactEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (compactInduced (H.comap s)
        ((σ.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))) := by
  let e := compactNormalCanonicalEquiv hBasis H r.ker hH hN hker σ hσ
  let es : Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      ((compactInduced H (σ.toCoinvariants (r.ker.subgroupOf H))).comp s) :=
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' l := e.isIntertwining' (s l) }
  exact es.trans (splitQuotientEquiv r hr s hs hrs H hker
    (σ.toCoinvariants (r.ker.subgroupOf H)) (coinvariantKernel_trivial r H σ))

@[simp] theorem normalSplitCompactEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    eval (H.comap s)
      ((σ.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))
      (normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker σ hσ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      Representation.Coinvariants.mk (σ.comp (r.ker.subgroupOf H).subtype)
        (eval H σ f.val (s l)) := rfl

/-- Naturality in every coefficient intertwiner, with independent coefficient
universes, for the same canonical split comparison. -/
theorem normalSplitCompactEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker τ hτ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      compactInducedMap (H.comap s)
        (restrictAlongMap (s.subgroupComap H)
          (normalCoinvariantsMap (r.ker.subgroupOf H) T))
        (normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker σ hσ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h f =>
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext l
    rfl

end Langlands.Induction
