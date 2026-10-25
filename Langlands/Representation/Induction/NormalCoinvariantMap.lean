import Langlands.Representation.Induction.NormalCoinvariantStatement
import Langlands.Representation.Induction.CompactQuotientProof

noncomputable section

namespace Langlands.Induction

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable (σ : Representation ℂ H V)

include hNH in
private theorem quotientPostcompose_invariant (n : N) :
    (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap ∘ₗ
        (compactInduced H σ).comp N.subtype n =
      (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap := by
  ext f x
  change Representation.Coinvariants.mk _ (eval H σ f.val (x * (n : G))) =
    Representation.Coinvariants.mk _ (eval H σ f.val x)
  have hn : x * (n : G) * x⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem inferInstance n.val n.property x
  let p : N.subgroupOf H := ⟨⟨x * (n : G) * x⁻¹, hNH hn⟩, hn⟩
  have he : x * (n : G) = ((p.val : H) : G) * x := by
    dsimp [p]
    group
  rw [he, eval_covariant H σ f.val p.val x]
  exact Representation.Coinvariants.mk_self_apply
    (σ.comp (N.subgroupOf H).subtype) p (eval H σ f.val x)

/-- The canonical map from induced normal coinvariants to induction of coefficient coinvariants. -/
def compactNormalCoinvariantsMap :
    ((compactInduced H σ).toCoinvariants N).IntertwiningMap
      (compactInduced H (σ.toCoinvariants (N.subgroupOf H))) where
  toLinearMap := Representation.Coinvariants.lift _
    (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap
    (quotientPostcompose_invariant H N hNH σ)
  isIntertwining' g := by
    apply Representation.Coinvariants.hom_ext
    ext f x
    rfl

theorem compactNormalCoinvariantsMap_mk (f : CompactFunctions H σ) :
    compactNormalCoinvariantsMap H N hNH σ
      (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f) =
        compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H)) f := rfl

theorem compactNormalCoinvariantsMap_eval (f : CompactFunctions H σ) (g : G) :
    eval H (σ.toCoinvariants (N.subgroupOf H))
      (compactNormalCoinvariantsMap H N hNH σ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f)).val g =
      Representation.Coinvariants.mk (σ.comp (N.subgroupOf H).subtype)
        (eval H σ f.val g) := rfl

theorem compactNormalCoinvariantsMap_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ H W) (T : σ.IntertwiningMap τ)
    (q : Representation.Coinvariants ((compactInduced H σ).comp N.subtype)) :
    compactNormalCoinvariantsMap H N hNH τ
      (Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (compactInducedMap H T) N) q) =
      compactInducedMap H (normalCoinvariantsMap (N.subgroupOf H) T)
        (compactNormalCoinvariantsMap H N hNH σ q) := by
  induction q using Representation.Coinvariants.induction_on with
  | h f => rfl

end Langlands.Induction
