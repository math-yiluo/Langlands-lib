import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.Absolute.Borel
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Filter.Cofinite

/-! # An almost-everywhere integral Iwasawa family on actual local points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.IntegralIwasawaFamily

variable (F : Type u) [Field F] [NumberField F]
  (G P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)

local instance localPointsTopology (v : FinitePlace F) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F (FiniteCompletion F v))

/-- The local compact, covering, adelic absorption and uniform integrality
conditions for a single family chosen before its adelic points and regular functions. -/
def IsIntegralIwasawaFamily
    (K : ∀ v : FinitePlace F,
      Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) : Prop :=
  (∀ᶠ v in cofinite,
    IsCompact (K v : Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) ∧
      (∀ L : Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))),
        IsCompact (L : Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) →
          K v ≤ L → L = K v) ∧
      Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) *
        (K v : Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)))) =
          Set.univ) ∧
  (∀ x : FiniteAdelicGroupPoints F G, ∀ᶠ v in cofinite,
    G.affinePointMap
      (CommAlgCat.ofHom
        ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
           commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x ∈ K v) ∧
  (∀ a : Γ(G.X.left, ⊤), ∀ᶠ v in cofinite,
    ∀ k : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)), k ∈ K v →
      G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) k a ∈
        v.adicCompletionIntegers F)

/-- The unproved existence target derived from good reductive/parabolic models.
No integral model, compact family or local covering is supplied as a premise. -/
def ExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    Langlands.GroupScheme.IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      Langlands.GroupScheme.IsParabolicSubgroup p →
      ∃ K : ∀ v : FinitePlace F,
          Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))),
        IsIntegralIwasawaFamily F G P p K

end Langlands.Global.IntegralIwasawaFamily
