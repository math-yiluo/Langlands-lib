import Langlands.GroupScheme.CentralIsogeny.TorusLift
import Langlands.AbelianScheme.IsogenyStability

/-! # Composition of closed-torus lifting up to isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Every closed target torus has a closed source torus mapping isogenously
onto it through the given homomorphism. -/
def LiftsClosedToriUpToIsogeny (φ : G ⟶ H) : Prop :=
  ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H),
    IsTorus S.toGrp → IsClosedSubgroup i →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
        (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ S.toGrp),
        IsTorus T.toGrp ∧ IsClosedSubgroup j ∧ IsIsogeny f ∧ j ≫ φ = f ≫ i

/-- The identity lifts each closed torus by itself. -/
theorem liftsClosedToriUpToIsogeny_id (G : GroupScheme (Spec (CommRingCat.of k))) :
    LiftsClosedToriUpToIsogeny (𝟙 G) := by
  intro S i hS hi
  exact ⟨S, i, 𝟙 S.toGrp, hS, hi, isIsogeny_id S.toGrp, by simp⟩

/-- Successive torus lifts compose; no centrality of the composite is needed. -/
theorem LiftsClosedToriUpToIsogeny.comp {φ : G ⟶ H} {ψ : H ⟶ K}
    (hφ : LiftsClosedToriUpToIsogeny φ) (hψ : LiftsClosedToriUpToIsogeny ψ) :
    LiftsClosedToriUpToIsogeny (φ ≫ ψ) := by
  intro S i hS hi
  obtain ⟨U, j, f, hU, hj, hf, hcommψ⟩ := hψ S i hS hi
  obtain ⟨T, l, g, hT, hl, hg, hcommφ⟩ := hφ U j hU hj
  refine ⟨T, l, g ≫ f, hT, hl, hg.comp hf, ?_⟩
  rw [← Category.assoc, hcommφ, Category.assoc, hcommψ, ← Category.assoc]

/-- Every affine-source central isogeny has the closed-torus lifting property. -/
theorem IsCentralIsogeny.liftsClosedToriUpToIsogeny
    [IsAffineHom G.X.hom] {φ : G ⟶ H} (hφ : IsCentralIsogeny φ) :
    LiftsClosedToriUpToIsogeny φ :=
  hφ.exists_isogeny_torus_lift

/-- Closed-torus lifting up to isogeny contains identities, is stable under
composition, and holds for affine-source central isogenies. -/
def TorusIsogenyLiftStabilityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H K : GroupScheme (Spec (CommRingCat.of k))),
    LiftsClosedToriUpToIsogeny (𝟙 G) ∧
      (∀ (φ : G ⟶ H) (ψ : H ⟶ K),
        LiftsClosedToriUpToIsogeny φ → LiftsClosedToriUpToIsogeny ψ →
          LiftsClosedToriUpToIsogeny (φ ≫ ψ)) ∧
      (∀ [IsAffineHom G.X.hom] (φ : G ⟶ H),
        IsCentralIsogeny φ → LiftsClosedToriUpToIsogeny φ)

theorem torusIsogenyLiftStabilityStatement : TorusIsogenyLiftStabilityStatement.{u} := by
  intro k _ G H K
  refine ⟨liftsClosedToriUpToIsogeny_id G, fun _ _ hφ hψ => hφ.comp hψ, ?_⟩
  intro _ φ hφ
  exact hφ.liftsClosedToriUpToIsogeny

end Langlands.GroupScheme
