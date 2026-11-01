import Langlands.Representation.GodementJacquet.Zeta

/-!
# Bi-smooth coefficient inclusion for actual subquotients

The general statement uses compact-open cofinality and smoothness of the
ambient representation. The p-adic specialization uses the canonical topology.
These are statements, with no coefficient-inclusion proof in this module.
-/

namespace Langlands.GodementJacquet

universe uG uF uV uW

/-- Every actual subquotient of a smooth complex representation has its
bi-smooth coefficient space contained in that of the ambient representation. -/
def SubquotientCoefficientInclusionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth σ →
      ∀ (A : Subrepresentation σ)
        (q : A.toRepresentation.IntertwiningMap τ),
        Function.Surjective q →
          biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ

namespace Padic

/-- The canonical p-adic general-linear specialization, with no extra
compact-open, admissibility, irreducibility, or target-smoothness premise. -/
def SubquotientCoefficientInclusionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
    ∀ (n : ℕ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth σ →
      ∀ (A : Subrepresentation σ)
        (q : A.toRepresentation.IntertwiningMap τ),
        Function.Surjective q →
          biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ

end Padic

end Langlands.GodementJacquet
