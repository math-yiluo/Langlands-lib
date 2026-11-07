import Langlands.Representation.Smooth.Definitions
import Langlands.Topology.LocallyProfinite
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic

/-!
# Renard VI.8.6: endomorphisms of an admissible family with irreducible fibers

A family over `B` is a `B`-linear representation `ρ : Representation B G V`, as in
`Langlands.Renard.AlgebraicFamily.Statements`. A set `Ξ` of points `B →ₐ[ℂ] ℂ` is
Zariski dense when every element of `B` vanishing at all points of `Ξ` vanishes at
every point.
-/

open TensorProduct Langlands.Topology

namespace Langlands.Renard.AlgebraicFamily

/-- VI.8.6 Proposition: let `V` be an admissible `(G, B)`-module, `φ` an endomorphism
of `(G, B)`-modules of `V`, and `Ξ` a Zariski-dense set of points `χ : B →ₐ[ℂ] ℂ`. If
the specialization `ℂ ⊗[B] V` at every point of `Ξ` is irreducible, then `φ` is the
action of some `b : B`. -/
def EndomorphismScalarStatement.{uB, uG, uV} : Prop :=
  ∀ (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
    [Algebra.FiniteType ℂ B] [IsReduced B]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ (V : Type uV) [AddCommGroup V] [Module B V] (ρ : Representation B G V),
        IsSmooth ρ → Module.Flat B V →
          (∀ K : OpenSubgroup G, IsCompact (K : Set G) →
            Module.Finite B (fixedVectors ρ K.toSubgroup)) →
            ∀ φ : V →ₗ[B] V, (∀ (g : G) (v : V), φ (ρ g v) = ρ g (φ v)) →
              ∀ Ξ : Set (B →ₐ[ℂ] ℂ),
                (∀ b : B, (∀ χ ∈ Ξ, χ b = 0) → ∀ χ : B →ₐ[ℂ] ℂ, χ b = 0) →
                  (∀ χ ∈ Ξ,
                    letI : Algebra B ℂ := χ.toRingHom.toAlgebra
                    Representation.IsIrreducible
                      ((Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ)) →
                    ∃ b : B, ∀ v : V, φ v = b • v

end Langlands.Renard.AlgebraicFamily
