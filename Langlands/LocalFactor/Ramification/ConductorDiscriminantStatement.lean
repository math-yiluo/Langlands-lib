import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.LocalFactor.Ramification.ArtinExponent
import Langlands.LocalField.RelativeIntegers
import Langlands.Representation.Finite.BrauerStatement
import Mathlib.RingTheory.Discriminant

/-!
# The conductor–discriminant formula

For a finite Galois extension `M/K` of p-adic fields with group `G`, the discriminant of the
integers `O_M` over `O_K` is `m_K` to the power `[G:G_0] Σ_i (|G_i| − 1)`, and it is the product
of the conductors `m_K ^ a(χ)` of the irreducible characters `χ` of `G`, each to the power `χ(1)`.
Proposition definition only.
-/

universe uK uM uι uG

/-- A representative of an irreducible class of complex representations (`Quotient.out`). -/
noncomputable abbrev Langlands.FiniteRep.IrreducibleClass.out {G : Type uG} [Group G]
    (a : FiniteRep.IrreducibleClass G) : FDRep ℂ G :=
  Quotient.out (a.1 : Quotient (CategoryTheory.isIsomorphicSetoid (FDRep ℂ G)))

namespace Langlands.Ramification.Padic

open IsLocalRing PadicField.TopologicalData

/-- **The conductor–discriminant formula.** For a finite Galois extension `M/K` of p-adic fields
(with data `TK`, `TM`), `G = Gal(M/K)` with lower groups `G_i`, and every basis `b` of `O_M` over
`O_K`:

1. if `G_N = 1`, the discriminant ideal is `m_K ^ ([G:G_0] Σ_{i<N} (|G_i| − 1))`;
2. the discriminant ideal is `∏_χ 𝔣(χ)^{χ(1)}` over the irreducible classes `χ` of complex
   representations of `G`, with `𝔣(χ) = m_K ^ a(χ)` and `a(χ)` the Artin exponent. -/
def FiniteConductorDiscriminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (M : PadicField.{uM} p)
    [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
    [IsGalois K.Carrier M.Carrier] (TK : K.TopologicalData) (TM : M.TopologicalData),
    letI := TK.valuativeRel
    letI := TM.valuativeRel
    letI := relativeIntegerAlgebra TK TM
    ∀ {ι : Type uι} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι TK.Integers TM.Integers),
      (∀ N : ℕ, lowerRamificationGroup TM K.Carrier N = ⊥ →
        Ideal.span {Algebra.discr TK.Integers b} =
          maximalIdeal TK.Integers ^ ((inertia TM K.Carrier).index *
            ∑ i ∈ Finset.range N, (lowerGroupOrder TM K.Carrier i - 1))) ∧
      ∀ [Fintype (FiniteRep.IrreducibleClass (M.Carrier ≃ₐ[K.Carrier] M.Carrier))],
        Ideal.span {Algebra.discr TK.Integers b} =
          ∏ a : FiniteRep.IrreducibleClass (M.Carrier ≃ₐ[K.Carrier] M.Carrier),
            (maximalIdeal TK.Integers ^ artinExponent TM K.Carrier a.out.ρ) ^
              Module.finrank ℂ a.out

end Langlands.Ramification.Padic
