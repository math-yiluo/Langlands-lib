# Proof that the end ring is the henselization of `k[x]` at `x = 0`

Module `Langlands.Correspondence.Laumon.EndTraitHenselizationProof`. The theorem
`endTraitHenselization` proves `EndTraitHenselizationStatement` (module
`Langlands.Correspondence.Laumon.Traits`), at its universe parameter, for every field `k`:
`endRing k`, the ring of power series in `t` that are separable algebraic over `k(t)`, is a
henselian local ring and a discrete valuation ring, its uniformizer `endUniformizer k .zero` (the
series `t`) is irreducible, and every ring map `φ : k[x] → B` to a henselian local ring with
`φ⁻¹(𝔪_B) = (x)` extends along `endChartCoordinate k .zero` (`x ↦ t`) to a unique local ring map
`endRing k → B`. This is the statement that `endRing k` is the henselization `k{x}` of
`k[x]_(x)` (Laumon 1987, (2.1.1), p. 151; Stacks Project, Section 10.155).

The proof assembles four results.

1. **Henselian** (`henselianLocalRing_endRing`, module
   `Langlands.Correspondence.Laumon.EndRingDvr`). A simple residual root of a monic polynomial
   over `endRing k` lifts to a root in `k⟦t⟧`, which is henselian; the lift is a simple root,
   hence separable over `endField k` and so over `k(t)`, and therefore lies in `endField k`.
2. **Discrete valuation ring** (`isDiscreteValuationRing_endRing`, same module). An element of
   `endRing k` is a unit exactly when its constant coefficient is nonzero, and every nonzero
   element is `t ^ n` times a unit.
3. **Irreducible uniformizer** (`irreducible_endUniformizer`, same module).
4. **Universal property** (`existsUnique_endRing_hom`, module
   `Langlands.Correspondence.Laumon.EndRingStageMaps`). Every element of `endRing k` lies in the
   *stage ring* of a *simple point* `b` (a root of a polynomial `G ∈ k[x][Y]` with `G'(b)` a
   unit): the fractions `p(b) / q(b)` with `q(b)` a unit. A Newton shift
   `b = (γ - γ_N) / t ^ N` turns any separable `γ` into such a point
   (`Langlands.Correspondence.Laumon.EndRingSimplePoints`), and every element of `endRing k`
   lying in `k(t)(b)` belongs to the stage ring of `b`; with a primitive element, any two
   elements lie in a common stage ring (`Langlands.Correspondence.Laumon.EndRingStages`). On a
   stage ring there is exactly one map to `B` extending `φ` with the right residues: it sends
   `b` to the root of `μ^φ` lifting the residue of `b` (`μ` the primitive minimal polynomial of
   `b`, Gauss's lemma for the kernel; Hensel's lemma in `B` for a polynomial that need not be
   monic, `Langlands.CommutativeAlgebra.HenselianSimpleRoots`), and uniqueness is the uniqueness
   of simple roots in a local ring. These maps glue to the required local map, and any local map
   extending `φ` restricts to them.

The proof does not use the weil-conjectures declarations named in the statement's Markdown
(`IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable`) nor the étale local
structure theory of Mathlib; it depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
