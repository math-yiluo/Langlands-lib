# Division algebras with a unitary involution over a local field are commutative

This module proves `Langlands.LocalUnitaryDivisionCommutativeStatement`
(`Langlands.Algebra.UnitaryInvolutionStatements`) as the theorem
`Langlands.localUnitaryDivisionCommutative`: for a nonarchimedean local field `K`, a separable
quadratic extension `L` with nontrivial `K`-automorphism `σ`, and a finite-dimensional central
division `L`-algebra `D` with a unitary involution `τ` relative to `σ`, `Module.finrank L D = 1`.

## Proof

1. **Local structure on `L`.** `L` receives the spectral valuation, topology and
   local-field structure of `Langlands.LocalField.FiniteExtension`. The helper
   `finiteExtension_valuation_aut` shows that `K`-automorphisms preserve this valuation
   (`spectralNorm_eq_of_equiv`), and `FiniteExtension.algebraMap_vle_iff` gives compatibility
   with the valuation of `K`. `D` is made a `K`-algebra through `L`.
2. **Galois facts.** `[L : K] = 2`, `L/K` is Galois, `Gal(L/K)` has two elements, so it is
   `{1, σ}` and the `σ`-fixed elements are exactly `K` (`IsGalois.mem_range_algebraMap_iff_fixed`).
3. **Part I.** `reducedDegree_dvd_two` (`Langlands.Algebra.LocalUnitaryResidue`) gives
   `d ∣ 2` for `d = reducedDegree L D`. If `d = 1`, `finrank L D = d² = 1`.
4. **Part II, `d = 2`.** Either every nonzero element of `K` has the valuation of a square in `L`
   — then `false_of_valuation_squares` (`Langlands.Algebra.LocalUnitaryQuaternion`, the descent
   case) gives a contradiction — or not, and then `exists_moved_of_not_squares`
   (`Langlands.Algebra.LocalQuadraticDichotomy`) yields an integral `θ` with `|σ θ - θ| = 1`, and
   `false_of_residue_moved` (the residue-field case) gives a contradiction.

The argument is valid in every characteristic of `K` and of its residue field; the descent case
replaces the corestriction argument of the literature (KMRT Theorem (3.1), Serre *Local Fields*
XIII §3) by an explicit descent of `D` to a quaternion algebra over `K`, the only cohomological
input being the Library theory of local division algebras (residue degree equals reduced degree,
cyclic unramified subfields, Skolem–Noether).
