# Necessary upper Jacquet bounds for an analytically tempered product Levi

Authors: Worker 540 and Worker 573. Worker 573 supplied the interface and
dependency audit; Worker 540 formulated the paired statement and checked the
original sources.

`Langlands.GLProductLeviTemperedExponentNecessityStatement.{uF,uV}` is a closed
`Prop`-valued definition. This module states the analytic necessity direction
for the actual block Levi. It supplies no proof.

## Input and measure

For every prime `p`, p-adic field `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, positive rank `n`, and ordered block shape `B`,
let `M = B.Levi F.Carrier` and `Q = M ⧸ Subgroup.center M`. The field
topology is `T.topology`; the Levi has its product topology. Quantify an
arbitrary Borel measurable structure on this actual quotient and one Haar
measure `μ` for it.

The input is any actual representation `σ : Representation ℂ M V`,
with `V : Type uV`, that is irreducible and satisfies
`IsTemperedModCenter σ μ`. The field and carrier universes are independent.
The analytic predicate includes admissibility, a unitary character of the
full centre with open kernel, and membership of every descended absolute
smooth matrix coefficient in `L^(2+ε)(Q, μ)` for every real `ε > 0`.
No tensor presentation, supplied scalar character, invariant positive form,
or temperedness for all Haar measures is an extra premise. Irreducibility
is retained from the induction consumer.

## Exact exponent conclusion

For every refinement `D : Geometric.BlockRefinement B`, put `C = B.flatten D`.
Use the actual normalized upper refined Jacquet action
`T.normalizedRefinedJacquet B D σ`. Pull it back from the refined Levi
through `Geometric.flattenedLeviEquiv F.Carrier B D`, then restrict to
`C.blockScalarLevi F.Carrier`.

Every character `ψ : (Fin C.length → F.Carrierˣ) →* ℂˣ` with open kernel
that is an `IsGeneralizedEigencharacter` of this restriction must satisfy
`‖ψ(a)‖ ≤ 1` whenever

```text
|a_(e(j,0))| ≤ |a_(e(j,1))| ≤ ...
e(j,i) = B.flattenBlockEquiv D ⟨j,i⟩
```

separately for each `j : Fin B.length`, with `|·| = T.normalizedAbs`.
There is no comparison between distinct outer blocks. All refinements,
including the identity refinement, are included. A generalized
eigencharacter is detected by a nonzero vector killed by one common power
of every character-defect operator; the power is uniform in the scalar
tuple. No ordinary eigenvector or full-dual eigenfunctional is substituted.

This conclusion is exactly the upper refinement-bound premise of
`GLProductLeviTemperedExponentSufficiencyStatement`, with its bundled
representation replaced by the actual `σ`. The sufficiency statement is
not a premise or a proof of necessity. The upper normalization is inverse
positive half-modulus. Its modulus on fine block scalars is

```text
δ_D(a) = product_j product_(k<l)
  |a_(e(j,k)) / a_(e(j,l))|^((D j).size k * (D j).size l).
```

In scalar real-part coordinates the bound is the nonnegative-prefix
condition within each outer block, with zero total there. If determinant
coordinates are used in a proof, the scalar exponent is the determinant
exponent multiplied by the corresponding fine block size.

## Original source and derived translation

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
literature ID `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:

- I.3, printed p.243 (PDF9), defines the uniform-power generalized
  exponents and the inverse-half normalized Jacquet action.
- Theorem I.4.1, printed p.245 (PDF11), gives the nondegenerate Casselman
  pairing and coefficient asymptotics in a sufficiently deep chamber.
- Proposition III.2.2, printed pp.265–266 (PDF31–32), identifies temperedness
  with the weak cone condition on every normalized Jacquet exponent.
- I.1(4)–(5), printed p.241 (PDF7), gives the Cartan decomposition and the
  two-sided comparison of Cartan-cell volume with inverse modulus.

These passages were read directly and their formula pages viewed as images.
No source-specific errata file was found in the workspace or public notes.

The specialization to the reductive group `M = product_j GL_(B.size j)(F)`
is derived: its standard parabolics are precisely the refinements `D`,
its centre is the product of the scalar centres, and its roots compare
fine scalars only within a fixed outer block. The explicit flattened
coordinates and their constructed Levi equivalence are Library
constructions rather than assertions stated in Waldspurger's notation.

Waldspurger defines temperedness using a coefficient bound by
`Ξ(g)(1+σ(g))^r`. The input here instead uses `L^(2+ε)` on the actual
full-centre quotient. Thus Proposition III.2.2 alone does not prove this
formal statement. The required analytic translation can use the
nondegenerate asymptotic pairing to detect an exponent on a deep chamber,
and the lower Cartan-cell volume estimate to rule out exponential
growth: a strict violation of the weak bound persists along a
uniformizer ray; for sufficiently small positive `ε` the corresponding
coefficient cannot lie in `L^(2+ε)`. Generalized vectors and chamber
boundaries require the finite-dimensional generalized-spectrum and
lattice arguments as well. This paragraph describes a proof obligation,
not an implemented result.

The measure comparison, the passage to the quotient by the full centre,
and the use of the single supplied Borel Haar measure also remain
obligations. They may be handled by deriving a same- or cross-Borel Haar
adapter, but no such adapter is assumed by this proposition.

## Intended use and remaining work

A separate proof must establish this exact proposition. Together with
algebraic preservation of these bounds by actual normalized induction,
induced admissibility, the induced scalar character and the ambient
tempered exponent criterion, it would supply the analytic induction
preservation argument. This statement proves none of those ingredients
and does not discharge `GLTemperedInductionPreservationStatement`.
