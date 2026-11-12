# Proof of the `k^(2g)` scaling of the Euler product of an ample line bundle and its inverse

Author: Worker 3649 (this file pair). The proof applies a published reduction to two
published proofs; their authors are named below.

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingProof`,
namespace `Langlands.AbelianScheme`. The module contains one theorem:

```lean
theorem algClosedFieldAmpleEulerInverseScaling :
    AlgClosedFieldAmpleEulerInverseScalingStatement.{u} :=
  ScalingAssembly.algClosedFieldAmpleEulerInverseScalingReduction
    Langlands.GroupScheme.fieldCubePullback Langlands.GroupScheme.fieldTheoremOfTheSquare
```

Its type is exactly the published statement
`Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement.{u}` (module
`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement`), at an
arbitrary universe `u` and with no further hypotheses. For an algebraically closed field `K`
of any characteristic, an abelian scheme `A` over `Spec K` of relative dimension `g` (any
`g`, including `0`), an ample line bundle `H` with an inverse `N`, a natural number `k ≥ 1`
and an inverse `Nk` of the right-associated tensor power `tensorPow H.obj k`, it states the
integer identity

`χ(H^{⊗k}) · χ(Nk) = k^{2g} · (χ(H) · χ(N))`,

where `χ` is the published `eulerCharacteristic` of the actual derived cohomology
`relativeCohomology A.X.hom`. The four finite-cohomology proofs are arbitrary. See
`AlgClosedFieldAmpleEulerInverseScalingStatement.md` for the meaning of every binder.

## Proof

The theorem is one application. The published theorem
`Langlands.AbelianScheme.ScalingAssembly.algClosedFieldAmpleEulerInverseScalingReduction`
(module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingAssembly`)
proves the published proposition

`AlgClosedFieldAmpleEulerInverseScalingReductionStatement.{u} :=
  FieldCubePullbackStatement.{u} → FieldTheoremOfTheSquareStatement.{u} →
    AlgClosedFieldAmpleEulerInverseScalingStatement.{u}`.

It is applied to two published proofs:

- `Langlands.GroupScheme.fieldCubePullback : FieldCubePullbackStatement.{u}`
  (module `Langlands.AbelianScheme.FieldCubePullbackProof`, Worker 815), the balanced cube identity
  `Q(f+g+h) ⊗ (Q f ⊗ (Q g ⊗ Q h)) ≅ Q(f+g) ⊗ (Q(f+h) ⊗ Q(g+h))` for pullbacks `Q a = a^* L`
  of a line bundle `L` on a commutative smooth proper geometrically connected group scheme
  over any field, along maps `f, g, h` from any scheme over the field;
- `Langlands.GroupScheme.fieldTheoremOfTheSquare : FieldTheoremOfTheSquareStatement.{u}`
  (module `Langlands.AbelianScheme.FieldTheoremOfTheSquareProof`, Worker 2784), the theorem of the square
  `t_{a+b}^* L ⊗ L ≅ t_a^* L ⊗ t_b^* L` for rational points `a`, `b` of such a group scheme.

Both are the exact Library propositions, not hypotheses of this module. No other input is
used.

## What the published reduction does

This section summarizes the published modules that the one-line proof relies on, so that
the reader can follow the mathematics. Nothing here is reproved in this module.

`algClosedFieldAmpleEulerInverseScalingReduction` (Worker 998) composes two published
theorems.

1. `algClosedFieldAmpleEulerInverseScaling_of_ne_zero cube square` (same module) proves
   `AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement`, the target restricted to those
   `k` with `(k : K) ≠ 0`. It follows the computation of the Euler characteristic of the
   Mumford bundle in the proof of (9.11) of Edixhoven, van der Geer and Moonen, *Abelian
   Varieties* (registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
   formulas (10)–(12), printed p.132), without the dual abelian variety. On `Z = A ×_K A`
   with second projection `q`, let `Q(L, M) = m^* L ⊗ fst^* M`, where `m` is the addition.
   - The shear isomorphism and the Künneth formula give `χ(Z, Q(L, M)) = χ(L) χ(M)` for an
     inverse pair `L ⊗ M ≅ 𝒪` (`eulerCharacteristic_mumfordAddition_tensor_fst`).
   - By the theorem of the square and ampleness, every higher direct image
     `Rⁿ q_* Q(H^{⊗k}, Nk)` and `Rⁿ q_* Q(H, N)` has finite closed support
     (`hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst`), so twisting by
     the pullback along `q` of a line bundle does not change `χ` (`eulerCharacteristic_twist`).
   - By the balanced cube identity, `Q(H^{⊗k}, Nk) ⊗ q^* E ≅ (1 × [k])^* Q(H, N)` for a line
     bundle `E` on `A` (`nonempty_pullback_twistedProduct_iso`).
   - For `(k : K) ≠ 0`, multiplication `[k]` is a finite flat isogeny
     (`multiplication_isIsogeny_of_ne_zero`) of native rank `k^{2g}` at every point
     (`finrank_multiplication_eq_of_ne_zero`, which uses the balanced cube identity and the
     ample `H`). Finite flat base change along `1 × [k]` multiplies `χ` by `k^{2g}`
     (`eulerCharacteristic_finiteFlatBaseChange`).

   Together: `χ(H^{⊗k}) χ(Nk) = χ(Z, Q(H^{⊗k}, Nk)) = k^{2g} χ(Z, Q(H, N)) =
   k^{2g} χ(H) χ(N)`.
2. `algClosedFieldAmpleEulerInverseScaling_of_coprime` (Worker 1222, module
   `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingCoprimeExtension`)
   extends the restricted statement to every `k ≥ 1`. The values `χ(H^{⊗n})` and
   `χ(N^{⊗n})` are values of rational polynomials in `n` (`smoothProperLineBundleEulerPolynomial_degree_le`).
   Their product agrees with `χ(H) χ(N) X^{2g}` at the infinitely many `n ≥ 1` that are
   nonzero in `K`, so the polynomials are equal. Evaluating at `k`, and replacing `Nk` by the
   isomorphic `N^{⊗k}`, gives the identity for every `k ≥ 1`.

The two published premises are themselves proved from the geometric theorem of the cube
`Langlands.AlgebraicGeometry.Picard.fieldCubeTriviality` (module
`Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityProof`), through the two-line-bundle
form `FieldCubeIsomorphismStatement` and the published conditional assembly
`fieldCubePullbackOfIsomorphism`; the theorem of the square is the case `f = a`, `g = b`,
`h = 𝟙` of the balanced cube.

## Provenance

The proof route is internal: it is the composition of published Library theorems described
above. The source result is Edixhoven, van der Geer and Moonen, (9.11) and formula (7),
`χ(L^m) = m^g χ(L)`, printed p.131 (J. S. Milne, *Abelian Varieties*, registered source
`milne-abelian-varieties-1986-author-2022`, Theorem 13.3, p.25, gives the same). The proof
does not use Riemann–Roch, Serre duality, a dual abelian variety or a Poincaré bundle.

## Dependencies and checks

- The import closure of this module contains neither
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryStatement` nor
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleMumfordEulerSquareStatement`, nor
  any module importing them. It uses neither
  `Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement` nor
  `Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`.
- The statement pair and its import closure are unchanged.
- `algClosedFieldAmpleEulerInverseScaling` depends only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound`.
