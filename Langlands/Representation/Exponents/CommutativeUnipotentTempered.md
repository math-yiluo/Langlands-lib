# Unipotent representations of commutative reductive groups are tempered

Author: Worker 100. Module `Langlands.Representation.Exponents.CommutativeUnipotentTempered`.

This helper module proves the temperedness half of the counterexample built for Renard's
Remark after the Corollary of VII.2.6: `𝔾_m` acting on `ℂ²` by `x ↦ [[1, ord(x)], [0, 1]]` is
tempered but not unitary. The Remark only says that without irreducibility the Corollary
("an irreducible tempered representation is unitary") can fail; Renard gives no example. The lemma here is internal and more general than the example. It applies to any
connected reductive `G` whose group of rational points `G(k)` is commutative, and to any
admissible smooth representation `π` with `(π(g) - 1)² = 0` for all `g`.

Source of the Remark: David Renard, *Représentations des groupes réductifs p-adiques*,
registered `renard-2026-representations-groupes-reductifs-padiques`, VII.2.6, Remark
(printed p.232 / PDF p.238). Renard states neither the example nor this lemma. The lemma is
the argument that the example's normalized exponents are trivial, written for the published
definitions.

## Declarations (namespace `Langlands.Aubert.General.RepresentedParabolic`)

- `eq_one_of_sq_sub_one_eq_zero_of_pow_sub_smul_apply_eq_zero`: generic linear algebra. Let `T`
  be a `ℂ`-linear operator with `(T - 1)² = 0`. If a nonzero `w` satisfies `(T - c)^d w = 0`,
  then `c = 1`. If `c ≠ 1`, `w` would lie in the generalized eigenspaces of `T` for `c` and for
  `1`, which are disjoint (Mathlib's `Module.End.disjoint_genEigenspace`).
- `jacquet_sq_sub_one_eq_zero_of_mul_comm`: suppose `G(k)` is commutative and
  `(π(g) - 1)² = 0` for all `g`. Then, for every specified parabolic `p`, Levi `l`, unipotent
  radical `r` with multiplication isomorphism, and split component `a`, every split-component
  point `t` acts on the normalized Jacquet module (`jacquetFunctor`) by an operator `T` with
  `(T - 1)² = 0`. The image `m` of `t` is central in `G(k)` because `G(k)` is commutative.
  The published `normalizedJacquetFunctor_obj_apply_of_mem_center` therefore shows that `T`
  acts on the coinvariant class of `x` by the class of `π(m) x`; the inverse half modulus is
  trivial at central points. Applying this twice gives
  `(T - 1)²(mk x) = mk((π(m) - 1)² x) = 0`. The quotient map `mk` is surjective, so
  `(T - 1)² = 0`.
- `eq_one_of_isNormalizedJacquetExponent_of_mul_comm`: under the same hypotheses, every
  normalized Jacquet exponent `χ` is the trivial character. The published
  `isNormalizedJacquetExponent_iff` and `isGeneralizedEigencharacter_iff` give one exponent `d`
  and a nonzero `w` with `(T_t - χ(t))^d w = 0` for every `t`. The linear algebra lemma then
  gives `χ(t) = 1` for each `t`.
- `isNormalizedExponentTempered_of_mul_comm_of_sq_sub_one_eq_zero`: under the same hypotheses,
  and assuming admissibility, `π` satisfies the published `IsNormalizedExponentTempered`. For
  every specified parabolic, Levi and split component, a compatible root presentation exists
  by the published `GroupScheme.parabolicRootPresentationExistence`. Every exponent is `1`, and
  its normalized real part is `0` (`Plancherel.SplitTorus.normalizedRealPart_one`). This lies
  in every presentation's nonnegative cone (`ParabolicRootPresentation.zero_mem_nonnegCone`).

The hypotheses are those of the variable block of `ArbitraryParabolicTempered`: a
nonarchimedean local field `k` with `T2Space k`, `IsAffineHom G.X.hom`, the canonical point
topology `RationalPointFamily.pointTopology` (a local instance), and `LocallyCompactSpace` and
`NonarchimedeanGroup` on `G(k)`.
