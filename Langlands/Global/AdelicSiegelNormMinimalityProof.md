# Proof of polynomial norm minimality on actual adelic Siegel products

Authors: Worker 5414 and Worker 5644.

This module proves the published proposition
`Langlands.Global.AdelicSiegelFactors.SiegelNormMinimalityStatement` (module
[`AdelicSiegelNormMinimalityStatement`](AdelicSiegelNormMinimalityStatement.md)) as the
theorem

```lean
theorem Langlands.Global.AdelicSiegelFactors.siegelNormMinimalityStatement :
    SiegelNormMinimalityStatement.{u}
```

at every universe `u` and without extra hypotheses. The statement is used unchanged.

## What is proved

Let `F : Type u` be a number field and let `G` be a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`. Let
`rho : MatrixRepresentation G (Fin N)` be a matrix representation. Assume
`IsConnectedReductive G`, `IsClosedSubgroup rho` and `0 < N`. Assume also
`IsSiegelAlgebraicSetup F G T i ν T₀ j`, and fix compact factors `C` for the standard
unipotent subgroup and standard Levi subgroup, and a threshold `t : ℝ≥0ˣ`. Then there
are a real `c` and a natural number `e` such that

```
adelicHeight F G rho s ≤ c * adelicHeight F G rho (rational F G q * s) ^ e
```

for every `s` in the weak Siegel product
`weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t` and every
rational point `q`. The proof gives `e = 1`. The hypothesis `IsClosedSubgroup rho` is
not used.

## Provenance

Mœglin–Waldspurger 1995 (`moeglin-waldspurger-1995-spectral-decomposition`), I.2.2 (vii),
printed pp. 20–21. The Markdown of the statement records the correspondence. The Lean
proof follows the plan in Task 5910's context, in three parts.

## Proof

The theorem is `siegelNormMinimalityStatement_of_diagonal` applied to
`exists_adelicHeight_map_le_rational_mul`.

- **Part A**, `exists_adelicHeight_map_le_rational_mul` (module
  [`AdelicSiegelDiagonalHeightBound`](AdelicSiegelDiagonalHeightBound.md), by
  Worker 5644). Let `T₀` be a split torus and `f : T₀.toGrp ⟶ G` a homomorphism. Then the
  height of the image of an intrinsic positive point of `T₀` is at most a constant times
  the height of each of its rational left translates. The proof diagonalizes `rho ∘ f`
  over `F` and applies the product formula.
- **Part B**, `exists_adelicHeight_conj_unipotent_le` (module
  [`AdelicSiegelConjugationBound`](AdelicSiegelConjugationBound.md), by Worker 5414).
  Conjugating a compact set of unipotent adelic points by the inverse of a weak chamber
  point gives bounded height.
- **Assembly**, `exists_adelicHeight_le_mul_rational_of_diagonal` and
  `siegelNormMinimalityStatement_of_diagonal` (module
  [`AdelicSiegelNormMinimalityAssembly`](AdelicSiegelNormMinimalityAssembly.md), by
  Worker 5414). Write `s = ι_N(n) · ι_M(m) · a · k`. The proof bounds the compact factors
  and moves `ι_M(m)` past `a`, using the setup's centralizer clause. With Part B it gets
  `H(s) ≤ B₁ · H(a)` and `H(q a) ≤ B₂ · H(q s)`. Part A, applied to
  `f = CommGroupScheme.groupHom j ≫ i`, gives `H(a) ≤ c · H(q a)`. Together these give
  `H(s) ≤ B₁ · c · B₂ · H(q s)`.

The linked Markdown files record each step.

## Checks

`lean_check` of this module in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with a
Lake build, reports no errors or warnings. The declaration inspection of
`siegelNormMinimalityStatement` shows only `propext`, `Classical.choice` and `Quot.sound`
(diagnostic `712e44a0-06a2-4a1e-bf4a-313844c2fdd1`). Worker 24 rechecked all four modules
over Library commit `f2b3d7dcdd52af1923cd0bf5c4d90beda3118720` with the same result
(diagnostic `12ca220b-423d-4a37-b422-3120df9ecce6`).
