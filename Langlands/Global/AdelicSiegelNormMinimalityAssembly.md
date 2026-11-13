# Norm minimality on weak Siegel products from a diagonal height inequality

Author: Worker 5414.

This module assembles the planned proof of
`Langlands.Global.AdelicSiegelFactors.SiegelNormMinimalityStatement` (Task 5910). It
reduces the statement to Part A of the plan, the diagonal inequality for positive points
of split tori. Part B is the conjugation bound `exists_adelicHeight_conj_unipotent_le`
(module [`AdelicSiegelConjugationBound`](AdelicSiegelConjugationBound.md)). All
declarations are in the namespace `Langlands.Global.AdelicSiegelFactors`. Write
`H = RepresentationGrowth.adelicHeight F G rho`.

## Statements

### `exists_adelicHeight_le_mul_rational_of_diagonal`

This theorem takes the following data:

- a number field `F : Type u`;
- a group scheme `G` over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`;
- a setup with `IsSiegelAlgebraicSetup F G T i ν T₀ j`;
- a matrix representation `rho : MatrixRepresentation G (Fin N)` with `0 < N`;
- compact factors
  `C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)`;
- a threshold `t : ℝ≥0ˣ`;
- a real `c ≥ 0`.

Its hypothesis `hdiag` asks that

```
H (positiveMap F G T i T₀ j a) ≤ c * H (rational F G q * positiveMap F G T i T₀ j a)
```

hold for every intrinsic positive point `a` of `T₀` and every rational point `q` of `G`.
The conclusion gives a real `c'` such that

```
H s ≤ c' * H (rational F G q * s)
```

for every `s` in
`weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t` and every
rational point `q`.

### `siegelNormMinimalityStatement_of_diagonal`

This theorem derives `SiegelNormMinimalityStatement.{u}` from one hypothesis `hA`. Take
any number field `F : Type u` and any group scheme `G` over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`. Take any
`rho : MatrixRepresentation G (Fin N)` with `0 < N`, any `T₀` with
`IsSplitTorus T₀.toGrp`, and any homomorphism `f : T₀.toGrp ⟶ G`. The hypothesis `hA`
asks for a real `c ≥ 0` such that

```
H (map F T₀.toGrp G f a) ≤ c * H (rational F G q * map F T₀.toGrp G f a)
```

for every `a : PositiveRealTorus.intrinsicSubgroup F T₀` and every rational point `q`.
This is the interface fixed for Part A in Task 5910's context, under the name
`exists_adelicHeight_map_le_rational_mul`. The theorem proves the statement with
exponent `e = 1`.

## Provenance

The statement being proved is Mœglin–Waldspurger 1995
(`moeglin-waldspurger-1995-spectral-decomposition`), I.2.2 (vii), printed pp. 20–21. The
Markdown of `SiegelNormMinimalityStatement` records the correspondence. The two
theorems here are the assembly step of the proof plan in Task 5910's context. The
hypotheses `hdiag` and `hA` are Part A of that plan, not published results.

## Proof

### `exists_adelicHeight_le_mul_rational_of_diagonal`

1. **Bounds on the compact factors.** Height is continuous by `continuous_adelicHeight`,
   and the inclusions `ι_N` and `ι_M` are continuous. So `H ∘ ι_N` is bounded on
   `C.omegaN` by some `B_N`, `H ∘ ι_M` is bounded on `C.omegaM` by some `B_M`, and `H` is
   bounded on `C.compactSubgroup` by some `B_K`. Here `ι_M` is the map
   `m ↦ map (Standard.leviHom i ν ∅) m` on norm-one points. These bounds are nonnegative,
   because `one_le_adelicHeight` gives `H ≥ 1`.
2. **Part B.** `exists_adelicHeight_conj_unipotent_le` with `Ω = C.omegaN` gives `B` with
   `H(A⁻¹ ι_N(n) A) ≤ B`. Here `n ∈ C.omegaN`, `a` lies in the weak chamber, and
   `A = positiveMap F G T i T₀ j a`.
3. **Decomposition.** `mem_productSet_iff` writes `s = ι_N(n) · ι_M(m) · A · k`, with
   `n ∈ C.omegaN`, `m ∈ C.omegaM`, `a` in the chamber and `k ∈ C.compactSubgroup`.
4. **Commutation.** The setup clause `standardLevi i ν ∅ = torusCentralizer i` and
   `commute_of_mem_standardLevi_image` (module `AdelicPositiveTorusCompatibility`) show
   that `ι_M(m)` commutes with `A`. Hence `s · k⁻¹ · ι_M(m)⁻¹ = ι_N(n) · A`, and so
   `A = s · k⁻¹ · ι_M(m)⁻¹ · (A⁻¹ ι_N(n) A)⁻¹`.
5. **Estimates.** `adelicHeight_mul_le` and `adelicHeight_inv` give two bounds:
   - `H(s) ≤ H(ι_N n) · H(ι_M m) · H(A) · H(k) ≤ B_N · B_M · H(A) · B_K`;
   - `H(q A) ≤ H(q s) · H(k) · H(ι_M m) · H(A⁻¹ ι_N(n) A) ≤ H(q s) · (B_K · B_M · B)`.

   Here `q A` means `rational F G q * A`. With `hdiag`,
   `H(A) ≤ c · H(q A) ≤ c · H(q s) · (B_K · B_M · B)`. Therefore
   `H(s) ≤ c' · H(q s)` with `c' = B_N · B_M · (c · (B_K · B_M · B)) · B_K`.

### `siegelNormMinimalityStatement_of_diagonal`

1. The setup's derived-subgroup clause supplies a maximal split torus `t₀` with source
   `T₀`. Its first component gives `IsSplitTorus T₀.toGrp`. The Library proof of
   `adelicRationalHeightReductionStatement_of_siegel` obtains it the same way.
2. Apply `hA` to `f = CommGroupScheme.groupHom j ≫ i`. Then `map F T₀.toGrp G f a` is
   `positiveMap F G T i T₀ j a` by definition, so `hA` gives `hdiag`.
3. The first theorem then gives `c'`, and `e = 1` works because `x ^ 1 = x`.

The hypothesis `IsClosedSubgroup rho` of the statement is not used.

## Checks

`lean_check` of this module in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
reports no errors or warnings (diagnostic `bcdb3097-cf4d-455e-a2b9-19d75cc7406b`). The
declaration inspections with a Lake build show only `propext`, `Classical.choice` and
`Quot.sound` for
- `exists_adelicHeight_le_mul_rational_of_diagonal` (diagnostic
  `15ac5672-b1a6-45a4-b8cf-7f012e8830bf`);
- `siegelNormMinimalityStatement_of_diagonal` (diagnostic
  `3a255bd5-0763-43a7-9a0d-2c17c5cb9725`).

A Lake build of this module with the three others of the proof over Library commit
`f2b3d7dcdd52af1923cd0bf5c4d90beda3118720` again reports no errors or warnings (diagnostic
`12ca220b-423d-4a37-b422-3120df9ecce6`).
