# Product-Levi square-integrability from strict Jacquet exponent bounds

Author: Worker 907, with Worker 728, who drafted the Lean formulations in the
task contract and in the shared task draft. The Lean text is that draft,
unchanged.

This module defines two closed propositions. Each has independent field and
representation universes `uF` and `uV`:

- `Langlands.GLProductLeviSquareIntegrableExponentSufficiencyStatement` is the
  core statement, phrased with upper generalized Jacquet exponents.
- `Langlands.GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement` is
  the consumer statement, phrased with dual eigenfunctionals on refined
  opposite Jacquet modules.

Both are `Prop`-valued definitions. Neither proposition is proved here. They
are the square-integrable analogues of the published tempered pair in
[`ProductLeviTemperedSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md).
The data, the hypotheses on `S` and `ω`, the quantifier over all refinements
`D`, and the shape of the conclusion are the same. Two things change:

- the conclusion `IsTemperedModCenter` becomes `IsSquareIntegrableModCenter`;
- each exponent condition gains a strict part in the non-central directions.

## Common data and hypotheses

Both statements quantify over:

- every prime `p` with `Fact p.Prime`;
- every `F : PadicField.{uF} p` and every realization `T : F.TopologicalData`,
  with topology `T.topology`;
- every positive rank `n` and every ordered block shape `C : BlockShape n`.

The group is the actual product Levi `M_C = C.Levi F.Carrier`, whose factors
are `GL_(C.size j)(F)`.

The bundled complex representation `S : Rep.{uV} ℂ M_C` is assumed
irreducible (`Representation.IsIrreducible S.ρ`) and admissible
(`IsAdmissible S.ρ`, which includes smoothness). A character
`ω : (Fin C.length → F.Carrierˣ) →* ℂˣ` satisfies
`Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) ω`: each
tuple of block scalar matrices acts on `S` by the number `ω` of the tuple. The
hypothesis `∀ a, ‖(ω a : ℂ)‖ = 1` makes `ω` unitary.

Openness of `ω.ker` is not assumed separately: it follows from smoothness and
a nonzero vector. The block scalars are the whole centre of `M_C`, because the
centre of a positive-size `GL_m(F)` is its scalars. This identification is part
of the mathematical translation, not an extra hypothesis.

Each statement adds one exponent hypothesis, quantified over every refinement
`D : BlockRefinement C`. These are described in the next two sections.

## Conclusion

Under its exponent hypothesis, each statement concludes

```text
IsSquareIntegrableModCenter S.ρ μ
```

for every Borel measurable structure on `Q = M_C ⧸ Subgroup.center M_C` and
every Haar measure `μ` on `Q`. The product group topology comes from
`T.leviTopologicalGroup C`.

The published predicate (in
[`MatrixCoefficient.ModuloCenter`](../MatrixCoefficient/ModuloCenter.md)) is
the conjunction of:

- `IsAdmissible S.ρ`;
- a `UnitaryCentralCharacter S.ρ`: a character of `Subgroup.center M_C` with
  open kernel and norm one, by which the centre acts;
- for every smooth functional `ℓ` and every vector `v`, membership of the
  descended coefficient norm `gZ ↦ ‖ℓ(S.ρ g v)‖` in `L²(Q, μ)`.

So the conclusion concerns the whole product Levi modulo its actual full
centre, for every choice of Borel Haar measure.

## The upper core hypothesis

Notation:

- `D : BlockRefinement C` chooses an ordered block shape `D j` inside each outer
  block `j`. Every refinement is quantified, including the identity refinement.
- `B = C.flatten D`, and `e(j,k) = C.flattenBlockEquiv D ⟨j,k⟩` is the flat
  index of the `k`-th inner block of outer block `j`.
- `flattenedLeviEquiv F.Carrier C D` identifies `B.Levi F.Carrier` with the
  actual refined Levi subgroup of `M_C`.
- `|·|` is `T.normalizedAbs`, with `|ϖ| = q⁻¹`.

Restrict `T.normalizedRefinedJacquet C D S.ρ` along `flattenedLeviEquiv` and
then along `B.blockScalarLevi F.Carrier`. Take any character
`ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with open kernel that is a generalized
eigencharacter of this restriction. `IsGeneralizedEigencharacter` means that
some nonzero vector is killed by a single power of every operator
`(action of a) − ψ(a)`.

Take any tuple `a` that is monotone in each outer block:

```text
|a_(e(j,0))| ≤ |a_(e(j,1))| ≤ ...      for each j separately.
```

The Lean condition writes this with `Monotone` on `Fin (D j).length`. Different
outer blocks are not compared. For such `a` the hypothesis requires:

1. `‖ψ(a)‖ ≤ 1`;
2. `‖ψ(a)‖ < 1` if, for some `j`, the values `|a_(e(j,k))|` are not all equal.

The upper action uses the inverse upper half-modulus
(`normalizedRefinedJacquet_mk`). On fine block scalars, the modulus of the
refined parabolic inside `M_C` is

```text
δ_D(a) = product_j product_(k<l)
           |a_(e(j,k)) / a_(e(j,l))|^((D j).size k * (D j).size l).
```

This is Waldspurger's normalization of the Jacquet module by `δ_P^(-1/2)`, for
the parabolic `P_D ∩ M_C` of `M_C`.

### Why the weak conjunct is redundant

Part 1 already follows from part 2 together with the other hypotheses. This
is derived here, not stated in Lean. Suppose `|a_(e(j,k))|` does not depend on
`k`, for each `j`. Then `a = z u`, where:

- `z` is constant on each outer block, so it is a central block scalar of
  `M_C`;
- `u` has unit entries.

The refined modulus is trivial on `z`, and `z` acts on `S` by `ω(z)`. So `z`
acts on the Jacquet quotient by `ω(z)`, and a generalized eigencharacter
satisfies `ψ(z) = ω(z)`. Also `‖ψ(u)‖ = 1`, because `ψ` maps the compact unit
group to a compact subgroup of `ℂˣ`. Hence `‖ψ(a)‖ = ‖ω(z)‖ = 1`.

The weak bound is kept explicitly because the tempered pair and the consumer
use the same shape.

## The dual-opposite consumer hypothesis

Quantify over:

- every refinement `D`;
- every open-kernel character `ψ`;
- every real vector `s : Fin B.length → ℝ` with `T.IsRealPartOf ψ s`, which
  means exactly `‖ψ(a)‖ = product_b |a_b|^(s_b)` for every `a`;
- every nonzero functional
  `φ : Module.Dual ℂ (Geometric.RefinedOppositeJacquetModule C D S.ρ)` that
  satisfies the eigen-equation

```text
φ(Jbar_D(m(a)) q(v)) = ψ(a) φ(q(v))
```

for all fine scalar tuples `a` and source vectors `v`. Here:

- `q` is `refinedOppositeJacquetMk C D S.ρ`;
- `m(a)` is the image of the flattened block scalar under `flattenedLeviEquiv`;
- `Jbar_D` is `T.normalizedRefinedOppositeJacquet C D S.ρ`. It uses the
  positive upper half-modulus (`normalizedRefinedOppositeJacquet_mk`), which is
  the inverse half-modulus of the opposite parabolic.

The quotient map `q` is surjective, so this is the eigenfunctional condition
on the whole quotient. As in the tempered pair and
[`Exponents.DualJacquet`](../Exponents/DualJacquet.md), the dual is the full
algebraic dual and the action is plain transposition: the character is neither
inverted nor conjugated.

The hypothesis then requires, for every outer block `j` and every inner index
`i`:

```text
P(j,i) = sum_(k ≤ i) s_(e(j,k)) ≤ 0,
P(j,i) < 0   whenever i + 1 < (D j).length.
```

A prefix with `i + 1 < (D j).length` is called *proper*: it stops before the
last inner block of `j`.

The full prefix of each outer block is only required to be `≤ 0`, but it is
automatically zero. This is a derived remark, not an extra hypothesis. The
argument is the one for the weak conjunct above: on scalars constant within
each outer block, the refined modulus is trivial and the quotient action is
that of `ω`. With `φ ≠ 0`, the eigen-equation gives `‖ψ‖ = 1` there, and testing
a uniformizer gives `sum_k s_(e(j,k)) = 0`.

## The strictness condition

The weak parts of both hypotheses are the published tempered conditions. The
strict parts are what separate square-integrability from temperedness:

- In the core form, the bound is strict on every monotone tuple outside the
  centre of `M_C` times the unit tuples.
- In the consumer form, every proper prefix is strictly negative.

For example, take `C = (2)` and the unitary principal series `1 × 1` of
`GL_2(F)`. Its exponents along `D = (1,1)` have real part `(0,0)`. It
satisfies both weak conditions but neither strict condition, as it should,
since it is tempered and not square-integrable. This is an illustration only,
not a Lean theorem.

## Relation between the two forms (derived, not proved here)

The relation is the same as for the tempered pair, with strictness carried
along.

- **Weyl conjugation.** Conjugation by the long Weyl element of each factor of
  `M_C` takes the inner opposite parabolic of `D` to the standard upper
  parabolic of the blockwise reversed refinement `D^rev`. It also takes the
  opposite normalization to the upper normalization of `D^rev`. The conjugated
  representation is equivalent to `S` through its own action. Reversal is a
  bijection on refinements, so quantifying all `D` on one side matches
  quantifying all `D` on the other.
- **Eigenfunctionals and exponents.** A nonzero eigenfunctional of an
  admissible, finitely generated Jacquet module detects a generalized
  eigencharacter on a finite-dimensional compact-open invariant subspace.
  Conversely, every generalized eigencharacter has a dual eigenvector there,
  which extends by compact-open averaging. So the characters tested by the
  consumer form are the exponents tested by the core form, after reversal.
- **Summation by parts.** Fix an outer block with `m` inner blocks. Let `r` be
  the upper real part, `R_k` its prefixes, and `x_k = log|a_k|`. Then

  ```text
  sum_k r_k x_k = R_m x_m − sum_(k<m) R_k (x_(k+1) − x_k).
  ```

  With `R_m = 0`, the core condition (`≤ 0` on increasing `x`, `< 0` unless `x`
  is constant) is equivalent to `R_k > 0` for every proper `k < m`.

  Within the block, reversal gives `r_k = s_(m+1−k)`, so
  `R_k = −(sum_(l ≤ m−k) s_l)`. Hence strictly positive proper upper prefixes
  correspond exactly to strictly negative proper opposite prefixes.
- **Zero totals.** These are automatic on both sides, by the central argument
  above.

A proof of the consumer form may therefore import the core proof together with
this adapter, as in
[`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md) for the
tempered pair. The Weyl conjugation, the spectral detection, the existence of
real parts, and the moduli identifications remain proof obligations. No
equivalence of the two hypotheses is stated as a Lean theorem in this file.

## GL₂ sign check

This is an explanatory calculation, not a Lean theorem. It uses the published
upper convention and the Library's opposite convention. Take `C = (2)`, so
`M_C ≅ GL_2(F)`. Its refinements are `(2)` and `(1,1)`.

| Representation | Upper real part on `(1,1)` | Opposite real part on `(1,1)` | Opposite prefixes |
| --- | --- | --- | --- |
| Steinberg `St₂` | `(1/2, -1/2)` | `(-1/2, 1/2)` | `-1/2` (proper), `0` (total) |
| Trivial representation | `(-1/2, 1/2)` | `(1/2, -1/2)` | `1/2` (proper), `0` (total) |

**`St₂`, upper.** The exponent along the Borel is `|·|^(1/2) ⊗ |·|^(-1/2)`, so
`‖ψ(a)‖ = (|a₁|/|a₂|)^(1/2)`. On `|a₁| ≤ |a₂|` this is at most one, and it is
strictly below one when `|a₁| < |a₂|`.

**`St₂`, opposite.** The proper prefix `-1/2` is strictly negative and the
total is `0`.

**Refinement `(2)`.** Both representations have a unitary central character,
and the only exponent is that character:

- in the core form, the norm is `1` and no tuple is non-constant;
- in the consumer form, the only prefix is the full one, and it is `0`.

So `St₂` satisfies both hypotheses on every refinement, consistent with its
square-integrability.

**Trivial representation.** The upper norm is `(|a₁|/|a₂|)^(-1/2)`. At
`a₁ = ϖ`, `a₂ = 1` it equals `q^(1/2) > 1`, so both the weak and the strict
upper conditions fail. Its proper opposite prefix `1/2` is positive, so the
consumer hypothesis fails too. This is consistent with the trivial
representation not being square-integrable.

## Original sources and the product-Levi translation

- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
  d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.
  Literature ID `waldspurger-2003-plancherel`, SHA256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF
  page = printed page − 234.
  - §III.1, printed p.263 (PDF29), assumes an admissible representation with a
    unitary central character. It defines square-integrability as square
    integrability of all coefficients on `A_G \ G`.
  - Proposition III.1.1 states that the following are equivalent:
    - (i) `π` is square-integrable;
    - (ii) `Re(χ) ∈ ⁺a_P^(G*)` for every semi-standard parabolic `P` and every
      `χ ∈ Exp(π_P)`;
    - (iii) the same condition for every proper maximal standard `P`.

    The proposition cites "[C, Théorème 4.4.6]".
  - §I.1, pp.239–240 (PDF5–6), defines the open cone `⁺a_P^(G*)` of
    combinations `sum_(α ∈ Δ_P) x_α α` with all `x_α > 0`. It also fixes the
    sign `|χ(g)|_F = q^(−⟨χ, H_G(g)⟩)`.
  - §I.3, p.243 (PDF9), defines exponents as the generalized eigencharacters
    of `A_M` on the Jacquet module normalized by `δ_P^(-1/2)`.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft of 1 May 1995. Literature ID
  `casselman-1995-admissible-representations`, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`; printed
  and PDF pages coincide.
  - Theorem 4.4.6, p.45: an admissible `ω`-representation is square-integrable
    if and only if:
    - (a) `ω` is unitary;
    - (b) for every `Θ ⊆ Δ` and every central character `χ` of `π` with respect
      to `P_Θ`, `|χ δ_∅^(-1/2)(a)| < 1` for all `a ∈ A_Θ^- ∖ A_∅(O) A_Δ`.

    The full quotation and the surrounding definitions are recorded in
    [`SquareIntegrableExponentStatement`](SquareIntegrableExponentStatement.md).
  - The proof of Theorem 4.4.6 (p.45) applies Theorem 4.3.4 and Corollary
    4.4.5. Corollary 4.4.5, p.44, is the criterion for `|F|^p` to be
    integrable modulo `Z_G` on a chamber cell `K · A_∅^-(ε) · K`.
- A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
  groups*, Princeton University Press and University of Tokyo Press, 1979.
  Literature ID `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`; PDF page
  = printed page + 6.
  - Theorem 4.5.10, pp.188–189 (PDF194–195), checked as page images, concerns
    a function `f ∈ A(G, η)` with `η` a unitary character of `Z`. It states
    that `∫_(G/Z) |f|² < ∞` is equivalent to:
    - (2) `f` is tempered, that is `f ∈ _w A(G)` (the tempered elements of
      `A(G)`, defined on printed p.185, PDF191), and its weak constant term
      `_w f_P` vanishes for every p-pair `(P, A) ≠ (G, Z)`;
    - (3) for every semi-standard p-pair and every exponent `χ` of `f`, the
      real exponent `γ` (with `|χ(a)| = q^⟨γ, H_P(a)⟩`) is
      `−sum_i c_i α_i` with all `c_i > 0`;
    - (4) a bound `c Ξ(x)(1+σ(x))^(−r)` for every `r > 0`.
  - Silberger's sign convention for `H_P` is not re-derived here. This source
    is a cross-reference for the shape "square-integrable ⟺ strict exponent
    inequalities". The Lean signs are fixed by Casselman's form and by the GL₂
    check above.

The cited passages were read directly. The formula-bearing Silberger pages
were checked as images. No errata notes for these sources were found in the
project or public notes.

### Applying the criterion to `M_C`

The criterion is applied to the reductive group `G = M_C`. The following
identifications are derived standard computations; they are not literal
statements in the sources.

- **Parabolics.** The standard parabolics of `M_C` (for the upper Borel of each
  factor) are products of standard parabolics of the factors. They are exactly
  the parabolics `P_D ∩ M_C` of the refinements `D`. The trivial refinement is
  `Θ = Δ`. The proper maximal ones split exactly one outer block into two inner
  blocks.
- **Hypothesis strength.** The Lean hypotheses quantify every refinement, which
  is Casselman's "every `Θ`". This includes Waldspurger's condition (iii), so
  the sufficiency direction (iii) ⇒ (i) applies.
- **Centre.** The centre of `M_C` is the group of block scalars, and it is
  split. So `A_G = Z(M_C)`, and Waldspurger's quotient `A_G \ G` is the
  Library's `M_C ⧸ Subgroup.center M_C`. Casselman's `ω`-representation is
  `HasScalarCharacter`, and his condition (a) is the unitarity hypothesis.
- **Split components.** The split centre of the Levi of `P_D ∩ M_C` is the
  flattened block scalars. They are reached through `B.blockScalarLevi` and
  `flattenedLeviEquiv`.
- **Exponents.** Exponents are generalized eigencharacters with a uniform
  power, as in Casselman Prop. 2.1.9. They have open kernel automatically for
  admissible `S`. The normalizations agree with Waldspurger I.3. For block
  scalars, Casselman's `δ_∅` agrees with `δ_D` on the split centre of the Levi
  of `P_D ∩ M_C`.
- **Chamber.** The simple roots of `P_D ∩ M_C` take the values
  `a_(e(j,k)) / a_(e(j,k+1))` on block scalars. So `A_Θ^-` is the blockwise
  `Monotone` set. With Waldspurger's sign of `H`, `Re χ ∈ ⁺a_P^(G*)` means
  `‖χ(a)‖ ≤ 1` on this set, with strict inequality whenever some
  `|α(a)| < 1`.
- **Removed directions.** A fine block scalar lies in `A_∅(O) A_Δ` (units times
  the centre of `M_C`) exactly when its absolute values are constant on every
  outer block. This is the non-constancy clause of the core hypothesis.
- **Coefficients.** "All coefficients" means the coefficients
  `g ↦ ℓ(π(g) v)` with `ℓ` a smooth functional, which is how
  `IsSquareIntegrableModCenter` reads them.
- **Haar measures.** The sources fix one Haar measure. Their proofs use only
  invariance and Cartan double-coset volumes, which hold for every Haar
  measure on the quotient. The all-measure conclusion is therefore part of the
  proof obligation, not an additional assumption.

The statement is also less general than the sources in one respect.
Irreducibility of `S` is assumed although Casselman does not need it, which
only strengthens the hypotheses. It matches the tempered pair and the
intended consumer.

For `C = (n)`, the core form is the sufficiency direction of the published
`GL_n` criterion
[`GLSquareIntegrableExponentCriterionStatement`](SquareIntegrableExponentStatement.md),
transported along the one-block Levi `C.Levi F.Carrier ≅ GL_n(F)`. That
comparison is derived and is not asserted in Lean.

## Intended consumer

The consumer form is applied in the proof of
`Langlands.GLWeaklyCriticalTopLayerL2Statement` (Silberger Corollary 4.5.11),
task `ecd53630-f80d-4513-82dc-99e03b56488f`. Its proof uses this declaration
with this name, universe order `{uF,uV}`, hypothesis order and prefix shape.

## Dependencies and remaining scope

The only import is `ProductLeviTemperedSufficiencyStatement`. Through it come:

- `IsSquareIntegrableModCenter` and `UnitaryCentralCharacter`;
- `HasScalarCharacter`;
- `IsGeneralizedEigencharacter` and `IsRealPartOf`;
- the actual upper and opposite refined Jacquet quotients and their
  normalized actions;
- the constructed flattened Levi and index equivalences.

The following are not added to either target:

- a tensor-product presentation of `S`;
- a cuspidal-support hypothesis;
- a temperedness hypothesis;
- a restriction to finitely many or to maximal refinements;
- a supplied coefficient bound.

The file proves nothing. In particular, it does not prove Casselman's
criterion, the strict chamber coefficient bound, the analytic passage to
`L²`, the Weyl/spectral adapter between the two forms, or the identification
of the block scalars with the full centre. Both declarations compile in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. They are `Prop`-valued, have
level parameters `uF uV`, and use only the standard axioms.
