# An Euler-coefficient degree on the endomorphisms of an abelian variety

Lean module: `Langlands.AbelianScheme.EndomorphismEulerDegree`, namespace
`Langlands.AbelianScheme.EndomorphismEulerDegree`.

Let `A` be an abelian scheme of relative dimension `g` over a field `k`, and let `L` be a fixed
ample line bundle on `A`. For an endomorphism `α`, the module defines the
*Euler-coefficient degree*
`δ(α) = coeff_g χ(α^*L^{⊗m}) / coeff_g χ(L^{⊗m})`.
Here `coeff_g` is the `g`-th coefficient of the Euler polynomial in `m`. The main theorem,
`endomorphismEulerDegree_spec`, states two properties. First, `δ` is the degree on isogenies.
Second, along every line `n ↦ n • φ + ψ`, `δ` is a polynomial in `n` of natural degree at most
`2 * g`. This is the content of the statement
`Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialStatement`.
That statement is stated for algebraically closed fields; the present module works over any
field. The one-line proof of the statement itself is
`Langlands.AbelianScheme.endomorphismDegreeLinePolynomial`, in the separate module
`Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialProof`.

## Provenance

The overall argument is that of Milne, *Abelian Varieties*, author revision of January 2,
2022 (registered source `milne-abelian-varieties-1986-author-2022`), Proposition 12.4, p. 21.
Milne computes `deg(nφ + ψ) · (D^g) = (D_n^g)` with `D_n = (nφ + ψ)^* D`. He shows that `D_n`
is quadratic in `n` by the theorem of the cube (Corollary 6.5). The present module makes two
changes, both internal to this project:

- The intersection number `(D^g)` is replaced by the `g`-th coefficient of the Euler
  polynomial `m ↦ χ(D^{⊗m})`. Its behaviour under finite flat maps is the published Library
  theorem `finiteFlatEulerPolynomialCoefficient`. That `L` has nonzero `g`-th coefficient is
  the published `smoothProperLineBundleEulerPolynomial` for ample `L`.
- The polynomiality in `n` is derived from the quadratic shape of the Picard classes. For
  this, the Euler characteristic is used only as a function on the Picard group that is
  polynomial in each variable separately (the published `coherentEulerPolynomial_eval`). The
  module `Langlands.Algebra.SeparatelyPolynomialQuadraticLine` then turns this into the bound
  `2 * g`.

`δ` is not required to vanish on non-isogenies. It need not equal Milne's degree there.

The Picard helpers `tensorObj_invertible`, `lineBundle_pullback_invertible`,
`tensorPow_invertible`, `picard_tensorObj` and `picard_tensorPow` restate, publicly, small facts
that the Library proves privately in `Langlands.AbelianScheme.FieldMultiplicationPullbackOfCube`.
Throughout, Picard classes live in `Langlands.CategoryTheory.PicardGroup` of the category of
`O_X`-modules. That group needs no hypothesis on pullbacks preserving tensor products.

## Declarations

### Picard helpers

- `tensorObj_invertible`: the explicit (localized) tensor product `tensorObj M N` of
  tensor-invertible modules is tensor-invertible (transport along `localizedTensorIso`).
- `lineBundle_pullback_invertible f L`: the module pullback of a line bundle is
  tensor-invertible (`locallyFreeRankOneIffTensorInvertible` and `IsLocallyFreeRankOne.pullback`).
- `tensorPow_invertible`: explicit tensor powers `tensorPow M n` of a tensor-invertible module
  are tensor-invertible (induction on `n`).
- `picard_tensorObj`: `ofObject (tensorObj M N) = ofObject M + ofObject N`
  (`PicardGroup.ofObject_tensor` and `localizedTensorIso`).
- `picard_tensorPow`: `ofObject (tensorPow M n) = n • ofObject M` (induction on `n`, using
  `PicardGroup.ofObject_unit` and `picard_tensorObj`).

### `lineOf x` (definition) and `lineBundle_hasFiniteCohomology`

`lineOf x` is the chosen representative `PicardGroup.representative x` of a Picard class,
regarded as a line bundle. `lineBundle_hasFiniteCohomology`: a line bundle on a scheme proper
over a field has finite cohomology (`hasFiniteCohomology_of_coherent`).

### `eulerClass f x` (definition) and `eulerClass_ofObject`

For `f : X ⟶ Spec K` proper, `eulerClass f x : ℚ` is the Euler characteristic of `lineOf x`.
`eulerClass_ofObject`: for every tensor-invertible `M` with finite cohomology,
`eulerClass f (ofObject M) = χ(M)`. Proof: `M` is isomorphic to the representative of its class
(`PicardGroup.ofObject_eq_iff`, `ofObject_representative`), and isomorphic modules have equal
Euler characteristics (`eulerCharacteristic_eq_of_iso`).

### `exists_eulerClass_nsmul_add`

**Statement.** Let `X` be proper over a field, noetherian and separated, with
`topologicalKrullDim X ≤ g`. For Picard classes `a` and `c` there is a rational polynomial `p`
with `p.natDegree ≤ g` and `eulerClass f (x • a + c) = p.eval x` for all natural `x`.

**Proof.** Take `p = coherentEulerPolynomial f (lineOf c).obj _ (lineOf a) g`. By
`coherentEulerPolynomial_eval` (with the support bound from
`HasSupportDimensionLT.of_topologicalKrullDim_le`), `p.eval x` is
`χ(lineOf c ⊗ (lineOf a)^{⊗x})`. By `picard_tensorObj` and `picard_tensorPow` the class of that
module is `x • a + c`, and `eulerClass_ofObject` finishes.

### `eq_of_second_difference` and `nsmul_quadratic`

Two identities in an additive commutative group. `eq_of_second_difference`: if
`q (n+2) + q n = q (n+1) + q (n+1) + P` for all `n`, then
`q n = q 0 + n • (q 1 - q 0) + C(n, 2) • P`. Proof: induction on `n` (two consecutive values
at a time), with `C(n+1, 2) = n + C(n, 2)`.
`nsmul_quadratic`: `m • (a + n • b + C • c) = (m * C) • c + (m * n) • b + m • a`.

### `ampleLineBundle A` (definition), `ampleLineBundle_isAmple`

A chosen ample line bundle on `A`, from the published `fieldAmpleExistence`.

### `eulerPolynomial A g α` and `endomorphismEulerDegree A g α` (definitions)

`eulerPolynomial A g α = lineBundleEulerPolynomial A.X.hom (α^* L) g`, the Library's Euler
polynomial (truncated in degree `g`) of the line-bundle pullback of the chosen `L` along the
underlying morphism of `α`. `endomorphismEulerDegree A g α` is
`(eulerPolynomial A g α).coeff g / (lineBundleEulerPolynomial A.X.hom L g).coeff g`.

### `eulerCharacteristic_congr`

The Euler characteristic depends on the structure morphism only up to equality of morphisms
(proof by `subst`).

### `coeff_lineBundleEulerPolynomial_ne_zero`

**Statement.** If `A.HasRelativeDimension g`, then the `g`-th coefficient of
`lineBundleEulerPolynomial A.X.hom L g` is nonzero.

**Proof.** `smoothProperLineBundleEulerPolynomial` gives, for ample `L`, a polynomial `P` with
`P.eval n = χ(L^{⊗n})`, `P.natDegree = g` and positive leading coefficient. The Library's
polynomial agrees with `P` at all natural numbers (`lineBundleEulerPolynomial_eval`, using
`field_topologicalKrullDim`), hence equals `P` (`Polynomial.eq_of_infinite_eval_eq`).

### `endomorphismEulerDegree_isogeny`

**Statement.** If `A.HasRelativeDimension g` and `β` is an isogeny, then for every point `y`
of `A.X.left`, `endomorphismEulerDegree A g β = (hom β).finrank y`.

**Proof.** `isIsogeny_iff` makes the underlying morphism finite and flat. Since `β` is a
morphism over the base, `hom β ≫ A.X.hom = A.X.hom`. The published
`finiteFlatEulerPolynomialCoefficient` applies with `P` the Euler polynomial of `L` and `Q` that
of `β^*L`. Their evaluations are given by `lineBundleEulerPolynomial_eval`; the structure
morphism is transported by `eulerCharacteristic_congr`. It gives
`Q.coeff g = finrank y * P.coeff g`. Dividing by `P.coeff g ≠ 0`
(`coeff_lineBundleEulerPolynomial_ne_zero`) finishes.

### `classOf A α` (definition), `classOf_cube`, `classOf_nsmul_add`

`classOf A α` is the Picard class of the module pullback of `L` along `hom α`.

`classOf_cube`: for endomorphisms `a₁ a₂ a₃`,
`cl(a₁+a₂+a₃) + (cl a₁ + (cl a₂ + cl a₃)) = cl(a₁+a₂) + (cl(a₁+a₃) + cl(a₂+a₃))`. Proof: the
published theorem of the cube `fieldCubePullback`, applied to the three underlying morphisms
and `L`, gives an isomorphism of the corresponding explicit tensor products. Its Picard classes
are expanded by `picard_tensorObj`.

`classOf_nsmul_add`: `cl(n • φ + ψ) = cl(ψ') + n • (cl(1 • φ + ψ) - cl(ψ')) + C(n, 2) • P`, where
`ψ' = 0 • φ + ψ` and `P = cl(φ + φ) - cl φ - cl φ`. Proof: `classOf_cube` with
`a₁ = n • φ + ψ` and `a₂ = a₃ = φ` gives the second-difference relation, and
`eq_of_second_difference` applies.

### `exists_endomorphismEulerDegree_line`

**Statement.** If `A.HasRelativeDimension g`, then for all endomorphisms `φ` and `ψ` there is
`R : ℚ[X]` with `R.natDegree ≤ 2 * g` and
`endomorphismEulerDegree A g (n • φ + ψ) = R.eval n` for all natural `n`.

**Proof.** Put `q n = cl(n • φ + ψ)`, `P = cl(φ + φ) - cl φ - cl φ`, `D = q 1 - q 0` and
`G x y z = eulerClass A.X.hom (x • P + y • D + z • q 0)`.

1. `G` is polynomial of natural degree at most `g` in each variable separately: apply
   `exists_eulerClass_nsmul_add` with `a = P`, `D` or `q 0` and `c` the sum of the other two
   terms (`abel` rearranges). The dimension bound is `field_topologicalKrullDim`.
2. Let `E n = eulerPolynomial A g (n • φ + ψ)`. For natural `m`, `(E n).eval m` is
   `χ(M^{⊗m})` with `M` the pullback of `L` along `n • φ + ψ`
   (`lineBundleEulerPolynomial_eval`). By `picard_tensorPow`, `classOf_nsmul_add` and
   `nsmul_quadratic`, the class of `M^{⊗m}` is
   `(m * C(n, 2)) • P + (m * n) • D + m • q 0`. So `eulerClass_ofObject` gives
   `(E n).eval m = G (m * C(n, 2)) (m * n) m`.
3. `exists_coeff_eq_eval_of_quadraticLine` (module `SeparatelyPolynomialQuadraticLine`, with
   `D = g`) gives `R` with `R.natDegree ≤ 2 * g` and `(E n).coeff g = R.eval n`.
4. The witness is `C c⁻¹ * R`, where `c` is the `g`-th coefficient for `L`. Its natural degree
   is at most that of `R`.

### `endomorphismEulerDegree_spec`

**Statement.** If `A.HasRelativeDimension g`, then the conjunction holds:
`∀ β, IsIsogeny β → ∀ y, endomorphismEulerDegree A g β = (hom β).finrank y`, and
`∀ φ ψ, ∃ R, R.natDegree ≤ 2 * g ∧ ∀ n : ℕ, endomorphismEulerDegree A g (n • φ + ψ) = R.eval n`.
This is the body of `EndomorphismDegreeLinePolynomialStatement` with
`δ = endomorphismEulerDegree A g`. The base here is `Spec (CommRingCat.of k)` over any field.

**Proof.** Pair `endomorphismEulerDegree_isogeny` and `exists_endomorphismEulerDegree_line`.
