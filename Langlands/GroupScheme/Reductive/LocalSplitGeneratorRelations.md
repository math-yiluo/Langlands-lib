# Big-cell gluing from generator relations

This internal derived criterion reduces big-cell gluing to relations for right
translation by the generators. The base ring is arbitrary and may have nilpotents.
It replaces the matching point-group homomorphisms assumed by the imported
closed-residue gluing criterion with a pointwise relation condition on
cell points.

`LocalSplitGeneratorRelationIsomorphismStatement.{u}` concerns two reductive group
schemes `G` and `H` over `Spec R`, with:

- a common coordinate split torus `i`, `i'` with character lattice indexed by `I`;
- additive-group families `u`, `u'` indexed by the same type `J`;
- exponent vectors `ch : J → I → ℤ`, common to both groups;
- finite root enumerations `neg`, `pos`;
- open-immersion cell maps `Ω = cellMap i u neg pos` and
  `Ω' = cellMap i' u' neg pos`.

Both maps have the same source `𝔾ₐᵐ × T × 𝔾ₐⁿ`. For a torus point `t`, write
`χ_α(t)` for the value at `t` of the exponent character with exponent vector
`ch α` (`VectorGroup.charValue` of `splitTorus.exponentCharacter`). This value
is a unit. The statement has three hypotheses:

- **torus equivariance in `G`:** for every `α : J`, every test object `Z` over
  `Spec R`, every torus point `t` and every global function `c` on `Z`,
  `i(t) · u_α(c) · i(t)⁻¹ = u_α(χ_α(t) · c)`;
- **torus equivariance in `H`:** the same identity for `i'` and `u'`, with the
  same characters `χ_α`;
- **root relations:** the following holds for every commutative local ring
  `A : Type u` with separably closed residue field, every structure map
  `s : Spec A → Spec R`, all cell-source points `x`, `y` over `s`, every
  `α : J` and every global function `c`. If `Ω(x) · u_α(c) = Ω(y)` in `G`,
  then `Ω'(x) · u'_α(c) = Ω'(y)` in `H`.

The conclusion is an isomorphism `ψ : G ≅ H` with `Ω ≫ ψ = Ω'`. The module
proves this proposition at full universe as
`localSplitGeneratorRelationIsomorphism`, by applying
`LocalSplitCell.exists_iso_of_rootRelations`.

The module also proves a more general core theorem,
`LocalSplitCell.exists_iso_of_generatorRelations`. It does not assume torus
equivariance. Instead it takes two hypotheses, `LocalSplitCell.TorusRelations`
and `LocalSplitCell.RootRelations`, both over the same local test rings and
cell points as above:

- **torus relations:** for every torus point `t`, if `Ω(x) · i(t) = Ω(y)` in
  `G`, then `Ω'(x) · i'(t) = Ω'(y)` in `H`;
- **root relations:** as above.

## Proof

**Right-good pairs.** A pair `(g, h)` of points of `G` and `H` over the same
test object `Z` is called right-good (`RightGood`) if the following holds for
every local test ring `B` with separably closed residue field, every map
`f : Spec B → Z` over `Spec R` and all cell points `x`, `y` over `B`: if
`Ω(x) · f*g = Ω(y)`, then `Ω'(x) · f*h = Ω'(y)`. The proof first establishes
some basic facts:

- Right-good pairs are stable under pullback.
- `(1, 1)` is right-good because `Ω` is a monomorphism.
- Inverting both members of a right-good pair swaps `x` and `y`, so it again
  gives a right-good pair.
- By `HasCellFactors`, every point `g` over a local test ring `A` has cell
  points `p`, `q` with `Ω(p) · g = Ω(q)`. For `G` this is the imported
  inverse-first factorization `exists_inverse_cell_factors`. As a result, a
  right-good partner of `g` over `A` is unique: both partners `h` and `h'`
  satisfy `Ω'(p) · h = Ω'(q) = Ω'(p) · h'`.

**Products (`RightGood.mul`).** This is a generic-line argument. Suppose
`(g₁, h₁)` and `(g₂, h₂)` are right-good and `Ω(x) · f*g₁ · f*g₂ = Ω(y)` over
`B`. Choose `p`, `q` with `Ω(p) · f*g₁ = Ω(q)`. Over the polynomial ring
`B[X]`, interpolate the coordinates linearly, `a(1 - X) + bX`, from `x` at
`X = 0` to `p` at `X = 1`. The interpolated torus coordinates are units in
three local rings:

- the local ring `AtPoint B 0` of the line at the closed point `X = 0`;
- the local ring `AtPoint B 1` at the closed point `X = 1`;
- the local ring `Generic B` at the generic point of the closed fibre.

So the interpolation defines cell points `z₀`, `z₁` and `z''` over these rings
and their extensions (`linePoint`). Evaluation `evalAt a` is a local section,
and it specializes `z₀` to `x` and `z₁` to `p`.

The products `Ω(z₀) · g₁ · g₂` and `Ω(z₁) · g₁` send the closed point into the
open cell. So the imported lifting lemma `exists_lift_of_localPoint_closedPoint_mem`
gives cell points `c₀` over `AtPoint B 0` and `d₁` over `AtPoint B 1`
representing them.

Next, use the imported closed-residue extension to choose a faithfully flat
local `Generic B`-algebra `B''` with algebraically closed residue field. Over
`B''`, apply the right-good hypotheses twice: first for `g₁` from `z''` to
`d₁`, then for `g₂` from `d₁` to `c₀`. This gives the `H`-relation for
`h₁ · h₂` over `B''`.

The relation then descends to `AtPoint B 0`. The composite
`AtPoint B 0 → Generic B → B''` is injective, since generization is injective
by McCoy's theorem (a polynomial with a unit coefficient is a non-zero-divisor)
and `B''` is faithfully flat. Because `H` is affine,
`CellGluing.hom_ext_of_injective_specMap` applies. Specializing along `evalAt 0`
gives the relation over `B`. No passage to residue fields occurs, so nilpotent
structure is retained.

**Generators.** In the core theorem, the torus and root relation hypotheses
say exactly that
`(t ≫ i, t ≫ i')` and `(u_α(c), u'_α(c))` are right-good; root points use
`comp_rootPoint`. By induction on the list, ordered products of root points are
right-good. By `comp_cellMap`, so are the pairs `(Ω(x), Ω'(x))` for all cell
points `x`. Every point `g = Ω(x)⁻¹ · Ω(y)` over a local test ring therefore
has the right-good partner `Ω'(x)⁻¹ · Ω'(y)` (`exists_rightGood`).

**Matching homomorphism and gluing.** For each local test ring `A`, choose the
unique partner of every `A`-point to obtain a function
`Ψ : G(A) → H(A)`. Uniqueness, together with the product and unit lemmas, makes
`Ψ` a monoid homomorphism. Uniqueness also shows that `Ψ` matches the torus
and root points. The imported `pointHom_bijective_of_matches` makes `Ψ`
bijective. The imported `exists_iso_of_closedResidueLocalRingPoints` then
glues these equivalences to the isomorphism with exact cell agreement.

**Torus relations from equivariance.** The proved proposition uses the
torus-equivariance hypotheses only to derive the torus relations
(`torusRelations_of_equivariant`). Equivariance applied to `χ_α(t)⁻¹ · c`
gives `u_α(c) · i(t) = i(t) · u_α(χ_α(t)⁻¹ · c)` (`rootPoint_mul_torus`). By
induction, an ordered product of root points also moves past `i(t)`, with each
coordinate multiplied by the inverse of its character value
(`orderedProduct_mul_torus`).

Let `x` have coordinates `(v, τ, w)`. The coordinate bijection of the cell
source gives a cell point `z` with coordinates `(v, τ · t, w')`, where
`w'_k = χ_{pos k}(t)⁻¹ · w_k`. Expanding `Ω(x) = U⁻(v) · i(τ) · U⁺(w)` and
moving `i(t)` to the left of `U⁺(w)`, where `i(τ) · i(t) = i(τ · t)`, gives `Ω(x) · i(t) = Ω(z)`
(`comp_cellMap_mul_torus`). If `Ω(x) · i(t) = Ω(y)`, then `z = y` because `Ω`
is a monomorphism. The same computation in `H` uses the same characters, so
it gives `Ω'(x) · i'(t) = Ω'(z) = Ω'(y)`.

## Provenance and scope

This is an internal derived criterion. It is in the spirit of the
generator-and-relation homomorphism criteria used in the proofs of the
Isomorphism Theorem (SGA 3, Exp. XXIII; B. Conrad, *Reductive group schemes*,
§6.2). The generic-line argument above is an explicit construction of this
module, not a transcription of a published proof.

The criterion does not verify torus equivariance or the root relations for
any pair of groups. Torus equivariance is the defining property of root-group
parametrizations, but the statement assumes it. Verifying the root relations
requires rank-one relations and commutator relations between root groups. The
criterion also does not prove the local split Isomorphism Theorem.
