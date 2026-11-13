# Proof of unramified-twist surjectivity across a rank-one wall

This module proves the Library statement
`Langlands.Plancherel.WallUnramifiedTwistSurjectivityStatement`, exactly as stated and at an
arbitrary universe `u`. The theorem is `Langlands.Plancherel.wallUnramifiedTwistSurjectivity`.

## Statement proved

Work over a nonarchimedean local field `k`. Let `G` be connected reductive, with rational Levis
`L ⊂ Q ⊂ M ⊂ P ⊂ G` and `L ⊂ Q₁ ⊂ M₁ ⊂ P₁ ⊂ G`, where:

* the two embeddings of `L` into `G` agree;
* `Q₁` is a maximal proper parabolic of `M₁`;
* a split component `A_M → M` of `M` factors through `L`, and its image is not central in `M₁`.

Then every unramified character `φ` of `L(k)` can be written as
`φ = ψ|_L · χ|_L` with `ψ` an unramified character of `M(k)` and `χ` one of `M₁(k)`. The
restrictions go along `l ≫ q : L → M` and `l₁ ≫ q₁ : L → M₁`.

## The Lean proof

The proof introduces all the binders of the statement, including `φ`, and combines two
published Library theorems. It proves nothing new about structure or analysis.

1. **Instances.** The statement puts `IsAffine` instances for `M`, `L`, `M₁` and the
   rational-point topologies inside the proposition as `haveI`/`letI`. `intro` zeta-reduces
   them. The proof therefore restates the three `IsAffine` facts with the same terms the
   statement uses (`isAffine_of_isAffineHom` applied to the affineness of the connected
   reductive Levis). `IsAffine` is a `Prop`, so these instances agree with the statement's
   by proof irrelevance. The topologies are the canonical `rationalPointTopology` instances
   used by the analytic theorem, so they match by definition. The analytic theorem also
   needs `LocallyOfFiniteType M.X.hom` and `LocallyOfFiniteType M₁.X.hom`. These come from
   `IsConnectedReductive.smooth` for `M` and `M₁` (smooth morphisms are locally of finite
   type, by instance).

2. **Structural input:** `Langlands.GroupScheme.WallCharacterSum.exists_nsmul_eq_restrict_add`
   (module `Langlands.GroupScheme.Rational.WallCharacterSum`). Its hypotheses are exactly the
   structural hypotheses of the statement. It shows that for every rational character `χ` of
   `L` there are `n > 0` and rational characters `ψ` of `M` and `ψ₁` of `M₁` with
   `n • χ = characterRestrict (l ≫ q) ψ + characterRestrict (l₁ ≫ q₁) ψ₁`.

3. **Analytic input:**
   `Langlands.Plancherel.rationalUnramifiedCharacterProductRestrict_surjective_of_nsmul`
   (module `Langlands.Representation.Plancherel.RationalJointRestriction`). Given this
   rational spanning property, it shows that the product-restriction homomorphism
   `rationalUnramifiedCharacterProductRestrict (l ≫ q) (l₁ ≫ q₁)` is surjective. This
   homomorphism sends `(ψ, χ) ↦ rationalUnramifiedCharacterRestrict (l ≫ q) ψ *
   rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ`.

4. Applying surjectivity to `φ` gives a pair `(ψ, χ)`. The equation it returns is the
   statement's equation read right to left, by the defining `simp` lemma (it holds by
   `rfl`), so `h.symm` closes the goal.

## Provenance

This is internal, derived material: it composes two published Library results and adds
nothing else. For the mathematical background (finite index of `X*(M)|_L + X*(M₁)|_L` in
`X*(L)`, and divisibility of `ℂˣ` for extending characters), see the Markdown of the two
modules cited above.
