# Statement: descent of a finite étale algebra from functorial chart isomorphisms

`Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement.{u}` is faithfully flat descent
of a finite étale algebra. The descent datum is given in functorial form: isomorphisms over
every test algebra and every pair of chart maps.

## The statement

All rings lie in one universe `u`. Let `A → A'` be an étale ring map with
`Spec A' → Spec A` surjective, so `A'` is faithfully flat over `A`. Let `C` be a finite,
projective, étale `A'`-algebra. For an `A`-algebra `T` (an object of
`CommAlgCat (CommRingCat.of A)`) and an `A`-algebra map `f : A' → T`, write
`C_f := T ⊗[A', f] C`. This is the tensor product for the `A'`-algebra structure
`f.toRingHom.toAlgebra` on `T`, regarded as a `T`-algebra through its left factor.

The data are, for every `T` and all `f₁ f₂ : A' →ₐ[A] T`, `T`-algebra isomorphisms
`θ T f₁ f₂ : C_{f₂} ≃ₐ[T] C_{f₁}`. They are assumed to satisfy:

- **identity:** `θ T f f = AlgEquiv.refl`;
- **cocycle:** `(θ T f₂ f₃).trans (θ T f₁ f₂) = θ T f₁ f₃`;
- **naturality:** for every map of `A`-algebras `χ : T ⟶ T₁` and every `x ∈ C_{f₂}`,
  `θ T₁ (χ ∘ f₁) (χ ∘ f₂) (χ ⊗ id) x = (χ ⊗ id) (θ T f₁ f₂ x)`. Here `χ ⊗ id : C_f → C_{χ ∘ f}`
  is `Algebra.TensorProduct.map` of `χ`, viewed as a map of `A'`-algebras from `(T, f)` to
  `(T₁, χ ∘ f)`, and of the identity of `C`.

The conclusion is that there are a finite, projective, étale `A`-algebra `B` and an
`A'`-algebra isomorphism `e : A' ⊗[A] B ≃ₐ[A'] C` such that, for every `T`, `f₁`, `f₂` and
`b ∈ B`, the isomorphism `θ T f₁ f₂` sends `1 ⊗ e (1 ⊗ b) ∈ C_{f₂}` to `1 ⊗ e (1 ⊗ b) ∈ C_{f₁}`.

## Source and provenance

This is a functorial form of effective descent for affine schemes along a faithfully flat ring
map, together with descent of finiteness, projectivity and étaleness. See the Stacks Project:
Proposition 35.3.9 (Tag 023N), Lemma 35.37.1 (Tag 0245), and descent of properties of
algebras, Section 35.23. The isomorphisms `θ T f₁ f₂` are the values of a descent datum on all
pairs of points of `Spec A'` with values in `T`. The classical descent datum over
`A' ⊗[A] A'` is the case `T = A' ⊗[A] A'`, with `f₁`, `f₂` the two inclusions. Naturality and
the cocycle condition over a single `T` give the classical cocycle over `A' ⊗[A] A' ⊗[A] A'`.

The statement is an internal interface. It is the form in which the canonical coefficient
isomorphisms `WeilChart.chartAlgEquiv` (module
`Langlands.GroupScheme.Reductive.WeilChartAlgebra`) arise in the proof of
`AffineWeilPairSingleChartDescentStatement` (Conrad, *Reductive group schemes*, 2014, proof of
Proposition 6.4.4). It contains no group schemes.

## Why the statement should hold

Put `T = A' ⊗[A] A'` with the two inclusions. Then `θ` is an isomorphism between the two base
changes of `C` to `A' ⊗[A] A'`. Naturality and the cocycle condition give the cocycle condition
over the triple tensor product, and the identity condition gives the unit condition. Faithfully
flat descent of algebras (for example in coaction form,
`FaithfullyFlatCoalgebraDescent.isPushout_eqLocus_of_groupoid` in the Library) produces `B` as
the subring of `θ`-invariant elements, with `A' ⊗[A] B ≅ C`. Finiteness, étaleness and hence
projectivity descend along the faithfully flat map `A → A'`. The invariance of `1 ⊗ e (1 ⊗ b)`
holds for the universal pair of chart maps by construction, and for every other pair by
naturality.
