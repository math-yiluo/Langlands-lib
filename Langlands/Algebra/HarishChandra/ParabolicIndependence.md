# Proof of independence of the parabolic for the normalized Levi component

Module `Langlands.Algebra.HarishChandra.ParabolicIndependence`, namespace
`Langlands.Algebra.HarishChandra`.

```lean
theorem parabolicIndependence : ParabolicIndependenceStatement.{v, w}
```

The theorem proves equality in `U(𝔪)` of the shifted components `τ_{λᵢ}(yᵢ)` of a central
element `z`. Here `yᵢ` is supplied by the congruence `z - j(yᵢ) ∈ 𝔳ᵢ U(𝔤)`, where
`j : U(𝔪) → U(𝔤)` is induced by `ι`. The shift `τ_{λᵢ}` sends `Y` to `Y + λᵢ(Y)` and
`2 λᵢ(Y)` is the trace of `ad ι(Y)` on `𝔳ᵢ`.

## A common Cartan subalgebra

In a simultaneous weight basis, the kernel of `ad Xᵢ` is spanned by the vectors whose weight
vanishes at `Xᵢ`. The common zero set therefore gives `range ι = ker ad X₂`.
`mem_center_of_sub_mem_generatorRightIdeal` shows that each `yᵢ` is central. It uses injectivity
of `j` and disjointness of its image from `𝔳ᵢ U(𝔤)`.

`IsSplitCartan.comap` gives a split Cartan subalgebra `K = ι⁻¹(𝔥)` of `𝔪`, identified with `𝔥`
by `comapCartanEquiv`. Choose `Y ∈ 𝔥` with `Re χ(Y) ≠ 0` for each Levi root `χ`.
Choose `ε > 0` with `ε |Re χ(Y)| < 1` for each ambient weight. Since the values of `χ(Xᵢ)` are
integers, `WeightBasis.re_shift` shows that the positive roots at `Xᵢ + εY` are precisely the
roots in `𝔳ᵢ` together with the Levi roots positive at `Y`. Both perturbed elements are
real-regular for `𝔤`, and the lift `Y_K` of `Y` is real-regular for `𝔪`.

## Comparison by Verma right ideals

Write `R_X(ν)` for the right ideal `vermaIdeal` at `X` with parameter `ν` in the Cartan
subalgebra under consideration. Let `κ₀` be the half-sum of the Levi roots positive at `Y`.
Fix a linear form `μ` on `K`. By `exists_sub_mem_vermaIdeal`, each `yᵢ` is congruent to a
scalar `sᵢ` modulo `R_{Y_K}(μ + λᵢ|_K)`. The lemma `sub_mem_vermaIdeal_of_levi` transports this
congruence to `𝔤`. The Levi positive generators and the radical generators map into the
positive part of the ambient ideal. The diagonal trace on the positive eigenspaces identifies
`λᵢ|_K` with their half-sum of roots, so the parameter of the ambient ideal is
`μ - κ₀ + ρ_{Xᵢ+εY}`, with `μ` transported to `𝔥`. Thus `z` is congruent to `sᵢ` modulo this
ambient ideal.

`WeightBasis.sub_mem_vermaIdeal_rho` transports the first ambient congruence to the second
Borel, with `μ - κ₀` fixed. It compares adjacent positive systems by the rank-one singular
vectors in `VermaWallCrossing` and extends the comparison along a generic segment.
Uniqueness of the scalar modulo the second ambient ideal gives `s₁ = s₂`.

`scalarShift_mem_vermaIdeal` sends the two Levi congruences into the common ideal `R_{Y_K}(μ)`.
Their difference is central by `scalarShift_mem_center` and belongs to this ideal for every
`μ`. `mem_generatorRightIdeal_of_forall_mem_vermaIdeal` places it in the right ideal generated
by the positive roots of `𝔪` by testing the Cartan PBW coordinates at every `μ`.
`centerBorelInjectivity` then forces the difference to vanish.

This is the right-ideal form of Knapp–Vogan, *Cohomological Induction and Unitary
Representations* (1995), Chapter IV §8, Proposition 4.129(c), printed p. 303. The argument
implements the transitivity of the normalized Cartan comparison through the common Levi
and uses the right-ideal version of the centrality assertion in Lemma 4.123(c), printed p. 301.
