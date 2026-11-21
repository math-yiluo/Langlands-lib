# Lifting a conjugate family parameter through a smooth product cover

Let `S` be a scheme in universe `u`, and let `G`, `D`, `Q`, and `L` be group
schemes over `S`. Suppose `p : G ×ₛ D → Q` is a smooth surjection of schemes
over `S`. Given homomorphisms `ρ : G → L`, `e : D → L`, and `m : Q → L`,
assume that the composite with `m` is `(g,d) ↦ ρ(g)e(d)` in that order.
Let `j : K → L_M` be a closed torus family with the universal property
`TorusSubgroupModuli.IsUniversal`, and let `f : G → M` classify the range of
the conjugate of `e` by the universal point `ρ` over `G`.

For a henselian local ring `A` with algebraically closed residue field and a
map `a : Spec A → S`, take a parameter `b : Spec A → M` over `S` and a
section `z` of `Q_A`. If the evaluated family at `b` has the range of the
conjugate of `e_A` by `m_A(z)`, then
`TorusSubgroupModuli.parameterOfConjugateOfSmoothProduct` chooses a point
`h : Spec A → G` over `S` together with the equality `h ≫ f = b`.

The proof (`exists_parameter_of_conjugate_of_smooth_product`) chooses a
rational point of the nonempty residue fibre of `p` over the reduction of
`z`. The fibre is locally of finite type over the algebraically closed
residue field. Henselian smooth lifting gives a lift `(h,δ)` of `z` itself.
The product equation identifies `ρ(h)⁻¹ m(z)` with `e(δ)`, which lies in the
range of `e` and thus in its normalizer. Consequently `ρ(h)` and `m(z)` give
the same conjugate range on all tests over `Spec A`. Compatibility of
family evaluation with restriction and injectivity of universal evaluation
then give the required parameter equality. The proof does not assume that
`p` is a homomorphism, that `D` is commutative, or that `Q` is affine.

The auxiliary lemma `evaluate_eq_range_conjugatePullback_of_factor` works
over an arbitrary test `a : W → S` with no henselian or smoothness
hypothesis. If the evaluated inclusion factors through `Q_W` and this
factor is identified by a source isomorphism with a conjugate of
`d_W : D_W → Q_W`, its range in `L_W` equals that of the conjugate of
`d ≫ m` base changed along `a`. Naturality of inner conjugation under `m`
and invariance of range under precomposition by an isomorphism prove
this equality.

This is an internal construction for the end of the valuative lifting
argument. It assembles published rational-point and henselian lifting
lemmas with the all-test subgroup range, conjugation, and evaluation
identities. It takes the product cover and the integral conjugating
section as inputs; it does not construct either of them or prove the
valuative lifting statement.
