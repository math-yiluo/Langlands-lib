# Models of smooth affine group schemes over rings of finite type over `ℤ`

Worker 1412. This is an internal lemma for the noetherian reduction in
SGA 3, Exposé XI, proof of Theorem 4.1, registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 21. There
the base `Spec A` is replaced by `Spec A₀` for a subring `A₀ ⊆ A` of finite
type over `ℤ`, citing EGA IV 8.

`exists_finiteType_model` takes a commutative ring `A : Type u` and an actual
group scheme `G` over `Spec A` with `G.X.hom` smooth and affine. It produces a
commutative ring `R : Type u` of finite type over `ℤ`, a ring map `φ : R → A`, an
actual group scheme `G₀` over `Spec R` with `G₀.X.hom` smooth and affine, and an
isomorphism of group schemes from `G` to the base change of `G₀` along
`Spec φ`.

## Proof

1. The underlying scheme of `G` is affine, with coordinate ring
   `B = Γ(G.X.left, ⊤)`. `B` is an `A`-algebra through the global-section map
   of `G.X.hom`. The structure morphism `G.X.hom` is `Spec` of that ring map
   up to the canonical isomorphism `G.X.left ≅ Spec B`, so `B` is a smooth
   `A`-algebra.
2. Mathlib's `Algebra.Smooth.exists_subalgebra_fg` (noetherian descent of
   smooth algebras) gives a finitely generated `ℤ`-subalgebra `A₀ ⊆ A`, a smooth
   `A₀`-algebra `B₀`, and an `A`-algebra isomorphism `B ≃ A ⊗[A₀] B₀`.
3. Put `f₀ = Spec(A₀ → B₀)`. It is smooth. Mathlib's
   `isPullback_SpecMap_of_isPushout`, applied to the tensor-product pushout and
   transported along `G.X.left ≅ Spec B ≅ Spec (A ⊗[A₀] B₀)`, shows that `G.X.hom`
   is a pullback of `f₀` along `Spec(A₀ → A)`.
4. The Library theorem `GroupScheme.subalgebraDescent` descends the group
   structure. It gives a finitely generated `A₀`-subalgebra `T ⊆ A` and an
   actual group scheme `G₀` over `Spec T`. Its underlying morphism is a pullback
   of `f₀`, and `G` is isomorphic as a group scheme to the base change of `G₀`
   along `Spec(T → A)`.
5. `T` is of finite type over `ℤ` because finite type is transitive along
   `ℤ → A₀ → T`. `G₀.X.hom` is smooth and affine because both properties are
   stable under pullback and hold for `f₀`. Take `R = T` and `φ` the inclusion
   `T → A`.

The proof never descends a general scheme: the model comes from the affine
model `Spec B₀ → Spec A₀` of the coordinate ring. The result is uniform in the
universe `u`.
