# A Galois cover realizing a finite continuous quotient of the fundamental group

The module `Langlands.AlgebraicGeometry.FiniteEtale.TameGaloisRealization`
turns a continuous homomorphism from the Library's pointed finite étale
fundamental group to a finite discrete group into a Galois cover, in the sense
of the pinned `weil-conjectures` package. A point of the cover fixed by an
element of the fundamental group shows that the element lies in the kernel.

## Declarations

- `toCover W : Cover S` is the total space `W.P ⟶ S` of a Galois cover
  `W : Scheme.GaloisCover G S`, seen as an object of the Library's category
  `Cover S` of finite étale schemes over `S`.
- `exists_galoisCover` assumes that `S` is connected and locally Noetherian,
  that `s : Spec Ω ⟶ S` is a geometric point with `Ω` algebraically closed
  and finite geometric fibres `hfin`, and that `H` is a finite group with the
  discrete topology. For every continuous group homomorphism
  `ρ : FundamentalGroup s hfin →* H` there are a group `G : Type (u + 1)`
  with `Finite G` and a Galois cover `W : Scheme.GaloisCover G S` such that:
  - `Nat.card G ∣ Nat.card H`;
  - for every `γ` in the fundamental group and every geometric point
    `p : Fiber s (toCover W)`, if `γ • p = p` then `ρ γ = 1`.

## Proof

Let `N` be the kernel of `ρ` and `Q` the quotient group. `N` is open because
`ρ` is continuous and `H` is discrete. `Q` injects into `H`, so it is finite
and `Nat.card Q` divides `Nat.card H`. Let `V` be `Q`, moved to universe `u`
by `Shrink`, with the fundamental group acting by left multiplication through
`Q`. The stabilizers of this action contain the open subgroup `N`, so the
action is continuous and defines an object `X` of the category of continuous
finite actions. Right multiplication by `g⁻¹`, for `g` in `Q`, gives
automorphisms `τ g` of `X`.

The Library's theorem `geometricContinuousActionEquivalence` says that
`continuousActionFunctor s hfin` is an equivalence. Let `A` be a cover with
`E(A) ≅ X`, and `T g` the automorphism of `A` corresponding to `τ g`. Then
`T 1 = 𝟙` and `T (g * h) = T h ≫ T g`, and the identification of fibres
`β : Fiber s A → V` is injective and equivariant, with
`β (p ≫ T g) = β p * g⁻¹`. So `Q` acts simply transitively on the geometric
fibre of `A`. The package theorem
`Scheme.FiniteEtale.isIso_sigmaDesc_of_existsUnique` turns this into the
torsor condition, and `Scheme.FiniteEtale.surjective_of_nonempty_fiber` gives
surjectivity, so the automorphisms `T g` make `A` a Galois cover `W` with
group `Q`.

If `γ • p = p`, then `γ • β p = β p` in `V`, that is, `γ̄ * β p = β p` in
`Q`, so `γ̄ = 1` and `γ` lies in `N`.
