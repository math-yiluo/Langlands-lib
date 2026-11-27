# Uniqueness of solutions of birational group laws

The module `Langlands.AlgebraicGeometry.BirationalGroupLawSolutionUniquenessStatement` states
Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.1 Proposition 3, printed p. 113
(literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`), over an arbitrary base scheme. The module states a proposition and proves
nothing.

## The proposition

`BirationalGroupLawSolutionUniquenessStatement.{u}` quantifies over schemes `S` and `X` in
universe `u`, a morphism `f : X ⟶ S` which is smooth, separated, locally of finite type,
quasi-compact and surjective, a representative `m : BirationalGroupLaw f` of an
`S`-birational group law (module `Langlands.AlgebraicGeometry.BirationalGroupLaw`), and two
solutions `σ τ : m.Solution`. It asserts that there is exactly one isomorphism
`e : σ.group ≅ τ.group` of group schemes over `S` (an isomorphism in
`Langlands.GroupScheme S = Grp (Over S)`) such that for every scheme `T` and all morphisms
`x : T ⟶ σ.domain` and `y : T ⟶ τ.domain` with the same composite to `X`,

`x ≫ σ.embedding ≫ e.hom.hom.hom.left = y ≫ τ.embedding`.

Here `e.hom.hom.hom.left` is the morphism of schemes underlying `e`. The condition says that
`e` restricted to the image of `σ.domain ∩ τ.domain` is the composite of the two embeddings:
`e ∘ σ.embedding = τ.embedding` on `σ.domain ∩ τ.domain`, tested on `T`-valued points.

## Correspondence with the source

BLR 5.1/3: let `m` be an `S`-birational group law on a separated and smooth `S`-scheme `X`
which is faithfully flat and of finite type over `S`. If there exists a solution of `m`, it is
uniquely determined up to canonical isomorphism.

- The base `S` is arbitrary, as in BLR.
- Smooth, separated, faithfully flat and of finite type: `Smooth` gives flatness,
  `Surjective` gives faithful flatness, and `LocallyOfFiniteType` with `QuasiCompact` is
  finite type.
- The canonical isomorphism of BLR's proof (printed pp. 113–114) is the extension of the
  birational map `τ.embedding ∘ σ.embedding⁻¹` from `σ.group` to `τ.group`, defined on the
  image of `σ.domain ∩ τ.domain`; this is the compatibility condition. BLR show that this
  birational map is defined everywhere (2.5/5, with Lemma 5.1/4), is a homomorphism, and has
  as inverse the analogous map in the other direction.
- "Uniquely determined up to canonical isomorphism" is stated as the existence of exactly
  one compatible isomorphism. Uniqueness holds because two compatible isomorphisms agree on
  the image of `σ.domain ∩ τ.domain`, an `S`-dense open of the smooth `S`-scheme underlying
  `σ.group`, which is schematically dense, and the target is separated over `S`.

## Use

The proof of BLR §6.5 Corollary 2 (printed pp. 157–158) uses this proposition over
`R' ⊗_R R'` and `R' ⊗_R R' ⊗_R R'` for a strict henselization `R'` of a discrete valuation
ring `R` to build a descent datum, and the proof of the last assertion of BLR §5.1 Theorem 5
(printed p. 114) uses it over the fraction field of `R`.
