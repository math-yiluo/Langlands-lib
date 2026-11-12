# Independence of choices and continuity of the star action: statements

Author: Worker 15, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). The module contains two
`Prop`-valued definitions and no proofs. They concern `GaloisPinningData.galoisAction`
and `GaloisPinningData.starAction` of the module `Reductive/StarAction`.

Throughout, `k` and `E` are fields in one universe `u` with an algebra `k → E`, `G` is a
group scheme over `Spec k` whose structure morphism is affine and locally of finite
type, and `G_E` is its base change along `algebraBaseMap k E`.

## Independence of choices

`StarActionIndependenceStatement`: for any two `d d' : GaloisPinningData k E G`, there
are

- an `E`-point `g : Over.mk (𝟙 (Spec E)) ⟶ G_E.X`;
- an isomorphism `φ` from the torus `T_E` of `d` to the torus `T'_E` of `d'`;
- an equivalence `e : RootPairing.Equiv P P'` of the two root data;

satisfying the following.

1. `i_E ≫ (G_E.innerIso g).hom = φ ≫ i'_E`: conjugation by `g` carries the torus of `d`
   onto the torus of `d'`, through `φ`. This is the convention of
   `MaximalTorusConjugacyStatement`.
2. The weight map of `e` is `characterLattice.congr φ`, that is, `χ ↦ φ⁻¹ ≫ χ`. So `e` is
   the map on character lattices induced by the conjugation.
3. The root bijection of `e` maps the support of the base of `d` onto the support of the
   base of `d'`.
4. For every `σ : E ≃ₐ[k] E`, `e ∘ starAction_d σ = starAction_{d'} σ ∘ e`, as
   equivalences `P ≃ P'`.

The star action is therefore, up to the isomorphisms of based root data induced by
`G(E)`-conjugation, independent of the torus `T`, the root datum, the base and the
pinning. Milne (below) asserts this independence, citing his 21.43. The statement makes
it explicit through an actual `E`-point and the map it induces on character lattices.

The torus condition is part of the data. Both tori are defined over `k`, and their
base changes are split maximal tori of `G_E`. The intended proof uses three facts.
Maximal split tori of a smooth connected affine group are conjugate by rational
points. The Weyl group is realized by rational normalizer points (`IsRootDatumOf`).
The based isomorphism induced by `G(E)` is unique, so applying `σ` to `g` changes it
only by a Weyl element. These are proof obligations.

## Continuity

`StarActionContinuityStatement`: assume moreover that `E/k` is algebraic. For every
`d : GaloisPinningData k E G` there is an intermediate field `L` of `E/k`, finite-dimensional
over `k`, such that every `σ : E ≃ₐ[k] E` fixing `L` pointwise satisfies
`d.galoisAction σ = 1` and `d.starAction σ = 1`.

For Galois `E/k`, this gives continuity of both actions for the Krull topology on
`E ≃ₐ[k] E` and the discrete topology on the full root-datum automorphism groups. These
target groups need not be finite: for `G = G_m²` with `E = k` the root and coroot sets
and the base are empty, and both full automorphism groups are `GL₂(ℤ)`. What the statement
yields is that both actions have finite image: they are trivial on the pointwise fixer
of `L`, which has finite index in `E ≃ₐ[k] E` because an automorphism is determined
modulo this fixer by its restriction to `L`, and `L` has only finitely many
`k`-embeddings into `E`. The ordinary part follows from
`TorusLatticeGaloisContinuityStatement` for the torus of `d`: a root-datum automorphism
with trivial weight and coweight maps permutes no roots. The star part follows from
the ordinary part, since `starAction` is `basedRootDatumProjection` after
`galoisAction`. These deductions are proof obligations.

## Source and provenance

Milne, *Algebraic Groups* (2022 corrected reprint), source `milne-2022-algebraic-groups`,
SHA-256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, §25.c,
printed p.555 (PDF p.566). Milne forms the based root datum of `(G_{k_s}, B, T_{k_s})`
and says: "As was explained in (21.43), this is independent of the choice of `(B, T)`
and so, even though the action of `Γ` on `G_{k_s}` need not preserve `B`, it does
define an action of `Γ` on `(X, Δ, X^∨, Δ^∨)`." Of the resulting `*`-action he says:
"This does define an action of `Γ` on `Δ`, and it is obviously continuous."

The statements are derived from these assertions. They allow an arbitrary extension
`E` (algebraic for continuity) instead of `k_s`, and they make the independence
explicit through an actual `E`-point and the induced map on character lattices.
