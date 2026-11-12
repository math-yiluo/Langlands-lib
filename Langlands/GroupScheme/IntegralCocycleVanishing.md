# Cocycle vanishing over complete rings with finite residue field

Authors: Worker 5015.

This module states and proves two vanishing theorems for the Library's scheme-valued
`Cocycle`, at arbitrary universe `u`:

- `Langlands.GroupScheme.IntegralCocycleVanishingStatement.{u}`, proved by
  `Langlands.GroupScheme.integralCocycleVanishing`;
- `Langlands.GroupScheme.FiniteFieldCocycleVanishingStatement.{u}`, proved by
  `Langlands.GroupScheme.finiteFieldCocycleVanishing`.

Both proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statements

**Integral vanishing.** Let `R : Type u` be a commutative ring and `I` a maximal ideal with
`Finite (R ⧸ I)` and `IsAdicComplete I R`. Let `H : GroupScheme (Spec R)` be smooth with affine
structure morphism. Assume that the actual special fibre, the total space of the base change
of `H` along `Spec (R ⧸ I) → Spec R`, is a connected topological space. Let `U` be an object
over `Spec R` with affine underlying scheme, flat and surjective over `Spec R`. Then every
`ξ : Cocycle H U` satisfies `ξ.IsTrivial`: there is `f : U ⟶ H.X` with
`ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹` for all tests and all `a b`.

**Lang's theorem for cocycles.** Let `k : Type u` be a finite field and `H : GroupScheme (Spec k)`
smooth, with affine structure morphism and connected total space. Then every cocycle of `H`
on an object `U` over `Spec k`, with `U.left` affine and `U.hom` flat and surjective, is trivial.

The covers are arbitrary affine flat surjective covers, not only finite étale ones. The
hypotheses on `R`, `I` and `H` are exactly those of the published construction
`IntegralTorsorPoint.integralTorsorPoint`. Those on `k` and `H` are exactly those of the
published `finiteFieldTorsorPointStatement`.

## The implemented proof

Both proofs follow the same three steps.

1. Torsor. The published construction in `CocycleTorsor` produces the torsor
   `CocycleTorsor.torsor ξ` with the action `CocycleTorsor.modObj ξ` and invertible shear
   `CocycleTorsor.isIso_leftSMul ξ`. It is surjective over the base
   (`CocycleTorsor.surjective_hom ξ`) and smooth over the base, because `H` is smooth
   (`CocycleTorsor.smooth_hom ξ`). Smoothness gives flatness. The torsor is affine, so its
   structure morphism to the affine base is affine and hence quasi-compact.
2. Point. In the integral case, `integralTorsorPoint R I H X hconn` supplies an `R`-valued
   point `p` of the torsor. In the finite-field case, `finiteFieldTorsorPointStatement`
   supplies a `k`-valued point. In both cases `ringPoint_self_left_comp` rewrites the base
   equation of `p`, which says `p.left ≫ X.hom = Spec.map (algebraMap C C)`. Since
   `algebraMap C C` is the identity, `p.left` is a section of the structure morphism.
3. Triviality. `Cocycle.isTrivial_of_torsor_section` applies to the torsor, its point
   `CocycleTorsor.point ξ` and this section. The cocycle equation it needs is
   `CocycleTorsor.toFun_smul_point`.

## Provenance and scope

The integral statement is the Library form of the torsor part of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 8.1.4, printed p.285 / PDF p.316, source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. That proof uses that
torsors over `o` have `o`-points. Kaletha–Prasad work over a Henselian discretely valued
field with Galois cohomology over the maximal unramified extension. The Library theorem used
here requires completeness and a finite residue field, and concerns the Library's
scheme-valued cocycles on arbitrary affine flat surjective covers. It does not compare these
cocycles with Galois cocycles of `G(O_K)`. It does not construct an Iwahori model.

The finite-field statement is a scheme-valued form of Lang's theorem as stated in Milne,
*Algebraic Groups* (2017), Corollary 17.98, printed p.383 / PDF p.399, source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`: for a connected group
variety `G` over a finite field `k`, `H¹(k, G) = 1`. Milne states this for Galois
cohomology. Here the cocycles are the Library's scheme-valued cocycles on arbitrary affine
flat surjective covers of `Spec k`. A smooth group scheme with affine structure morphism is
of finite type over `k`, so it is a group variety in Milne's sense. The proof does not use
Galois cocycles; it goes through torsors and the published `finiteFieldTorsorPointStatement`.

The intended consumer is the Bruhat–Tits route to
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement` in task
`306b2ea2-25ed-490a-9131-292ce36e6c84`. There an Iwahori-valued cocycle must be shown to be a
coboundary. This module proves no part of that statement or of
`LocalSimplyConnectedCocycleVanishingStatement`.
