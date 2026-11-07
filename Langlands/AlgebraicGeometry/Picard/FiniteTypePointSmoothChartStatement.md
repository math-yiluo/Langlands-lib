# Smooth Picard charts through finite-type field points: statement

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartStatement`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This module contains one predicate, one elementary lemma and one
proposition, `FiniteTypePointSmoothChartStatement.{u}`, which is not proved
here. It is an intermediate statement for the proof of the published
`FiniteTypePicardStackAtlasStatement`. It specializes Stacks Lemma 98.13.8
to the actual Picard groupoid and to bases of finite type over `ℤ`.

## The predicate `PicardGroupoid.HasSmoothPointFibers`

Fix schemes `S`, `X`, a morphism `f : X ⟶ S`, a scheme `U` over `S` and an
actual line bundle `L` on `(relativeSpace f).obj U = U ×ₛ X`.
`HasSmoothPointFibers f L` says: for every scheme `T` over `S` and every
actual line bundle `M` on `T ×ₛ X`, there is a scheme `P` over `T.left`
such that

- the lifted Yoneda presheaf of `P` on the full slice over `T.left` is
  isomorphic to the published actual point-fibre presheaf
  `PicardGroupoid.pointFiberPresheaf f L M`, and
- the structure morphism `P.hom : P.left ⟶ T.left` is smooth.

This is the published `PicardGroupoid.IsSmoothSurjectivePresentation f L`
from `Langlands.AlgebraicGeometry.Picard.StackAtlas` with its surjectivity
clause removed, and with the same quantifiers, the same point-fibre
presheaf and the same representing data. In stack language it says that
the morphism from `U` to the Picard stack defined by `L` is representable
by schemes and smooth. There are no affine, quasi-compact or nonempty
restrictions on `T`.

The lemma `IsSmoothSurjectivePresentation.hasSmoothPointFibers` forgets
surjectivity: a smooth surjective presentation has smooth point fibres.

## The statement

`FiniteTypePointSmoothChartStatement.{u}` quantifies over

- every commutative ring `R : Type u` of finite type over `ℤ`;
- every scheme `X : Over (Spec R)` with `X.hom` proper and flat;
- every field `K : Type u` with an `R`-algebra structure such that `K` is
  of finite type over `R` (`Algebra.FiniteType R K`);
- every actual line bundle `L₀` on
  `(relativeSpace X.hom).obj (ArtinianTest.residueBase R K)`, that is, on
  `Spec K ×_{Spec R} X`. Here `ArtinianTest.residueBase R K` is `Spec K`
  over `Spec R` through `algebraMap R K`.

Its conclusion is the existence of

- a scheme `U` over `Spec R` with `U.hom` locally of finite type;
- an actual line bundle `L` on `U ×_{Spec R} X`;
- a morphism `p : ArtinianTest.residueBase R K ⟶ U` over `Spec R`, that is,
  a `K`-valued point of `U` compatible with the given `R`-algebra
  structure of `K`;

such that `PicardGroupoid.HasSmoothPointFibers X.hom L` holds and there is
an isomorphism of line bundles
`ArtinianChartVersality.residueBundle X.hom L p ≅ L₀`. The published
`residueBundle X.hom L p` is the ordinary pullback of `L` along
`(relativeSpace X.hom).map p : Spec K ×_{Spec R} X ⟶ U ×_{Spec R} X`.

A field of finite type over `R` is a finite field, since `R` is of finite
type over `ℤ` (a Jacobson ring argument). The statement keeps the
hypothesis `Algebra.FiniteType R K`, which is the source's notion of a
finite type field over the base, rather than finiteness of `K`.

The morphism `p` is only a `K`-valued point. It determines a point `u` of
`U` (the image of the unique point of `Spec K`) and an embedding of
residue fields `κ(u) → K` over `R`. The statement does not require this
embedding to be an isomorphism. For example, with `R = 𝔽₂`, `K = 𝔽₄`,
`X = U = Spec 𝔽₂` and trivial bundles, the only morphism `Spec 𝔽₄ ⟶ U` has
image with residue field `𝔽₂`. No surjectivity of the chart is required.

## Source and derivation

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06` (chapter PDFs of version
ed88ff78, compiled 14 July 2026). Within `artin.pdf`, Chapter 98 "Artin's
Axioms" is numbered internally without the chapter prefix.

- **`artin.pdf`, Lemma 98.13.8 (Tag 07XY), printed as Lemma 13.8.** For a
  locally Noetherian base `S`, a category fibred in groupoids `𝒳` whose
  diagonal is representable by algebraic spaces, satisfying axioms [1],
  [2], [3] of Section 98.14, effectivity of
  formal objects, openness of versality, and `𝒪_{S,s}` a G-ring, and for a
  finite type field `k` over `S` with an object `x₀` over `Spec k`: there
  are a morphism of finite type `U → S` and an object `x` over `U` such that
  `x : (Sch/U) → 𝒳` is smooth, and a finite type point `u₀ ∈ U` with
  residue field `k` and `x|_{u₀} ≅ x₀`.
- **`artin.pdf`, Lemma 98.12.7 (Tag 07XH), printed as Lemma 12.7**, is the
  algebraization step used in that proof (a versal effective formal object
  is algebraized at a finite type point with residue field `k`).
- **`artin.pdf`, Lemma 98.17.1 (Tag 07Y4), printed as Lemma 17.1**,
  assembles such charts, one for each finite type field and each object
  over it, into a smooth surjective atlas. The planned proof of
  `FiniteTypePicardStackAtlasStatement` from the present statement follows
  that assembly.

The Picard stack and its atlas condition are those of the published target
statement; its source is `stacks-picard-stack-algebraicity-2026-11-01`
(`0372.html`, Section 95.16, for the stack of invertible sheaves;
`0D04.html`, Proposition 99.10.2, for its algebraicity; `0DM9.html`,
Lemma 108.8.1, for its affine diagonal).

### Specialization

Take `S = Spec R` and `𝒳` the Picard stack of `X → S`. The base is
Noetherian since `R` is of finite type over `ℤ`, and the local rings of a
scheme of finite type over `ℤ` are G-rings (`ℤ` is excellent), so the
hypotheses on `S` hold. The hypotheses of Lemma 98.13.8 on `𝒳` are
properties of the Picard stack of a proper flat finitely presented
morphism; they are proof obligations, not hypotheses of this statement.
A morphism `(Sch/U) → 𝒳` is given by an actual line bundle `L` on
`U ×_S X`. Its smoothness means that for every `T → S` and every object
`M` over `T`, the base change `U ×_𝒳 T → T` is smooth. Since the diagonal
of the Picard stack is affine (Lemma 108.8.1 above), this base change is a
scheme, representing exactly `pointFiberPresheaf X.hom L M`; this is the
predicate `HasSmoothPointFibers X.hom L`. A finite type point `u₀` with
residue field `k` and an isomorphism `x|_{u₀} ≅ x₀` gives a morphism
`Spec k ⟶ U` over `S` together with an isomorphism of the pulled-back
bundle with `x₀`; this is the pair `p` and `residueBundle X.hom L p ≅ L₀`.

The Lean statement weakens the source conclusion in two ways:

- the source's `U → S` of finite type is weakened to locally of finite
  type;
- the source's point `u₀` with residue field `k` is weakened to a
  `k`-valued point `p`, whose image may have a residue field strictly
  contained in `k` (see the example above).

So the source conclusion implies the Lean conclusion, but not conversely.
Both weakenings keep what the assembly of Lemma 98.17.1 uses: a smooth
chart through which the object `x₀` over `Spec k` factors, that is, a lift
`Spec k ⟶ U` of `x₀`.

The statement is therefore a derived specialization of Lemma 98.13.8, not
a verbatim single source assertion. Proving the axioms for the actual Lean
Picard groupoid (in particular effectivity, Artin approximation and
openness of versality) is the content of its future proof.

## Scope

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and zero rings, and every proper flat
scheme over `Spec R`. It assumes no projectivity, smoothness, connectedness,
section or cohomological flatness. It asserts nothing at points whose
residue field is not of finite type over `R`, and asserts no surjectivity;
both are supplied by the assembly of Lemma 98.17.1.
