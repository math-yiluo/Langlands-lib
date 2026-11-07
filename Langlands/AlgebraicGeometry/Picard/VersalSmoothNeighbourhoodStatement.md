# Smooth open neighbourhoods of versal Picard points: statement

Module: `Langlands.AlgebraicGeometry.Picard.VersalSmoothNeighbourhoodStatement`.

Author: Worker 1420, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`. The
statement's shape was agreed with Worker 1653, who plans its proof.

This module contains one proposition, `VersalSmoothNeighbourhoodStatement.{u}`,
which is not proved here. It is an intermediate statement for the proof of
the published `FiniteTypePicardStackAtlasStatement`. It is the second half
of the proof of Stacks Lemma 98.13.8, specialized to the actual Picard
groupoid over bases of finite type over `ℤ`: a chart that is versal at one
finite type point becomes smooth after shrinking to an open neighbourhood of
that point. Together with `FiniteTypeVersalChartStatement`, it gives the
published `FiniteTypePointSmoothChartStatement`; see the module
`FiniteTypePointSmoothChartReduction`.

## The statement

`VersalSmoothNeighbourhoodStatement.{u}` quantifies over

- every commutative ring `R : Type u` of finite type over `ℤ`;
- every scheme `X : Over (Spec R)` with `X.hom` proper and flat;
- every scheme `U` over `Spec R` with `U.hom` locally of finite type;
- every actual line bundle `L` on `(relativeSpace X.hom).obj U`, that is,
  on `U ×_{Spec R} X`;
- every point `u₀` of `U`, every field `K : Type u` with an `R`-algebra
  structure, and every ring isomorphism `e : κ(u₀) ≅ K`
  (`U.left.residueField u₀ ≅ CommRingCat.of K`);
- every morphism `p : ArtinianTest.residueBase R K ⟶ U` over `Spec R`,
  where `ArtinianTest.residueBase R K` is `Spec K` over `Spec R` through
  `algebraMap R K`.

Its hypotheses are:

1. `p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀`: `p` is the
   canonical morphism `Spec κ(u₀) ⟶ U` transported to `Spec K` along `e`.
   Since `p` lies over `Spec R`, `e` is then an isomorphism of `R`-algebras,
   so `u₀` has residue field `K` over `R`;
2. `p.left` is locally of finite type. Given hypothesis 1, this says that
   `κ(u₀)` is of finite type over `R`, that is, `u₀` is a finite type point
   of `U` in the sense of the source;
3. `PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p`,
   the published lifting form of versality at `p`. Its tests are the
   published `ArtinianTest R K`: local Artinian `R`-algebras with a
   surjective augmentation to `K`. For every surjective test arrow
   `A → B`, every scheme `T` over `Spec R` with an actual line bundle `M` on
   `T ×_{Spec R} X` and a map `a : Spec A ⟶ T`, every actual point of the
   point fibre of `L` and `M` over `Spec B` whose chart map restricts to `p`
   lifts to an actual point over `Spec A`.

Its conclusion is the existence of a scheme `V` over `Spec R` and a morphism
`j : V ⟶ U` over `Spec R` such that

- `j.left` is an open immersion;
- `u₀` lies in the image of `j.left`;
- `PicardGroupoid.HasSmoothPointFibers X.hom L'` holds for the pullback
  `L'` of `L` along `(relativeSpace X.hom).map j : V ×_{Spec R} X ⟶
  U ×_{Spec R} X`. This published predicate says that for every scheme `T`
  over `Spec R` and every actual line bundle `M` on `T ×_{Spec R} X`, the
  actual point-fibre presheaf of `L'` and `M` is represented by a scheme
  smooth over `T`.

An open subscheme `W ⊆ U` containing `u₀` gives such a `j`, namely
`V = Over.mk (W.ι ≫ U.hom)` and `j = Over.homMk W.ι`; the statement allows
any open immersion over `Spec R`.

## Source and derivation

The source is The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06` (chapter PDFs of version
ed88ff78). Within `artin.pdf`, Chapter 98 "Artin's Axioms" is numbered
internally without the chapter prefix.

- **`artin.pdf`, Lemma 98.13.8 (Tag 07XY), printed as Lemma 13.8,
  pp. 23–24.** Its proof obtains `U`, `x` and `u₀` with `x` versal at
  `u₀`, then argues: "By openness of versality we may shrink `U` and assume
  that `x` is versal at every finite type point of `U`. We claim that
  `x : (Sch/U)_{fppf} → 𝒳` is smooth", using Lemma 98.13.3 (Tag 07XT) and
  Lemma 98.13.7 (Tag 07XX). The present statement is this step.
- **`artin.pdf`, Definition 98.13.1 (Tag 07XQ), printed p. 21–22**:
  openness of versality, for `U` locally of finite type over `S` and a
  finite type point `u₀` at which `x` is versal.
- **`artin.pdf`, Definition 98.12.2 (Tag 07XF), printed p. 18**: versality
  at a finite type point `u₀`, smoothness of
  `x̂ : F_{(Sch/U),k,u₀} → F_{𝒳,k,x₀}`; with `k = κ(u₀) ≅ K` it is the
  lifting property `IsFormallyVersalAt X.hom L p` at the point `p` of `u₀`.
- **Lemma 98.13.3 (Tag 07XT) and Lemma 98.13.7 (Tag 07XX)**, printed
  pp. 22–23: if `x` is versal at every finite type point of `U`, then the
  morphism `x` satisfies the infinitesimal lifting condition (13.2.1), and
  a morphism representable by algebraic spaces satisfying (13.2.1) between
  limit preserving stacks is smooth.

The Picard stack is that of the published target statement; its source is
`stacks-picard-stack-algebraicity-2026-11-01` (`0372.html`, Section 95.16;
`0DM9.html`, Lemma 108.8.1, for its affine diagonal).

### Specialization

Take `S = Spec R` and `𝒳` the Picard stack of `X → S`. A morphism
`(Sch/U) → 𝒳` is an actual line bundle `L` on `U ×_S X`. Its restriction
to an open `U' ⊆ U` is the pullback `L'` along the open immersion. Since
the diagonal of the Picard stack is affine, smoothness of
`(Sch/U') → 𝒳` means that each base change along `T → 𝒳` is a scheme
smooth over `T` representing the point-fibre presheaf; this is
`HasSmoothPointFibers X.hom L'`. The source hypotheses on the stack
(openness of versality, (RS), limit preservation, representability of the
diagonal) are properties of the Picard stack of a proper flat finitely
presented morphism over a Noetherian base; they are proof obligations, not
hypotheses of this statement.

The Lean conclusion keeps smoothness of the shrunken chart and drops the
intermediate assertion that `L'` is versal at every finite type point of
`U'`. It asks for an open immersion `j` over `Spec R` rather than an open
subset, which is equivalent up to isomorphism. The base is restricted to
rings of finite type over `ℤ`, where the source allows any locally
Noetherian scheme; this restriction suffices for the target. The statement
is therefore a derived specialization of the cited step, not a verbatim
single source assertion.

## Scope

The statement allows every commutative ring of finite type over `ℤ`,
including non-reduced, non-domain and zero rings, every proper flat scheme
over `Spec R`, and every chart locally of finite type. It assumes no
projectivity, smoothness, connectedness, section or cohomological flatness.
It asserts nothing about surjectivity of the shrunken chart.
