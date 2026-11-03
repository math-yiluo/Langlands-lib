# A universal connective perfect comparison for proper module Hom

`CoherentSheaves.NoetherianHomPerfectComparisonStatement.{u}` asserts that
the ordinary module Hom presheaf for a proper locally finitely presented
scheme over a noetherian affine base is computed by one strictly perfect
complex of modules over the coefficient ring.

Precisely, for `R : CommRingCat.{u}` noetherian, `p : Y → Spec R` proper and
locally of finite presentation, and actual finitely presented module sheaves
`M,N` on `Y` with `N` flat over the base, it asserts the existence of an
integer cochain complex `K` satisfying:

- `ModuleComplex.IsStrictlyPerfect K`, meaning bounded with finite
  projective terms;
- vanishing of every negative homology module after ordinary scalar
  extension along every ring map `R → S`, for `S : CommRingCat.{u}`;
- a natural isomorphism on the entire scheme slice from
  `intrinsicModuleHomPresheaf p M N` to
  `TensorSections.homologyPresheaf K 0`.

Both presheaves have explicitly lifted values in `Type (u+1)`. The left
side retains every ordinary map between the pulled-back module sheaves;
the right side is the degree-zero homology of
`Γ(T,𝒪_T) ⊗[R] K`. Naturality includes arbitrary scheme tests and arbitrary
morphisms over the base. There is no assumption that the source module or
the ambient scheme is flat, projective, or locally free.

This is a derived intermediate statement extracted from the proof of the
Stacks Project, Section 99.3, Lemma 99.3.9 (Tag 08JY), together with the
connective truncation step of Lemma 99.3.8 (Tag 08JX). The retained source
is `08JS.html` in the registered publication folder
`stacks-hom-functor-08js-2026-11-02`.

The literature first replaces the source by a perfect approximation, then
uses proper perfect direct image and arbitrary base change to obtain a
perfect complex `K` on the affine base with universally vanishing negative
cohomology. On an affine base it has a bounded finite projective module
representative. Its universally connective amplitude permits replacing
that representative by a homotopy equivalent bounded complex of finite
projectives concentrated in nonnegative degrees. For such a representative,
degree-zero hypercohomology on any test scheme is the kernel of the map on
global sections of its first two terms. Finite projectivity identifies
those sections with tensor products with `Γ(T,𝒪_T)`. This explains the
ordinary tensor formula on nonaffine tests; that formula is not valid for
arbitrary complexes without the stated connectivity and perfection.

The present statement records the geometric perfect comparison before
local bases and a finite matrix are chosen. It supplies no proof of that
comparison, no matrix model, and no representability theorem.
