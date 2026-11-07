# The supercuspidal part of represented cuspidal/remainder splittings

Worker 1582. Internal derived infrastructure for the proof of Renard VI.7.5,
Proposition, printed page 186 / PDF page 192, in David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July
2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes
reductifs p-adiques (2026 version)--2026.pdf`.

Renard's VI.3.5 Theorem, printed pages 146–147 / PDF pages 152–153, splits
the category of smooth representations into a supercuspidal factor and its
complement. The Library records a local consequence of it, without proving
existence: `HasCuspidalRemainderSplitting A` asks for an actual Bool-indexed
coproduct with vertex `A`, a supercuspidal `true` component and a `false`
component without nonzero supercuspidal actual subquotients. This module
shows what such chosen splittings of all smooth representations give: the
supercuspidal components form an additive endofunctor that preserves
monomorphisms and epimorphisms. In the VI.7.5 argument this functor takes
the place of the supercuspidal factor of the category. Renard does not
state these lemmas separately; they are derived here. Supercuspidality is
exactly the published `IsSupercuspidal`, tested on every proper actual
rational parabolic through the published normalized `jacquetFunctor`. No
splitting is constructed here, and neither VI.7.5 statement is proved.

## Definitions

- `HasNoSupercuspidalSubquotient A`: no nontrivial `SmoothRep.IsSubquotient`
  of `A` is supercuspidal. This is word for word the condition that
  `HasCuspidalRemainderSplitting` imposes on its `false` component.
- `CuspidalRemainderSplitting A`: chosen data for that condition. It has
  summands `summand : Bool → SmoothRep ℂ (rationalPoints G)`, inclusions
  `inj b : summand b ⟶ A`, a proof `isSupercuspidal_true`, a proof
  `hasNoSupercuspidalSubquotient_false`, and a colimit proof `isColimit` for
  `Cofan.mk A inj`. `HasCuspidalRemainderSplitting.splitting` chooses such data
  from the existence statement. `hasCuspidalRemainderSplitting` goes back.
- `cuspidalProjection` and `remainderProjection`: the coproduct maps out of
  `A` that are the identity on one summand and zero on the other.
- `cuspidalMap t f`: for splittings `s` of `A` and `t` of `B` and
  `f : A ⟶ B`, the component `s.inj true ≫ f ≫ t.cuspidalProjection`.
- `cuspidalPartFunctor hs`: for `hs` giving a splitting of every smooth
  representation, the endofunctor with objects the chosen supercuspidal
  summands and with morphisms `cuspidalMap`.
- `cuspidalPartι hs : cuspidalPartFunctor hs ⟶ 𝟭 _` and
  `cuspidalPartπ hs : 𝟭 _ ⟶ cuspidalPartFunctor hs`: the chosen inclusions
  and projections, as natural transformations.

## Implemented proofs

Closure of supercuspidality. `IsSupercuspidal.of_injective` and
`IsSupercuspidal.of_surjective` pass supercuspidality along a morphism with
injective underlying map (to its source) and with surjective underlying map
(to its target). Each proof argues by contradiction on one proper parabolic.
A nontrivial Jacquet module of the source, respectively of the target, gives
a nontrivial Jacquet module of the other side, by the published
`nontrivial_jacquet_of_injective` and `nontrivial_jacquet_of_surjective`. The
categorical forms `of_mono`, `of_epi` and `of_iso` use
`SmoothRep.mono_iff_injective` and `SmoothRep.epi_iff_surjective`.
`of_isSubquotient` decomposes an actual subquotient into an injection and a
surjection through `SmoothRep.isSubquotient_iff_exists`.

Hom vanishing. `hom_eq_zero_of_isSupercuspidal_of_hasNoSupercuspidalSubquotient`
assumes `C` supercuspidal and `B` without supercuspidal subquotients. It
shows that every `f : C ⟶ B` is zero. The image `image f` is a quotient of
`C`, hence supercuspidal, and a subobject of `B`, hence an actual
subquotient. It is therefore not nontrivial, that is, a zero object, and
`f = factorThruImage f ≫ image.ι f` vanishes.
`hom_eq_zero_of_hasNoSupercuspidalSubquotient_of_isSupercuspidal` is the
reverse direction, for `f : B ⟶ C`. Here the image is a subobject of `C`
and a quotient of `B`.

Splittings. The four `inj_*_cuspidalProjection` and
`inj_*_remainderProjection` lemmas are the coproduct factorizations.
`projection_add` shows that the two idempotents add up to `𝟙 A`, checked on
both coproduct components. The supercuspidal inclusion is a split
monomorphism, and both projections are split epimorphisms.
`isZero_remainder_of_isSupercuspidal` assumes `A` supercuspidal. Then the
remainder summand is a quotient of `A`, hence supercuspidal, and a
subquotient of itself, hence zero. `isZero_of_isSupercuspidal` then shows
that a supercuspidal `A` with zero supercuspidal summand is zero, through
`projection_add`.

Naturality. By the two hom-vanishing lemmas, the mixed components
`s.inj true ≫ f ≫ t.remainderProjection` and
`s.inj false ≫ f ≫ t.cuspidalProjection` are zero. Inserting
`projection_add` then gives `cuspidalMap_inj`, which says
`cuspidalMap t f ≫ t.inj true = s.inj true ≫ f`. It also gives
`cuspidalProjection_cuspidalMap`, which says
`s.cuspidalProjection ≫ cuspidalMap t f = f ≫ t.cuspidalProjection`.
Functoriality of `cuspidalPartFunctor` follows from the first identity and
the identity `inj_true_cuspidalProjection`. The two identities are the
naturality of `cuspidalPartι` and of `cuspidalPartπ`.

Exactness properties. The functor is additive, since `cuspidalMap` is a
composite and composition is bilinear. It preserves monomorphisms: for a
monomorphism `f`, the composite `(cuspidalPartFunctor hs).map f ≫ ι_B`
equals `ι_A ≫ f`, a monomorphism, so the first factor is one. Epimorphisms
are preserved in the same way, through `cuspidalPartπ`. Finally,
`isZero_of_isSupercuspidal_of_isZero_cuspidalPartFunctor_obj` says that a
supercuspidal representation with zero image under the functor is zero.

## Scope

The ambient data are a field `k` with a Hausdorff topology, an affine group
scheme `G` over `Spec k`, the canonical topology on its rational points, and
local compactness and nonarchimedeanness of that point group. The section
`LocalField` adds `[ValuativeRel k]` and `[IsNonarchimedeanLocalField k]`,
which `nontrivial_jacquet_of_injective` requires. It contains the results
that pass supercuspidality to subobjects: `of_injective`, `of_mono`,
`of_isSubquotient`, the second hom-vanishing lemma, the projection
naturality, `cuspidalPartπ`, its retract identity and epimorphism instance,
and preservation of epimorphisms. The field and carrier universes `u` and
`v` are independent. No reductivity hypothesis is used. The functor is
built from the splittings chosen by `hs`; no statement about other choices
is made.
