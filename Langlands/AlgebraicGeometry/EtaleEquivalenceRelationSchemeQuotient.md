# Scheme quotients of étale equivalence relations by gluing affine quotients

Module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotient`. It imports the
Library module `EtaleEquivalenceRelationInvariantOpen` and the published Anthropic FLT port
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`.
The FLT port imports all of Mathlib, and so does this module.

This module is the scheme-gluing piece ("piece Q") of the first-level step of absolute Noetherian
approximation (FL task 8d02331e, Worker 706). It was written for that task and, in the end, for
this task (Tag 07VS). Its result is used where the Stacks Project concludes that an algebraic
space covered by open subspaces that are affine schemes is a scheme.

## Statements

All schemes live in one universe `u`. `F : EtaleEquivalenceRelation.{u}` is the Library
structure: `t s : F.R ⟶ F.U`, `(t, s)` a monomorphism, with equivalence relation axioms on
points and étale `t` and `s`.

- `structure EtaleEquivalenceRelation.SchemeQuotient F` (the selected declaration) has fields
  - `M : Scheme.{u}` and `q : F.U ⟶ M`;
  - `isPullback : IsPullback F.t F.s q q`, so `F.R` is the kernel pair `F.U ×_M F.U` of `q`
    through `(F.t, F.s)`;
  - the instance fields `etale : Etale q` and `surjective : Surjective q`.

  No affineness, separation or finiteness of `M` is asserted.
- `EtaleEquivalenceRelation.nonempty_schemeQuotient_of_invariantOpenCover F V hV hinv hq` takes
  a family `V : K → F.U.Opens` over an arbitrary index type `K` with
  - `hV : iSup V = ⊤`,
  - `hinv : ∀ k, F.IsInvariantOpen (V k)` (`F.s ⁻¹ᵁ V k = F.t ⁻¹ᵁ V k`),
  - `hq : ∀ k, (F.chart (V k).ι).HasAffineQuotient` (the relation restricted to `V k` has an
    affine quotient in the sense of the Library predicate `HasAffineQuotient`).

  Its conclusion is `Nonempty F.SchemeQuotient`. Affineness of `F.U`, `F.R` or `V k` and
  finiteness of `K` are not needed.
- `EtaleEquivalenceRelation.schemeQuotientOfInvariantOpenCover F V hV hinv hq : F.SchemeQuotient`
  is the chosen quotient, defined with `Nonempty.some`.
- `EtaleEquivalenceRelation.exists_quotient_restrict_of_hasAffineQuotient F V hV h` rewrites an
  affine quotient `q` of the chart relation on an invariant open `V` as a quotient of the
  restriction of `F` to `F.s ⁻¹ᵁ V`. That restriction has the maps `F.s ∣_ V` and
  `(F.R.isoOfEq hV).hom ≫ (F.t ∣_ V)`. The lemma gives the commuting square, flatness, local
  finite presentation, surjectivity and the kernel-pair square.
- `FppfQuotientGluing.exists_quotient_of_forall_exists_quotient_restrict s t W hxW hinv loc` is
  the general gluing theorem. The inputs are morphisms `s t : R ⟶ X` and, for each point `x`, an
  open `W x ∋ x` with `s ⁻¹ᵁ W x = t ⁻¹ᵁ W x`. Over each `W x` there must be a quotient `p`
  of the restricted relation that is flat, locally of finite presentation and surjective, with the
  restricted relation as its kernel pair. The conclusion is a global `p : X ⟶ Y` with
  `s ≫ p = t ≫ p`. It is flat, locally of finite presentation and surjective, satisfies
  `IsPullback s t p p`, and is a coequalizer (`IsColimit (Cofork.ofπ p w)`).
- Two auxiliary theorems sit in the same namespace. `FppfQuotientGluing.quotient_baseChange`: an
  fppf quotient presentation stays one after base change along any morphism of the quotient,
  including the coequalizer property. `FppfQuotientGluing.restrict_pkg` is the case of an open
  of the quotient.

The remaining declarations of `FppfQuotientGluing` are internal steps of the gluing
construction: `Yloc`, `ploc`, `V`, `pV`, `φ`, `core`, `D`, `chart`, `pglued`, and the lemmas
about them.

## Proofs

- Gluing. For each point `x`, choose the local quotient `ploc x : W x ⟶ Yloc x`. The quotient is
  flat and locally of finite presentation, hence open. So the image `V x y` of
  `W x ∩ W y` is open in `Yloc x`, and its preimage is exactly `W x ∩ W y`, because that open is
  invariant (`preimage_imageOpens`). Over `V x y`, the restriction of `ploc x` is again an fppf
  quotient of the restricted relation (`restrict_pkg`). In particular it is a coequalizer, so
  the two quotients of `W x ∩ W y` are identified by a unique isomorphism
  `φ x y : V x y ≅ V y x` (`quotIso`). Its cocycle condition is checked after cancelling the
  epimorphism given by a restricted quotient map (`core_cocycle`). The resulting gluing datum
  (`MkCore`, imported from the FLT port) produces the glued scheme `D.glued`. The local maps
  glue to `pglued : X ⟶ D.glued` along the open cover `W` (`Cover.glueMorphisms`). Each
  `W x → Yloc x → D.glued` is a pullback of an open immersion (`isPullback_chart`). Flatness,
  local finite presentation and surjectivity are local on the target, and the kernel-pair square
  is checked on the open cover (`isPullback_pglued`). The coequalizer property follows from the
  kernel pair and Mathlib's instance that a flat, locally finitely presented surjection is an
  effective epimorphism.
- Base change (`quotient_baseChange`). The three morphism properties are stable under base
  change. The kernel-pair square is built directly from the universal properties of the
  pullback squares. The coequalizer property comes from the effective epimorphism instance.
- Charts (`exists_quotient_restrict_of_hasAffineQuotient`). For an invariant open `V`, the
  Library lemma `isCartesianHom_chart_of_isInvariantOpen` makes the chart arrows
  `V ×_{U,t} R ×_{s,U} V` a pullback of `F.s` along `V.ι`. So does the open
  `F.s ⁻¹ᵁ V` of `F.R`. The comparison isomorphism `IsPullback.isoIsPullback` matches the chart
  projections with `F.s ∣_ V` and with the restriction of `F.t`; the latter is checked after
  composing with the monomorphism `V.ι`. The kernel-pair square of the chart quotient is
  transported along this isomorphism (`IsPullback.of_iso'`).
- Main theorem. Choose for each point `x` an index `k x` with `x ∈ V (k x)` (from
  `iSup V = ⊤`). Apply the gluing theorem with `s := F.s`, `t := F.t`, `W x := V (k x)`. The
  result `q` satisfies `IsPullback F.s F.t q q`, and its flip is the required square. `F.t` is
  the base change of `q` along the flat, locally finitely presented surjection `q`, and `F.t` is
  étale. Étaleness descends along such morphisms (Mathlib's fpqc descent instance for `Etale`,
  upgraded to the fppf class, using `IsZariskiLocalAtTarget` for `Etale`), so `q` is étale
  (`MorphismProperty.of_isPullback_of_descendsAlong`).

## Provenance and relation to the literature

Provenance: derived. Stacks, Limits of Algebraic Spaces, Lemma 70.5.11 (Tag 07SR) ends with "This
means that `X_i` is a scheme (see for example Properties of Spaces, Section 66.13)": an
algebraic space covered by open subspaces that are affine schemes is a scheme. In the absolute
Noetherian approximation of Proposition 70.8.1 (Tag 07SU) this is how the levels `W_i` become
schemes. The FL task works with étale presentations instead of algebraic spaces. In that
setting, "the open subspace given by an invariant open `V k` is an affine scheme" becomes
`HasAffineQuotient` for the chart relation, and "the space is a scheme" becomes a scheme
quotient of the presentation. This module proves that translation by gluing the affine
quotients along the images of the overlaps. This is the gluing of schemes of Stacks, Schemes,
Section 26.14, used in the form of Mathlib's `Scheme.GlueData`. The structure `SchemeQuotient`
and the open-cover form of the hypotheses are internal and follow the interface agreed with the
FL task.

### Code adapted from the Anthropic FLT formalization

Sections `RestrictPkg`, `Main`, `Core` and `Main56` of `FppfQuotientGluing` are adapted from two
files of the Anthropic Lean formalization of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Copyright 2026 Anthropic, PBC, Apache License 2.0;
see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`):

- `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean`;
- `P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean`.

Both are published in this Library under `Langlands/AnthropicFLT/P2M/Sol/`. Changes:

- Removed the hypothesis `IsFinite p` from the local quotients and from `quotient_baseChange`,
  and removed `IsFinite` from all conclusions. The lemma `isFinite_pglued` and the instance
  `isFinite_pV` are deleted.
- Shifted the projections of the conjunctions accordingly.
- The effective-epimorphism instance used for the coequalizer and the epimorphism arguments is
  now Mathlib's instance for flat, locally finitely presented surjections
  (`Mathlib.AlgebraicGeometry.Sites.Fpqc`) instead of the quasi-compact one.
- `V` and `core` are ordinary definitions in this namespace (they were private root-namespace
  definitions), and the `export` lines of the port are dropped.
- Imported rather than copied from the published port: the gluing core `MkCore` and the
  helpers `imageOpens`, `preimage_imageOpens`, `imageOpens_top`, `le_imageOpens_iff`,
  `preimage_preimage_eq`, `tRes`, `tRes_ι`, `sRes_w`, `quotIso`, `π_quotIso_hom`. None of
  them assumes finiteness.
- `haveI` became `have` where the linter asked for it.
- The file keeps the port's finite heartbeat options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`) and `backward.isDefEq.respectTransparency.types false`.

The final section, in namespace `EtaleEquivalenceRelation`, is new.
