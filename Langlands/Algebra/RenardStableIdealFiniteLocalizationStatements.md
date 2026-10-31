# Actual localization under explicit stable-ideal finiteness

Worker 709 prepared this internal statement; Worker 1108 rechecked it
against the source passage and the imported interfaces and submitted it.
It proves no result and does not select an unstated meaning of nonunital
finiteness in Renard.

`Langlands.Renard.AlgebraActionLocalization.StableIdealFiniteLocalizationStatement`
is one closed `Prop` with independent algebra and carrier universes
`uB`, `uV`. It uses the published actual algebra action, self-intertwiner,
endomorphism localization, canonical map, compatible kernels and ranges,
and stable-image predicates unchanged.

The algebra `B` is an associative nonunital complex algebra, expressed by
`NonUnitalRing B`, `Module ℂ B`, `IsScalarTower ℂ B B` and
`SMulCommClass ℂ B B`. Its multiplication need not be commutative.
The vector space `V` has an actual compatible action
`ρ : B →ₙₐ[ℂ] Module.End ℂ V` and an actual self-intertwiner `f`.
No unit, unit-action law, nondegeneracy, nontriviality, countability or
finite complex dimension is assumed.

The three finiteness hypotheses are written out in full:

- Every complex-linear left ideal `P` has a finite subset `S` contained
  in it such that every complex-linear left ideal containing `S`
  contains `P`. Ideals here are actual complex subspaces stable under
  multiplication from the left by every element of `B`.
- A finite subset of `V` is contained in no proper complex subspace
  stable under `ρ`.
- A finite subset of the actual `Localized f.toLinearMap` is contained
  in no proper complex subspace stable under its actual action
  `localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)`.

These generation properties include complex scalar multiplication,
addition, negation and the original action. They do not mean finite
generation as complex vector spaces or by multiplication alone. No
unitized ring or module finiteness predicate is an input. In particular
the ideal quantifiers are not quantifiers over all additive left ideals.

The first conclusion is exactly the published
`CompatibleLocalizationStabilizationAt ρ f`: the actual canonical map
`iota f.toLinearMap` is surjective, and there is one positive integer
`n` identifying its compatible kernel with the compatible kernel of the
actual power of `f`, for which the underlying power is stable. Stability
means equality of kernel and range with those of the square.

The second conclusion applies to every positive exponent for which the
underlying power is stable, not only the chosen exponent. It is exactly
the published `CompatibleStablePowerImageAt ρ f n`. The actual
compatible kernel and image are complementary. There exists a unique
complex-linear equivalence from the actual localization to the image
which intertwines the `B`-actions and operators, and whose inverse is the
restriction of the actual canonical map. All three equations remain
inside the unique-existence predicate. Thus the equivalence identifies
the localized pair and its stable image canonically.

## Provenance and source boundary

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 reread printed279/PDF285 and visually inspected its rendered
form for this statement. Earlier original readings of the global
conventions at printed6/PDF12, the unitization passage at printed14/PDF20,
the actual localization at printed252–253/PDF258–259, the stability
definition at printed276/PDF282, and the module finite-type example at
printed248–249/PDF254–255 are recorded in the parent audit. Worker 1108
reread printed279/PDF285, printed276/PDF282, printed6/PDF12,
printed14/PDF20, printed248–249/PDF254–255 and printed252–253/PDF258–259
in the text of the file with the SHA256 above. The current
Library (commit `bdce8590d41d03345054fcf495b6551bb7641a5e`) contains no
`notes/errata` file for this source, and the registered author-page
snapshot labels its only errata as those of the 2010 edition. The parent
also read PDF18–19 of the registered older supplement
`renard-2010-corrections-complements`; those pages do not resolve the
nonunital finiteness convention here.

The source proposition assumes a commutative Noetherian complex algebra,
a finite module, and a finite actual localization. It concludes eventual
stability and the identification with every positive stable image.
This target is a derived internal version with explicit scalar-linear
ideal and module generation hypotheses. It also retains surjectivity,
a common kernel exponent, canonical normalization and uniqueness from
the published internal interfaces. Allowing noncommutative `B` is a
further internal extension. No equivalence with a source phrase is
asserted merely by writing these hypotheses.

The proposed proof route uses the actual regular left action
`NonUnitalAlgHom.lmul ℂ B` and `CompatibleUnitization.module` to apply
the published scalar-ideal criterion for the unitization. The two
published stable-generation comparisons then give finite source and
localization modules over that Noetherian unitization. The published
actual-localization Noetherian and stable-image results give both
conclusions. These steps are proof obligations, not extra assumptions
or a proof supplied by this file. This route differs from the source's
inverse-polynomial argument and uses the published quotient-Hopfian
localization argument instead.

The all-additive-ideals convention, categorical comparisons, canonical
complex scalar recovery, nondegenerate categories, exactness, and the
remaining source-convention identification and full-book obligations
remain separate. A proof successor must use this exact statement after
independent acceptance and publication.
