# Finite-support cohomology detection for the second abelian-square projection

The theorem
`Langlands.AbelianScheme.algClosedFieldSquareSecondProjectionFiniteSupportDetection`
proves the entire published proposition
`Langlands.AbelianScheme.AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement.{u}`.
It has exactly this type, in arbitrary universe `u`, with no additional
outer parameters or hypotheses.

For an abelian scheme `A` over an algebraically closed field `K`, write
`a = A.X.hom`, `Z = pullback a a`, and `p2 = pullback.snd a a`.
Let `Q` be an actual line bundle on `Z` and `F` a finite set of actual
`K`-rational points of `A`. If all cohomology of the restriction of `Q`
to `A × {x}` vanishes for every `x ∉ F`, and all total cohomology of `Q`
on `Z` vanishes, then all fibre cohomology vanishes for every rational
point, including the points of `F`. Each degree is an arbitrary natural
number, including zero.

## Implemented proof

First apply the published theorem `squareSecondProjectionSupport`.
Its hypotheses are exactly the finite set `F` and the outside-`F`
vanishing from the target. It gives

```text
HasFiniteClosedSupport ((DerivedSections.higherDirectImage p2 q).obj Q.obj)
```

for every natural degree `q`. This support theorem uses the actual
rational-point complement, the second-fibre identification, and the
rational-fibre vanishing criterion with the proved universal perfect
sections theorem. The present assembly imports that result.

Fix `q` and apply the published `finiteClosedSupportLeray` to
`p2`, `a`, and `Q.obj`. It gives an isomorphism from
`(DerivedSections.relativeCohomology (p2 ≫ a) q).obj Q.obj` to
the relative global sections along `a` of
`(DerivedSections.higherDirectImage p2 q).obj Q.obj`.
The pullback equation identifies `p2 ≫ a` with
`pullback.fst a a ≫ a`, the exact structure map in the target's total
vanishing hypothesis. Transporting zero through the isomorphism
therefore makes those relative global sections zero.

The relative zero-detection clause of the published
`finiteClosedSupportCohomology` then makes the higher direct image itself
zero. Repeating this for every `q` gives joint vanishing in all natural
degrees. Both the Leray comparison and zero detection hold for actual
scheme modules with finite closed support. This route needs no separate
coherence assertion in the assembly; it uses the stronger general
finite-support results.

Apply the published theorem `higherDirectImageVanishingAffineBaseChange`
to `p2`, `Q`, this joint vanishing, and `x.left : Spec K ⟶ A.X.left`.
The projection `p2` is smooth and proper by base change from the structure
morphism of the abelian scheme; Lean infers these instances. The result
is zero cohomology of the actual pulled-back module on
`pullback p2 x.left`, in every natural degree. The imported theorem
establishes this implication using affine restriction, the proved
perfect representative, arbitrary scalar change of an acyclic bounded
flat complex, and local detection. It leaves no comparison or
perfect-sections premise in the present theorem.

Finally, the published `squareSecondFibreCohomologyIso`, with the actual
section equation `x.w`, identifies that pullback cohomology with the
cohomology of the line bundle pulled back along the target's exact map

```text
i2(x) = pullback.lift (id A.X.left) (a ≫ x.left) (section equation).
```

Transporting zero through this isomorphism gives the required conclusion.
All functors are the published scheme-module pullback, pushforward,
relative global sections, and their right-derived cohomology functors.

## Original source and derived specialization

The registered original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary version of the first chapters, literature
ID `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The relevant passages are Fact (7.20), printed p.105 / PDF p.109,
and the second Leray calculation in Proposition (7.21), printed p.106 /
PDF p.110. The surrounding Lemmas (7.15), (7.16), and (7.19) on
PDF pp.108–109 were also read.

The source applies the argument to a Mumford bundle and its finite
translation stabilizer. This theorem isolates the resulting geometric
implication for an arbitrary line bundle `Q` and an arbitrary finite set
`F`, as specified by the published target. It is derived content, rather
than a transcription of a separately numbered source theorem. Its proof
uses the published finite-support Leray comparison in place of
constructing another spectral sequence.

The support step in the printed proof cites (7.15), apparently referring
to (7.19) together with (7.20). The unrestricted printed Fact (7.20)
omits flat-family hypotheses. Here the smooth proper projection and the
line bundle supply the hypotheses used by the proved perfect-sections
and vanishing results. In particular, the proof uses joint vanishing in
all degrees; it does not assert arbitrary base change for each isolated
higher direct image. The source and bounded errata check recorded with
the target found no passage-specific correction, and no source-specific
errata note was present in the current Library or project notes on
2026-10-31.

The characteristic and dimension are unrestricted, including dimension
zero. No ampleness, projectivity, cube theorem, dual or Picard scheme,
tensor-preservation hypothesis, or unproved geometric certificate is
added to the target.
