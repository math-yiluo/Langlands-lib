# Simple-connectedness ascent for groups with split maximal tori

Worker 416. This module is an internal conditional assembly toward
`IsSimplyConnectedFieldExtensionStatement`. It uses the actual root-datum
base-change proof and the published group-scheme and lattice definitions.
It proves no structural hypothesis and does not establish the unconditional
field-extension theorem.

`IsSimplyConnected.fieldExtension_of_splitMaximalTorus` treats every extension
of fields `K/k` at arbitrary universe `u`, for an actual simply connected
group `G` over `k` with a supplied split maximal torus `i : T.toGrp ⟶ G`.
Its five global hypotheses are:

- `IsSemisimpleFieldExtensionStatement`, preservation of semisimplicity;
- `MaximalTorusBaseChangeStatement`, preservation and reflection of torus
  maximality (only preservation is used);
- `RootDatumExistenceStatement`, existence of a finite reduced root datum
  on the actual character and cocharacter lattices;
- `SplitSimplyConnectedCorootSpanStatement`, necessity of integral coroot
  generation for simple connectedness;
- `SplitCorootSpanSimplyConnectedStatement`, sufficiency of that generation.

Root-datum existence supplies `J`, `P`, an `IsRootDatumOf i P` witness,
finiteness of `J`, and reducedness. The necessity input makes
`P.corootSpan ℤ` the whole cocharacter lattice. Let `b` be the actual map
`Spec.map (CommRingCat.ofHom (algebraMap k K))`. The semisimplicity and
maximality inputs give semisimplicity of `G_K` and maximality of the actual
pulled-back torus. Splitness of the torus is preserved by its existing
base-change theorem.

The implemented theorem `IsRootDatumOf.baseChange` in
`Reductive.RootDatumBaseChangeProof` shows that the canonically transported
datum `SplitRootDatum.baseChange b T hT P` is a root datum of this actual
pulled-back inclusion. This step is a proved comparison, rather than an
additional root-compatibility hypothesis. Its character and cocharacter
maps are the actual lattice pullbacks. The proved
`SplitRootDatum.corootSpan_eq_top_iff` carries integral coroot generation
to the transported datum. Applying the sufficiency input over `K` concludes
simple connectedness, including its test against every incoming semisimple
central isogeny over `K`.

`isSimplyConnectedAlgClosedFieldExtension_of_corootCriterion` is a `def`
whose value is a conditional proof of
`IsSimplyConnectedAlgClosedFieldExtensionStatement`. It has the same five
hypotheses and additionally `TorusFiniteGaloisSplittingStatement`. The
existing `maximalTorusExistence` supplies a maximal torus over an
algebraically closed field `k`. Its source splits: finite Galois splitting
gives a finite extension, and the existing
`IsTorus.isSplitTorus_of_finiteGaloisSplitting` reflects that splitness over
the algebraically closed base. The preceding theorem now applies to the
arbitrary extension `K/k`. The target statement also assumes `K`
algebraically closed; the split-torus proof itself needs no such assumption.
The local `linter.defProp` setting permits this proof-valued definition,
following the existing conditional-assembly convention.

`isSimplyConnectedFieldExtension_of_algebraicClosureAscent_and_corootCriterion`
combines that extension step with the existing `GeometricReduction`.
It retains the six hypotheses above, adds
`CentralIsogenyBaseChangeStatement` for reflection, and explicitly assumes
`IsSimplyConnectedAlgebraicClosureAscentStatement`. The earlier geometric
reduction embeds the algebraic closure of `k` into the algebraic closure
of `K`, transports along the actual composite-base-change isomorphisms,
and reflects invertibility of morphisms already defined over `K`.

The remaining ascent from an arbitrary field to its algebraic closure is
a separate geometric obligation. It does not follow here from the split
coroot criterion: a maximal torus of the original group need not split
over that original field. No arbitrary group or isogeny over an extension
is assumed to descend, and no cover-existence result is used.

All statements retain the Library's field-only `IsSimplyConnected`
predicate, full scheme-theoretic central kernels, and the actual pullback
functor. The deductions in this module have internal provenance: they
combine the named Library interfaces and the implemented root-datum
comparison without asserting any new external structure theorem.
