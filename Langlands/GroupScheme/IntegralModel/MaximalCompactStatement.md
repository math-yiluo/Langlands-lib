# Maximal compactness of the actual integral-point image

`Langlands.GroupScheme.IntegralModel.MaximalCompactStatement` states the final
assertion of Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 2.4.3, printed p. 59 / PDF p. 76. The registered original is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
retained at
`/home/taskhub/central-library/Getz-Hahn--An introduction to automorphic representations (book)--2024.pdf`.
Definition 2.4.1 and the group-model convention on printed p. 58 / PDF p. 75
specify the models used here. The October 2026 authors' errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
retained at
`/home/taskhub/pilot/literature/Getz–Hahn — Errata for An Introduction to Automorphic Representations (October 2026).pdf`,
were read in full (PDF pp. 1–5); they contain no correction to this passage.

The proposition is universe polymorphic. At each universe `u`, it ranges over
every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, every actual group scheme `G` over `Spec F`,
every proof of the existing `IsConnectedReductive G`, and every supplied
`M : IntegralModel 𝒪[F] F G`. No characteristic restriction is imposed; equal
and mixed characteristic use the same statement. The existing
`IsConnectedReductive` predicate expresses smoothness, affineness,
connectedness and triviality of the geometric unipotent radical.

Here the `ValuativeRel` notation `𝒪[F]` is the actual valuation integer subring
`Valuation.integer (ValuativeRel.valuation F)`. Its algebra map to `F` is the
subtype inclusion, and the model uses the canonical fraction-ring instance.
The local-field module imports these existing structures. The residue field
`𝓀[F]` is `IsLocalRing.ResidueField 𝒪[F]`; its algebra map from `𝒪[F]` is the
canonical residue quotient. The hypothesis is connected reductivity of the
full actual special-fibre group scheme

```text
(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group.
```

It is not a hypothesis about only a reductive quotient of that fibre.

`M.group` is affine, flat and locally of finite type over `Spec 𝒪[F]`.
Affineness supplies quasi-compactness, hence finite type, as required in
Definition 2.4.1. That definition explains that flatness identifies its
coordinate algebra with an integral subalgebra of the generic coordinate
algebra. The supplied `M.genericIso` identifies the actual generic pullback
with `G` as a group scheme, retaining the source's compatibility of the group
operations. This statement reuses that model interface rather than adding a
coordinate presentation as new data.

The subgroup is exactly `M.integralPoints`, the range of the already defined
`M.integralPointMap : M.integralSections →* rationalPoints G`. That map
restricts an integral section along the actual inclusion `𝒪[F] → F`, forms
the pullback lift, and postcomposes with the supplied `M.genericIso`.
Thus the subgroup is the actual image in the existing `rationalPoints G`.

The topology is explicitly `rationalPointTopology F G.X`, the existing
regular-function evaluation topology on the identity-test rational-point
carrier. The proposition derives `IsAffineHom G.X.hom` from the supplied
connected-reductivity proof and then derives `IsAffine G.X.left`; neither
is an additional premise. It installs the named topology locally for both
compactness assertions. The conclusion says that the integral image is
compact and that **every** compact subgroup `L` of that same rational-point
group containing the image satisfies `L = M.integralPoints`. This is
maximality among all compact subgroups, with no selected collection.

This is a proposition statement, not a proof. The existing
`IntegralModel.isCompact_integralPoints` in
`Langlands.GroupScheme.IntegralModel.CompactPoints` proves compactness of a
supplied model image over a compact Hausdorff ring with continuous inclusion;
it supplies no maximality. The remaining proof must establish the complete
stated conclusion for every supplied model. In particular, any comparison
with a geometric special compact or parahoric subgroup must be proved for
this actual image. No building, comparison, splitness, positive rank,
transitivity, compact-overgroup maximality, Iwasawa decomposition, or
smoothness of `M` is assumed. Getz–Hahn observe smoothness after Definition
2.4.4 on the same page; any use of it belongs to the proof.

The equivalence between unramifiedness and existence of a good model in the
first part of Theorem 2.4.3, arithmetic spreading, and the global integral
Iwasawa consumer are outside this declaration. The book attributes the
theorem to Bruhat–Tits and points to [Mac17, §1.2]; that reference is a route
for later proof work, not a Lean proof provided by this module. No further
external source is used here.
