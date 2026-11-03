# Arbitrary base change of central isogenies

`Langlands.GroupScheme.CentralIsogenyBaseChangeStatement` is the proposition
that, for all schemes `S S' : Scheme.{u}`, every scheme morphism `b : S' ⟶ S`,
all actual group schemes `G H : GroupScheme S`, and every group-scheme
homomorphism `f : G ⟶ H`,

```text
IsCentralIsogeny f →
  IsCentralIsogeny ((GroupScheme.baseChange b).map f).
```

The proposition uses the current `IsCentralIsogeny` definition from
`Langlands.GroupScheme.CentralIsogeny.Basic` directly. Its conclusion requires
that the actual underlying morphism of schemes be finite, flat, surjective
and locally of finite presentation, and that its full scheme-theoretic kernel
be central. `GroupScheme.baseChange` is the actual pullback functor
`(Over.pullback b).mapGrp`.

Both bases and `b` are arbitrary, including nonflat base changes. There are
no field, reducedness, smoothness, affineness, connectedness, reductivity or
kernel-smoothness hypotheses. Centrality retains every test scheme over the
new base and every morphism of such test schemes, including nonreduced ones.
Surjectivity is a property of the underlying scheme morphism; it does not
assert surjectivity on points over each test scheme.

## Source convention and derived provenance

Conrad, *Reductive group schemes* (2014), Definition 3.3.9, PDF p.103,
defines an isogeny between smooth affine group schemes over a scheme as a
finite flat surjection, and calls it central when its kernel is central.
The registered source is `conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

Milne, *Algebraic Groups* (2017), Definition 18.1, printed p.387 / PDF p.403,
gives the central-kernel convention for isogenies of connected group varieties
over a field. Its registered source is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete retained official errata snapshot of 2026-11-02 was read:
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
Its Chapter 18 corrections concern reductivity in Remark 18.4 and the
factorization arrow in Proposition 18.8, whose target must be the source
`G'` of the incoming cover. They do not alter Definition 18.1.
No source-specific project errata note for Conrad was present in the
available project notes.

The arbitrary-base-change assertion is a derived closure statement for the
Library definition, rather than a separately numbered result attributed to
either definition above. The Library explicitly includes local finite
presentation over arbitrary bases. The target preserves that condition and
does not import the smoothness or field hypotheses of the source settings.
Its intended derivation uses stability of the scheme-morphism conditions
under pullback and the functorial meaning of full kernel centrality.

## Existing comparisons and the remaining proof

`Langlands.AbelianScheme.IsogenyStability` already proves
`Langlands.GroupScheme.IsIsogeny.baseChange`. It supplies the finite, flat and
surjective part of the intended derivation. Local finite presentation has
the usual scheme-morphism base-change stability and remains a required part
of the conclusion.

The kernel comparison is already constructed and proved in
`Langlands.AbelianScheme.KernelBaseChange`:

```text
kernelBaseChangeIso b f :
  (GroupScheme.baseChange b).obj (kernel f) ≅
    kernel ((GroupScheme.baseChange b).map f).
```

`kernelBaseChangeIso_hom_ι` identifies its forward map followed by the
new kernel inclusion with `(GroupScheme.baseChange b).map (kernelι f)`.
Consequently, this same canonical isomorphism identifies the actual new
kernel inclusion with the pullback of the old kernel inclusion. No additional
kernel comparison is postulated by this statement.

This is a comparison on all test schemes, with its compatibility already
proved. For each `T : Over S'`, `baseChangePointsEquiv b G T` is a multiplicative
equivalence with the points of `G` on `(Over.map b).obj T`.
`kernelBaseChangeIso_points` proves that the kernel isomorphism agrees with
the existing kernel-point identifications and that pullback point
equivalence. `baseChangeKernelPointsEquiv_naturality` proves compatibility
with every morphism of test schemes.

These proved comparisons supply the kernel transport needed in a proof of
the new proposition: use the inverse kernel isomorphism to view a new
kernel point as a point of the pulled-back old kernel; the inclusion equation
then identifies its image in the pulled-back group. Centrality of the old
kernel applies to the corresponding old-base point and all its restrictions.
The multiplicative point equivalence and its naturality transport these
commutation identities to every new-base test scheme. The existing
`SubgroupFunctor.baseChange` implements this point transport for subgroup
functors, and `SubgroupFunctor.range_baseChangeHom` in
`Langlands.GroupScheme.SubgroupBaseChange` gives the corresponding equality
of range functors. The target needs no representing centre.

This module defines the exact proposition only. The kernel isomorphism and
its compatibility laws, and `IsIsogeny.baseChange`, are existing proved
results; preservation of the complete `IsCentralIsogeny` predicate is the
new proof obligation. No proof of that obligation is supplied here.
