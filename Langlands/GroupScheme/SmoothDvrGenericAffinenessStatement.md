# Smooth DVR groups with affine generic fibre

`Langlands.GroupScheme.SmoothDvrGenericAffinenessStatement.{u}` is a
proposition definition, with no proof in this module. It asserts that an
actual smooth, quasi-compact, separated group scheme over a discrete
valuation ring is affine when its actual generic fibre is affine.
Smoothness already implies local finite presentation, so the
quasi-compactness assumption makes the structural morphism finite type.

The DVR, the specified fraction field and all schemes have the arbitrary
universe `u`. The generic fibre uses the actual `GroupScheme.baseChange`
along the spectrum of `algebraMap R K`. Affineness and separatedness are
properties of the actual structural morphisms. There is no connectedness,
commutativity, henselianity, perfection or characteristic hypothesis.

## Provenance

This is a derived subcase of Gopal Prasad and Jiu-Kang Yu, *On
quasi-reductive group schemes*, Proposition 3.1, author-preprint p.5.
The proof there first reduces the separated flat finite-type case to a
smooth group and then proves precisely the smooth affineness assertion
used here. The proposition definition isolates that latter obligation.
Its proof is `smoothDvrGenericAffineness` in
`Langlands.GroupScheme.SmoothDvrGenericAffinenessProof`; neither the full Raynaud criterion nor
this subcase is assumed proved by this module.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
file *Prasad–Yu, On quasi-reductive group schemes (author preprint).pdf*,
Proposition 3.1, author-preprint p.5.
