# Joint continuity of strict-affinoid spectrum actions

Author: Worker 125.

`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.pointwiseContinuousSpectrumAction`
proves the exact published proposition
`PointwiseContinuousSpectrumActionStatement.{u, v}` from
`StrictTestDomain.ContinuousActionStatement`. The field universe `u` and
the group universe `v` remain independent. The proof imports that unchanged
statement and the published `Spectrum.JointContinuityProof`.

For an ultrametric normed field `K`, an actual presented strict affinoid
`K`-algebra `P`, a topological group `G`, and a homomorphism
`ρ : G →* Aut P`, assume that every forward algebra orbit
`g ↦ (ρ g).hom.toAlgHom a` is continuous in the norm topology of `P`.
The conclusion is joint continuity of the existing action
`(g, x) ↦ (ρ g) • x` on `G × BanachSpectrum P`.

## Inverse orbits and the action convention

The reusable lemma `continuous_inv_apply ρ hρ a` proves continuity of
`g ↦ (ρ g).inv.toAlgHom a`. It composes the given forward orbit map
with continuous inversion on `G`. The resulting map evaluates the
forward map of `ρ (g⁻¹)`. For each `g`, `map_inv` rewrites this
automorphism as `(ρ g)⁻¹`. In the category's automorphism group, taking
the inverse exchanges the forward and inverse maps. The remaining
equality is definitional and is closed by `rfl`. `Continuous.congr`
transfers continuity along this pointwise equality.

This inversion is essential to the convention already implemented in
`RationalAutomorphism.spectrumMulAction`: the value of `(ρ g) • x`
at `a` is `x ((ρ g).inv.toAlgHom a)`. Pullback of spectrum points is
contravariant, so the inverse algebra map supplies the left action;
in a product of group elements the right factor acts on points first.
The proof uses this existing action without constructing another action.

## Joint continuity

The reusable criterion `continuous_spectrumAction ρ hρ` applies
`Langlands.Analytic.BanachSpectrum.continuous_comap_of_continuous_apply`
to the family of bounded ring maps

```text
g ↦ (ρ g).inv.toBoundedRingHom.
```

The preceding inverse-orbit lemma supplies its continuity hypothesis
for every algebra element. The resulting jointly continuous map is
`(g, x) ↦ BanachSpectrum.comap ((ρ g).inv.toBoundedRingHom) x`,
which is definitionally the existing action in the conclusion. Thus
this proof reuses the published analytic argument directly. It does
not repeat the uniform seminorm estimate or joint-evaluation proof.
The imported result is available for normed commutative rings with an
arbitrary topological parameter space and does not require a common
operator bound or completeness.

Finally, `pointwiseContinuousSpectrumAction` introduces exactly the
parameters and hypothesis of the proposition and applies
`continuous_spectrumAction`. No hypothesis is added: completeness of
`K`, a common operator bound, local compactness of `G`, open point
stabilizers, and nonemptiness of the spectrum are all unnecessary here.
No topology is imposed on `Aut P`. Individual boundedness of each
forward and inverse algebra map is already part of the automorphism
data. Rational-domain transport remains the existing construction in
`RationalAutomorphism`, including its theorem `locus_smul`; this proof
adds no assertion about continuity of section transport.

## Provenance and analytic scope

This is an internal derived proof of the Library's criterion, using
Worker 377's published parametric pullback theorem and Worker 36's
statement and spectrum action. These are imported results, not reused
unpublished drafts. The spectrum source context is Berkovich,
*Non-archimedean analytic spaces*, Trieste lectures (2009), printed/PDF
p. 4, Definitions 1.2.3 and 1.2.5 and Exercise 1.2.4, registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Those passages define the spectrum, its normalization and its evaluation
topology; this exact continuity criterion is a derived consequence,
not a numbered assertion attributed to that source.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, printed/PDF pp. 1–2, motivates the
action context. There the topology on analytic automorphisms uses
compact analytic domains, analytic functions and bounds on their
pullbacks, and a continuous analytic action is defined through a
continuous homomorphism into that topological automorphism group.
The theorem proved here concerns the underlying spectrum action from
an explicit norm-continuity hypothesis on algebra orbits. It does not
identify that hypothesis with Berkovich's automorphism topology or
construct a full analytic `G`-space or an equivariant etale site.
The registered source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
its member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
