# Berkovich's ordinary equivariant cohomology spectral sequences

## Source and scope

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), §1.2, printed and PDF pp. 4–5.
[The displayed spectral sequence is at the top of p. 5](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=5).
Registered literature ID: `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
folder SHA-256: `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
PDF SHA-256: `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Page 4 defines invariant sections `Γ_{X(G)}` and smooth sections `Γ_{X{G}}`
on both equivariant sites. Page 5 states that for an abelian sheaf `F`,

\[
E_2^{p,q} = H^p(G,H^q(X\{G\},F)) \quad\Longrightarrow\quad H^{p+q}(X(G),F).
\]

This module states a derived-category presentation of this assertion for the
Library's two fixed-field equivariant sheaf models. It specifies a spectral
sequence, its second page and its finite abutment filtration. The inner
cohomology on page 2 is derived **smooth sections** in the model; it is not
`H^q(X,b^*F)`. The latter second page in Theorem 1.6.1(ii), p. 13, uses the
compact-base comparison and is not stated here. Neither is the étale
compact-support spectral sequence of Corollary 1.5.2(i), pp. 11–12.

Both the inner derived smooth sections and the derived invariant sections in
the abutment are computed in the Library's model categories, not in the
manuscript's equivariant sites. In the manuscript Theorem 1.4.2, pp. 8–9,
provides the equivalence via `b^*` from the equivariant sites to smooth
`G`-sheaves. Identifying the model functors with the manuscript functors
requires a formal comparison realizing this transfer on each site; that
comparison is open. See the modelling choices in
[AnalyticGlobalComposite/Statement.md](../AnalyticGlobalComposite/Statement.md#correspondence-and-modelling-choices).

## Inputs and conventions

* `X` lies in `LocalizedCategory.{u,v,v} (K := K)`, for a complete ultrametric
  normed field `K : Type u`. A topological group `G : Type z` acts by analytic
  automorphisms over `K` via `ρ : G →* Aut X`, with `IsContinuousAction ρ`
  as in `ContinuousAnalyticAction`. Berkovich assumes Hausdorff spaces
  throughout (§1.1, p. 1) and continuous actions (§1.1, p. 2), and allows
  automorphisms inducing isometric automorphisms of the base field (§1.1,
  p. 1). The Library statements use continuous actions over the fixed field
  and the refinement instances below. They do not handle actions moving the
  field, but in the model they apply without a global Hausdorff hypothesis.
  No compactness or cohomology comparison is assumed.
* Put `s = max u (v + 1) uL`. The site-size instance is `Small.{s} G`. The
  étale statement takes `HasAdmissibleRefinements` for
  `distinguishedLiftSystem ρ` on `twistedEtaleTopology ρ`; the quasi-étale
  statement takes `HasFiniteEquivariantRefinements` for `compactLiftSystem ρ`
  on `twistedQuasiEtaleTopology ρ`. These retained Library model conditions
  make the respective sheaf cohomology functors available; neither proposition
  asserts the refinement condition. The sheaves are the `EtaleGSheaf` and
  `QuasiEtaleGSheaf` models from `Langlands.Sheaf.Equivariant.AnalyticGSheaves`.
* The sheaf coefficients are modules over one commutative ring `R : Type s`.
  This is the fixed-coefficient module version of the source's abelian-sheaf
  assertion (integer coefficients for abelian sheaves, with universe lift if
  needed). For `C = SmoothRep.{s,z,s} R G` the statement quantifies over a
  model `HasDerivedCategory.{w} C`. The Ext universe is `w`, using
  `hasExt_of_hasDerivedCategory`. The trivial smooth representation on `R` is
  `AnalyticGlobalComposite.trivialSmoothRep R G`. In this model the group
  cohomology on page 2 means the right derived functors of smooth invariants,
  with underlying additive groups `Abelian.Ext R M p` in `C`, where `R` in
  the first argument denotes the trivial representation. This interpretation
  uses the identification of `Hom_C(R,M)` with `M^G` by evaluation at `1`
  (`AnalyticGlobalComposite.invariantsHomIso`). No identification with a
  group cochain complex, no coefficient change, and no scalar-linear or
  natural-family version of the page/abutment identifications is asserted.

## Lean declarations and convergence

The declarations are in `Langlands.Cohomology.AnalyticGlobalSpectralSequence`.

* `spectralSequence D A` is an abbreviation for the Library's
  `hyperextSpectralSequence` on `op D` and `op (A[0])` in the opposite of
  `DerivedCategory C`, with the opposite standard t-structure. This choice
  gives the covariant sequence for `Hom(A[0], D[n])`. In the two geometric
  statements `A = trivialSmoothRep R G` and `D` is
  `DerivedCategory.Plus.ι.obj ((etaleGSheafComplex ρ R).obj F)` or its
  quasi-étale counterpart. This is the derived smooth-section complex,
  denoted `RΓ(X{G}, F)` in model notation, constructed using injective
  resolutions in the corresponding Library model.
* `FirstQuadrantAbutmentStatement D A H` is the internal convergence predicate
  for this *specified* sequence and a family of additive groups `H n`.
  It requires vanishing on page 2 outside `p,q ≥ 0`. In each degree `n : ℕ`
  it identifies the abutment `ShiftedHom (op D) (op (A[0])) n` additively
  with `H n`. On the abutment, `HyperextAbutment.filtration` is the decreasing
  truncation filtration; the predicate requires `F^0 = ⊤` and
  `F^{n+1} = ⊥`. At any integer position `(p,q)`, once
  `r ≥ max(2,p+1,q+2)`, it requires zero incoming and outgoing differentials
  and an additive-group isomorphism of `E_r^{p,q}` with
  `HyperextAbutment.graded`, the piece `F^p/F^{p+1}` in degree `p+q`. Thus
  in nonnegative total degree the filtration can be transported to `H n`
  by the asserted additive equivalence. The bounds are sufficient stability
  bounds from the half-bounded hyperext construction, not a degeneration
  claim or an additional hypothesis on `F`.
* `AnalyticEtaleGlobalSpectralSequenceStatement` and
  `AnalyticQuasiEtaleGlobalSpectralSequenceStatement` are the two source
  propositions. For every `F` in the corresponding category, they identify
  `E_2^{p,q}` for `p,q : ℕ` additively with
  `Abelian.Ext (trivialSmoothRep R G) ((etaleGSheafCohomology ρ R q).obj F) p`
  or its quasi-étale counterpart. The second Ext argument is the model's
  `H^q(X{G},F)`. They assert `FirstQuadrantAbutmentStatement` with `H n` the
  underlying additive group of `(etaleGSheafInvariantCohomology ρ R n).obj F`
  or `(quasiEtaleGSheafInvariantCohomology ρ R n).obj F`, respectively. These
  are the derived invariant sections in the same model categories, denoted
  `H^n(X(G),F)` in model notation. The page and graded-piece identifications
  and the convergence conditions are all conclusions.

## Relation to existing Library results

The ordinary composite statements in `AnalyticGlobalComposite.Statement`
identify the abutment but do not state the spectral sequence. For a later
proof here, `HyperextConvergence.CovariantSecondPageProof` supplies the
covariant page-2 and shifted-Hom identifications. The analytic global-complex
homology isomorphisms and negative-degree vanishing identify that page with
Ext into smooth cohomology and give the first-quadrant bound. Since `D` is
nonnegative and `A[0]` is concentrated in degree zero, the two objects in
opposite degrees satisfy the bounds `b = c = 0` of
`HyperextConvergence.HalfBoundedProof`; the filtration endpoints use
`HyperextAbutmentFiltration`. The published ordinary composite proofs then
identify the abutment with invariant cohomology. This describes the provenance
of the formulation; this module supplies statements, not their proofs.
