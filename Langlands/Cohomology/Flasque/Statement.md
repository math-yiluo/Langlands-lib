# Flasque Godement resolutions and cohomology with supports

Author: Worker 3.

Documentation corrections I003 and I023: Worker 100, with source and publication
audit contributions from Worker 291.

This pair defines eight propositions and their conjunction
`Langlands.Cohomology.FlasqueGodementCohomologyStatements`. They concern the
published Godement, compact-support and derived-section constructions. The
statements cover flasqueness of Godement terms, acyclicity of flasque sheaves,
and the resulting computation of ordinary and compactly supported cohomology by
Godement complexes, on topological spaces and on small etale sites of schemes.
These are theorem-statement definitions, not proofs. No conclusion is supplied
as data, as a hypothesis of another component, or as a record field.

## Objects

All topological components use a space `X : TopCat.{u}`, a commutative ring
`R : Type u`, and the category `TopCat.Sheaf (ModuleCat.{u} R) X` of sheaves of
`R`-modules on the open sets of `X`. This is the category on which the
published compact-section and derived-section functors are defined. Those
published functors fix one universe `u` for the space, the ring and the module
carriers, and this pair inherits that restriction. No Hausdorff, local
compactness, paracompactness or finiteness hypothesis is imposed anywhere.

- `Flasque.spacePoints X` sends `x` to Mathlib's point
  `Opens.pointGrothendieckTopology x` of the open-set site. Its fiber functor
  is the colimit over open neighborhoods of `x`, that is, the stalk.
- `Flasque.godementComplex X R F` is the published
  `Langlands.Sheaf.Godement.complex` for these points. Its degree-zero term is
  the product, over all `x` in `X`, of the skyscraper sheaves of the stalks.
  Its sections over an open `U` are canonically the product of the stalks
  `F(x)` over `x` in `U`, which is Grothendieck's `C^0(F)`. This is a canonical
  identification, not a definitional equality. Higher terms follow the
  published iterated-cokernel recurrence, `C^n = C^0(Q_n)` with
  `Q_(n+1) = coker(Q_n -> C^0(Q_n))`. It agrees with the source formula
  `C^n(F) = C^0(C^(n-1)(F)/Im C^(n-2)(F))`, because the image of `C^(n-2)` in
  `C^(n-1)` is the image of `Q_(n-1)`.
- `IsFlasque` is Mathlib's `TopCat.Sheaf.IsFlasque`: every restriction map is
  an epimorphism, which for modules means surjective. The source definition
  asks that every section over an open subset extend to the whole space. The
  two are equivalent: restricting a global extension gives an extension to any
  intermediate open, and conversely the source condition is the case of the
  restriction from the whole space.
- Supports are those of the published `Langlands.Sheaf.CompactSupport`: the
  set of points where the germ is nonzero. This is the source's complement of
  the largest open set on which the section vanishes, and it is closed.
  `CompactSupport.globalSections` is the source's `Gamma_Phi` for `Phi` the
  family of all closed subsets. `CompactSupport.functor` is `Gamma_Phi` for
  `Phi` the family of compact closed subsets. Both families are nonempty,
  closed under finite unions and under passage to closed subsets, so they are
  antifilters of closed sets in the source's sense. Supports with respect to
  other families are not constructed in the Library and are not asserted here.
- `TopologicalDerivedSections.ordinaryCohomology X R n`,
  `compactCohomology X R n` and `forgetSupport X R n` are the published right
  derived functors of the two section functors, computed in the category of
  `R`-module sheaves, and the derived support-forgetting map.

The two scheme components use an actual scheme `X : Scheme.{u}` and a
commutative ring `R : Type u`. `Geometry.EtaleGodement.EtaleSheaf X R` is the
category of sheaves of `R`-modules on Mathlib's small etale site. Its objects
lie in universe `u + 1`, and so do its hom-sets.
`Geometry.EtaleGodement.complex X R F` is the published Godement complex for
one geometric point over each scheme point, using a separable closure of the
residue field. The published module proves this family of points conservative.
`Geometry.EtaleDerivedSections.cohomology X R n` is the right derived functor
of `sections X R`, the sections at the final object of the small etale site.

## The eight propositions

| Declaration | Hypotheses and asserted conclusion |
| --- | --- |
| `Langlands.Cohomology.GodementTermFlasqueStatement` | For every module sheaf `F` and every `n`, the degree-`n` term of `godementComplex X R F` is flasque. |
| `Langlands.Cohomology.FlasqueShortExactStatement` | For a short exact sequence `0 -> F' -> F -> F'' -> 0` of module sheaves with `F'` and `F` flasque, `F''` is flasque. Ordinary sections and compactly supported sections both carry the sequence to a short exact sequence of modules. |
| `Langlands.Cohomology.InjectiveSheafFlasqueStatement` | Every injective object of the category of module sheaves is flasque. |
| `Langlands.Cohomology.FlasqueAcyclicityStatement` | If `F` is flasque, then for every `q`, both `ordinaryCohomology X R (q + 1)` and `compactCohomology X R (q + 1)` vanish at `F`. |
| `Langlands.Cohomology.GodementComputesCohomologyStatement` | Godement complexes compute both ordinary and compactly supported cohomology, through the canonical comparison maps described below. |
| `Langlands.Cohomology.CompactSpaceSupportComparisonStatement` | If `X` is compact, then `forgetSupport X R n` is an isomorphism for every `n`. |
| `Langlands.Cohomology.EtaleGodementTermAcyclicStatement` | For every etale module sheaf `F` and all `n` and `q`, `cohomology X R (q + 1)` vanishes at the degree-`n` Godement term of `F`. |
| `Langlands.Cohomology.EtaleGodementComputesCohomologyStatement` | The etale Godement complex computes small-etale cohomology, through the canonical comparison map described below. |

The comparison targets use the same canonical map as the published
`Langlands.Cohomology.AcyclicResolutionComparisonStatement`. Let `G` be the
section functor and `I` an injective resolution of `F`. The map takes homology
of the image under `G` of a lift `phi` from the Godement complex to `I`, and then
applies the inverse of Mathlib's identification of `I` with the right derived
functor. The target asserts that this composite is invertible in every degree.
The hypotheses are as follows:

- `ε` is a chain map from `F`, concentrated in degree zero, to the Godement
  complex. Its degree-zero component must equal the constructed coaugmentation
  (`Sheaf.Godement.augmentation`, respectively
  `EtaleGodement.coaugmentation`). Such a chain map exists and is unique: it
  corresponds under `CochainComplex.fromSingle₀Equiv` to the coaugmentation,
  whose composite with the first differential vanishes by the published
  `augmentation_d`. The hypothesis therefore only fixes the augmentation; it
  does not assume that the augmentation is a quasi-isomorphism. That is a
  separate Godement exactness theorem.
- `phi` is any lift with `ε ≫ phi = I.ι`. Existence and homotopy uniqueness of
  such lifts, and independence of the comparison from `I` and `phi`, are the
  published `ResolutionLiftStatement` and
  `ResolutionComparisonIndependenceStatement`.

These targets choose to quantify over any `ε` with the prescribed degree-zero
component, so their formulation does not depend on naming a particular
chain-map construction. Such a construction is already published in
[`Langlands.Sheaf.Godement.ExactnessStatement`](../../Sheaf/Godement/ExactnessStatement.md):
`Langlands.Cohomology.CokernelComplex.augmentationMap`, with its degree-zero
formula `augmentationMap_f_zero`, naturality lemma
`augmentationMap_naturality`, and natural transformation `augmentationNat`.
Specializing it to the respective Godement endofunctor and coaugmentation
gives the required `ε`. This module does not import that construction; its
quantified formulation is a design choice. The construction and these
identities do not prove exactness of the augmented complex or this pair's
flasqueness, acyclicity and comparison assertions.

## Original-source correspondence

The primary topological source is Grothendieck, *Sur quelques points
d'algebre homologique*, Tohoku Math. J. (2) 9 (1957), section 3.2 and 3.3,
printed pp.157-160 (PDF pp.39-42 of the retained 103-page scan). All four pages
were rendered from the retained scan and read visually.

| Targets | Original location and precise relation |
| --- | --- |
| Families of supports and derived functors | Tohoku p.157: an antifilter `Phi` of closed subsets, the support convention, `Gamma_Phi`, its derived functors `H^p_Phi(X,F)`, and their computation from any right resolution by `Gamma_Phi`-acyclic sheaves. |
| `InjectiveSheafFlasqueStatement`, `FlasqueAcyclicityStatement` | Tohoku p.158, Lemme 3.3.1: if a class `M` satisfies conditions (i)-(iii), every injective object is in `M` and `R^pF(M) = 0` for `p > 0`. Tohoku p.159, Proposition 3.3.2(1) and its Corollaire: flasque sheaves satisfy the conditions for every `Phi`, so `H^p_Phi(X,F) = 0` for `p > 0`. The two components are this conclusion at the two families above. |
| `FlasqueShortExactStatement` | Condition (iii) of Lemme 3.3.1 for the class of flasque sheaves, as asserted in Proposition 3.3.2(1), p.159, for the two families above. Grothendieck leaves its proof to Godement's book or to the reader. The target keeps the source hypothesis that both `F'` and `F` are flasque. Mathlib's stronger `TopCat.Sheaf.IsFlasque.epi_of_shortExact`, which needs only a flasque `F'`, concerns sections of abelian-group sheaves on an open set. It is not invoked or restated. |
| `GodementTermFlasqueStatement` | Tohoku p.159: a sheaf whose sections over `U` are a product of sets over the points of `U` is flasque. Tohoku p.160, Resolution de l'identite: the canonical resolution has `C^0(F)` the product of the stalks, and its terms `C^n` are flasque. |
| `GodementComputesCohomologyStatement` | Tohoku p.160: the `C^n(A)` are flasque, hence `Gamma_Phi`-acyclic for every antifilter `Phi`, so `H^n_Phi(X,F) = H^n(Gamma_Phi C(F))`. The Lean target states this identification as invertibility of the published canonical comparison, for `Phi` all closed sets and compact closed sets. |
| `CompactSpaceSupportComparisonStatement` | Derived, not stated in the source. On a compact space every closed set is compact, so the two families of supports coincide. The published inclusion of compact sections into sections is then an isomorphism, and so is its derived map in every degree. It is the topological case of identifying compactly supported and ordinary cohomology for compact spaces. |

Tohoku states Proposition 3.3.2 for sheaves of abelian groups. Page 159 also
embeds every sheaf of `O`-modules into a flasque sheaf of `O`-modules.
Condition (iii) concerns only the underlying abelian sheaves. Lemme 3.3.1 is
therefore applied in the abelian category of sheaves of `R`-modules, here
modules over the constant sheaf of rings `R`. The Lean derived functors are
computed in that category. Soft sheaves and paracompactifying families,
Proposition 3.3.2(2), are not used or formalized here.

The scheme components use SGA 4. P. Deligne, Expose XVII, Tome 3, section
4.2: Definition 4.2.2 and Proposition 4.2.3(i), printed p.326, assert that the
Godement terms `C^n(F)` relative to a conservative family of points are
flasque. The proof at the top of printed p.327 obtains this because they are
direct images of sheaves on a discrete space. Remarks 4.2.4 and 4.2.5, p.328,
extend this to points of sites and to Modules. Proposition 4.2.3(i) refers to
"(V 3.7)" for flasqueness. In the retained Tome 2 scan, section 3 of Expose V
ends with Exercise 3.6, and flasque is Definition 4.1. J.-L. Verdier,
Expose V, Tome 2:

- Definition 4.1, printed p.29: a Module is flasque when `H^q(X,F) = 0` for
  every object `X` of the topos and every `q > 0`.
- 4.4, printed p.30: flasqueness depends only on the underlying abelian sheaf.
- 4.6, printed p.30: injective sheaves are flasque.
- 4.8, printed p.31: for topological spaces the terminology agrees with
  Godement's classical one.
- Proposition 4.9(1), printed p.31: direct images preserve flasque Modules.
  The proof of XVII 4.2.3(i) uses this.

`EtaleGodementTermAcyclicStatement` is Definition 4.1 at the final object of
the small etale site, whose sections are the published `sections X R`. It is
weaker than full SGA 4 flasqueness, which concerns every etale object.
`EtaleGodementComputesCohomologyStatement` combines that acyclicity, the
exactness of the Godement resolution (XVII 4.2.3), and the computation of
derived functors from acyclic resolutions (Tohoku p.158, Corollaire of
Lemme 3.3.1). It is a derived formulation.

These scheme components concern the published scheme etale construction.
They do not identify an algebraic etale site with Berkovich's analytic site.

## Relation to Berkovich and Harris

Berkovich's supplied unfinished 1995-1996 manuscript, section 1.5, p.10, recalls
the Godement resolution of SGA 4 XVII 4.2 on the etale site of `X(G)` with
properties (i)-(iii), including flabbiness. Example 1.1.3, p.3, fixes the
morphism `b : X -> X(G)`. Proposition 1.5.1, p.10, asserts that the inverse
images (pullbacks) `b^*(C^m(F))` are soft sheaves on the analytic etale site
`X_et`. Corollary 1.5.2(i), pp.11-12, gives the compact-support comparison
`H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` for analytic `G`-spaces.
Harris 1999, section 2,
p.304, uses a smooth equivariant resolution that is acyclic for compactly
supported cohomology. Those analytic and equivariant assertions are not
asserted by this pair. It supplies the ordinary topological and scheme-etale
counterparts: flasqueness, acyclicity for ordinary and compactly supported
sections, and the computation of cohomology by Godement complexes. Softness,
the analytic etale site, smooth group actions, and the Shimura and Drinfeld
specializations remain separate obligations. No banality, torsion or
characteristic hypothesis is introduced.

## Registered sources

- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, Tohoku 1957, retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Printed pp.157-160 were read visually.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305 (1973), retained file
  `literature/SGA 4 Tome 3 (1973 original scan), including Deligne Expose XVII.pdf`,
  SHA-256 `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
  Printed pp.326-328 (PDF pp.329-331) were read visually.
- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270 (1972), retained file
  `literature/SGA 4 Tome 2 (1972 original scan), including Verdier Expose V.pdf`,
  SHA-256 `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`.
  Printed pp.1-3 and 28-31 (PDF pp.3-5 and 30-33) were read visually.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
  member PDF SHA-256
  `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
  in the same-title literature folder. Example 1.1.3, p.3, and section 1.5,
  pp.10-12, were independently read for this correction and are cited for
  context only.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, p.304, cited for the intended application only.

No claim is made to have read either SGA 4 volume in full.

## Formal dependencies and checks

The pair imports published modules by Lean name. Their bytes in the current
Library commit `a6142598ca59c1c7c4408d715a4ae77cfe7469bc` equal the local
workspace bytes:

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.Cohomology.TopologicalDerivedSections` | `f2c3e8f0d296eb10d666bb649c121362cf184069db96aa3c27d4b50f21b243c9` | `b3e584b5f40b826f896f9bc0219a67f55c25073f45458b35eb92851ad5b1d7f8` |
| `Langlands.Sheaf.CompactSupport` | `65a924376d143fa231a58338848c323fcb3dad4f4f5a0be814b8a360684757b5` | `ba155085ac48fb1083516a79b184f73bdf3a0a1ed8dd550a6709942825e34e98` |
| `Langlands.Sheaf.Godement` | `fcf2515607d29714f845b8218a251d44d218a2aceb1141ee84703fb8f7eaf3d0` | `a6ee81493065823de1e872289581afacc635b4c7a6b7d30114884a8eafec9b36` |
| `Langlands.Cohomology.CokernelComplex` | `0f034f1d42a5f8d3c72f47635ad6bea750b94e1cf8c20f5b54e2d0514dac2f11` | `7ff7d71403c074ea426d44b884d415ff11924d4299ff316c15aec2f79776f794` |
| `Langlands.Geometry.EtaleGodement` | `d0aded4edc3cf5bcff2bba08a843fc3836b2320cb6aadcc6fea2b8a7bafee461` | `07d39153a258525766ace53417297a7b14b9f3b951c9fadbacc085f991c46718` |
| `Langlands.Geometry.EtaleDerivedSections` | `66abab55a791a1aabad61b3a9c3ce8bfffb35b70312b24c71c2940b1bb74d5df` | `cc73094a54f44304d8cbf80e756fd07761a88a44862a198590437ccd80eaa2e7` |

These constructions are by Worker 13. The Mathlib imports
`Mathlib.Topology.Sheaves.Flasque` and `Mathlib.Topology.Sheaves.Points`
provide `TopCat.Sheaf.IsFlasque` and `Opens.pointGrothendieckTopology`. The
environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Development check `7f965453-014b-48e8-adba-c94713450c64` built this module with
no errors or warnings. It inspected
`Langlands.Cohomology.FlasqueGodementCohomologyStatements` as a definition
returning `Prop`, with universe parameter `u` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Check
`9ac6b16e-e2a4-412c-aa88-dca6d610f124` printed every component, both helper
abbreviations and the conjunction with universe annotations, and the output
was read. The prints show:

- the flasque predicate is `TopCat.Sheaf.IsFlasque`, at the sheaf category of
  the published functors;
- the Godement complex uses `Opens.pointGrothendieckTopology` at every point;
- the short-exactness target assumes the first two terms flasque;
- the augmentation equation pins the degree-zero component;
- the scheme components use the published small-etale constructions.

Compilation and inspection establish well-formed statements; they do not prove
any of the eight assertions.
