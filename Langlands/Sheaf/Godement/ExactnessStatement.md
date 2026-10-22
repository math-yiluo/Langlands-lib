# Exactness of the constructed Godement resolution

Author: Worker 3.

This pair defines seven propositions and their conjunction about the published
cokernel and Godement constructions. The augmentation chain map, its naturality,
and the retraction on a chosen point fiber are constructed, and their intrinsic
identities are proved. The seven theorem assertions remain separate obligations;
defining them does not prove them.

## Objects, maps and hypotheses

In an abelian category A, fix an actual endofunctor T and a natural
transformation eta from the identity to T. The imported construction defines
residual functors Q and term functors C by

    Q_0 = identity,    Q_(n+1) = coker(eta at Q_n),    C_n = Q_n followed by T.

Its differential C_n to C_(n+1) is the cokernel projection followed by the
coaugmentation at Q_(n+1). These are actual functors, categorical cokernels
and natural transformations. No resolution, cohomology, or exactness property
is included as a field of their definitions.

`CokernelComplex.augmentationMap` is the chain map from the input object,
concentrated in degree zero, to this nonnegative cochain complex. It is built
using `CochainComplex.fromSingle₀Equiv` and the already proved equation that the
augmentation followed by the first differential vanishes.
`augmentationMap_f_zero` proves that its degree-zero component is eta.
`augmentationMap_naturality` proves its naturality by reducing equality of
these chain maps to their degree-zero components and applying eta's naturality.
`augmentationNat` packages those maps as a natural transformation.

For an actual site `(C,J)` with points p_i, the imported Godement functor is

    T(F) = product over i of (skyscraper at p_i of the fiber of F at p_i).

Its coaugmentation is the product of the fiber/skyscraper adjunction units.
`fiberRetraction F i` applies the i-th fiber functor to the i-th product
projection, then applies that adjunction's counit. The proved identity
`fiber_coaugmentation_retraction` says that the fiber of the coaugmentation
followed by this retraction is the identity. The proof uses the published
projection formula and the adjunction triangle identity. This construction
does not require conservativity, an abelian coefficient category, or exactness.

The seven component targets are:

| Declaration | Hypotheses and asserted conclusion |
| --- | --- |
| `Langlands.Cohomology.CokernelResolutionStatement` | For any abelian A, T and eta, monicity of eta on every object implies that the actual augmentation chain map is a quasi-isomorphism. Neither additivity nor exactness of T is assumed. |
| `Langlands.Cohomology.CokernelResolutionFunctorExactnessStatement` | When T is additive and preserves finite limits and finite colimits, and eta is monic on every object, every Q_n and C_n is additive and preserves finite limits and finite colimits. |
| `Langlands.Sheaf.Godement.ResolutionStatement` | For an actual site, actual points, and an abelian coefficient category with the displayed products, colimits and sheafification, joint faithfulness of the point-fiber functors implies that the actual Godement augmentation is a quasi-isomorphism. |
| `Langlands.Sheaf.Godement.ModuleZeroFunctorExactnessStatement` | For module coefficients over an arbitrary ring, the actual degree-zero Godement functor is additive and exact. No joint-faithfulness assumption is imposed. Exactness is the conclusion, not an input. |
| `Langlands.Sheaf.Godement.ModuleTermFunctorExactnessStatement` | With module coefficients and jointly faithful point fibers, every actual residual and term functor is additive and exact. Exactness of the degree-zero functor is not assumed. |
| `Langlands.Sheaf.Godement.ModuleFiberSplitResolutionStatement` | On any selected point fiber, the actual augmentation has a chain retraction whose degree-zero map is `fiberRetraction`. The augmentation followed by the retraction is the identity, and the opposite composite is homotopic to the identity. No joint-faithfulness assumption is imposed. |
| `Langlands.Geometry.EtaleGodement.ResolutionExactnessStatement` | For an actual scheme X and commutative coefficient ring R, the published construction on the small etale site gives a quasi-isomorphic augmentation for every R-module sheaf and exact additive term functors in every degree. The published geometric points already supply the needed conservativity and monicity. |

`Langlands.Cohomology.GodementExactnessStatements` is their conjunction.
Every component is a `def` returning `Prop`. The statements do not assume any
of the seven conclusions in order to be defined.

Here exactness of an additive functor is expressed by preservation of finite
limits and finite colimits. Quasi-isomorphism of the augmentation identifies
degree-zero cohomology with the input and makes all positive-degree cohomology
zero. It does not assert acyclicity after applying compactly supported sections.

The general site target keeps the site-object, site-morphism, point-fiber,
point-index, coefficient-object and coefficient-morphism universes independent.
It explicitly requires products indexed in both the fiber and family universes,
colimits of the fiber size, and `HasSheafify`. The module targets use one universe
w for module carriers, point fibers and the point-index set; the ring universe
is independent. Their `LocallySmall.{w} C` hypothesis bounds the site hom-sets at
that size. This is the size hypothesis used by the actual filtered-fiber
construction, not a geometric finiteness, banality or torsion hypothesis.
The scheme specialization uses the universe choices of `EtaleGodement`: the
scheme's underlying space and R are in u; small-etale objects and module objects
are in u+1, with hom-sets in u.

The splitting target is stated on the image of the actual complex under the
fiber functor, with the actual image of the augmentation. Its contracting
homotopy is existentially quantified; no homotopy is supplied as input.
The retraction in degree zero is fixed by the displayed counit formula.
No particular formula for all components of the homotopy is asserted.
Mathlib's convention is `Homotopy f g`: f = dh + hd + g, with h of degree -1.
Thus the target expresses r;a - identity = dh + hd, while a;r is exactly the
identity. This is the split-resolution assertion with an explicit retraction,
not just an isomorphism of accidentally equal cohomology objects.

## Original-source correspondence

The main original is SGA 4, Tome 3, Expose XVII by P. Deligne, section 4.2,
printed pp.326-328 (expose-local pp.75-77, PDF pp.329-331). Those pages were
read visually from the original scan, including the whole proof of 4.2.3.

| Targets or constructions | Original location and precise relation |
| --- | --- |
| Cokernel complex and augmentation | Grothendieck, Tohoku (1957), section 2.5, Example (a), p.150 (PDF p.32), constructs a resolution of the identity from an exact endofunctor with monic natural coaugmentation. SGA 4 XVII 4.2.2, p.326, gives the Godement recurrence and its augmentation. |
| `CokernelResolutionStatement` | A derived separation of the exact-resolution part of those constructions: the short exact sequences Q_n to C_n to Q_(n+1) and the differential's factorization give exactness. This part uses monicity of eta and actual cokernels, independently of exactness of T as a functor. It is not quoted as a separate theorem with these weaker hypotheses in the source. |
| `CokernelResolutionFunctorExactnessStatement` | The three-by-three induction in the proof of SGA 4 XVII 4.2.3(ii), p.327. That argument applies in any abelian category to an exact additive T and monic eta. Tohoku p.150 supplies the same general abelian-category construction. |
| `ResolutionStatement` | SGA 4 XVII 4.2.1-4.2.2, p.326, and 4.2.4, p.328, transfer a conservative point family to the associated topos and make the coaugmentation monic. The Lean version uses the more direct joint-faithfulness hypothesis and the already proved `mono_coaugmentation_of_jointlyFaithful`; its remaining exactness assertion is the general cokernel-resolution argument. |
| Module degree-zero and higher-term exactness | SGA 4 XVII 4.2.3(ii) and its proof, pp.326-327: inverse image to the discrete point family and its direct image are exact, giving exactness of C_0; the three-by-three induction gives the residual and higher-term functors. Remark 4.2.5, p.328, treats module-valued sheaves on ringed topoi. Here coefficients are a fixed possibly noncommutative ring and the maps are R-linear: exact filtered module colimits give exact fibers, and products of modules give exact skyscrapers and their product. This is the constant-coefficient module formulation, not a formalization of arbitrary ringed topoi. |
| Retraction and fiber splitting | SGA 4 XVII 4.2.3(iii), p.326, and the proof at the bottom of p.327 and top of p.328. The coaugmentation followed by the counit on fibers is the identity; applying this at each residual gives split short exact sequences and hence a contraction of the augmented complex. The Lean target records existence of that contraction with the specified retraction at degree zero. |
| Scheme specialization | Apply the preceding site statements to the actual geometric points and module-valued small-etale sheaves constructed in the published `EtaleGodement` module. This is an explicitly derived application of SGA 4 XVII 4.2.4-4.2.5, not a claim that an algebraic etale site is Berkovich's analytic site. |

The residual indexing is explicit. Our Q_0 is F, and Q_n corresponds to the
source's Z^(n-1). The source takes the cokernel of the preceding differential;
our recurrence takes the cokernel of the coaugmentation at the current
residual. These agree by the cokernel universal property because the preceding
cokernel projection is epic. This is a canonical identification, not an assertion
that the two presentations are definitionally identical in Lean. The unnumbered
short exact sequence near the bottom of original p.327 prints Z^(n+1) on its
left. The diagram above it and the substitution F to Z^(n-1)(F) on p.328 show
that the left term is Z^(n-1). Our recurrence follows that diagram and
substitution; it does not adopt the misindexed printed line.

Berkovich's supplied unfinished 1995-1996 manuscript, section 1.5, p.10,
items (a)-(b), recalls the non-equivariant Godement functor and explicitly
attributes its exactness, flabbiness and pointwise splitting to SGA 4 XVII
4.2.3. The present pair supplies the exactness and splitting theorem interfaces
for that recalled construction. Berkovich's subsequent smooth equivariant
construction and Proposition 1.5.1/Corollary 1.5.2, pp.11-12, require additional
arguments. The supplied manuscript's numbering is retained; no identification
with a differently numbered historical version is assumed.

Registered originals and retained bytes:

- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4, Tome 3, Lecture Notes in
  Mathematics 305, Springer (1973), Expose XVII. Original 643-page scan obtained
  from [SLMath](https://library.slmath.org/nonmsri/sga/sga/pdf/sga4-3.pdf).
  Retained file:
  `literature/SGA 4 Tome 3 (1973 original scan), including Deligne Expose XVII.pdf`.
  SHA256 `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
  The cited original pages and title/contents were checked; no full-volume
  reading claim is made. The later Cornell retypesetting was only a locator
  lead and is not the cited edition.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algebre homologique*, Tohoku Math. J.
  (2) 9 (1957), both instalments in the retained 103-page scan.
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Section 2.5, Example (a), p.150/PDF p.32 was read and visually checked.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, supplied
  unfinished manuscript. Registered folder SHA256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
  member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
  The fifteen-page supplied manuscript was read during the preceding source
  audit; section 1.5 was rechecked for this pair.

## Formal dependencies and remaining scope

This pair imports the published construction modules by their Lean names.
The exact dependency version is the current Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`; the following local bytes were
verified equal to that public tree:

| Module | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `Langlands.Cohomology.CokernelComplex` | `0f034f1d42a5f8d3c72f47635ad6bea750b94e1cf8c20f5b54e2d0514dac2f11` | `7ff7d71403c074ea426d44b884d415ff11924d4299ff316c15aec2f79776f794` |
| `Langlands.Sheaf.Godement` | `fcf2515607d29714f845b8218a251d44d218a2aceb1141ee84703fb8f7eaf3d0` | `a6ee81493065823de1e872289581afacc635b4c7a6b7d30114884a8eafec9b36` |
| `Langlands.Geometry.EtaleGodement` | `d0aded4edc3cf5bcff2bba08a843fc3836b2320cb6aadcc6fea2b8a7bafee461` | `07d39153a258525766ace53417297a7b14b9f3b951c9fadbacc085f991c46718` |

These modules are authored by Worker 13; no unpublished construction was
copied or assumed. The new augmentation chain map and fiber retraction are
added in this pair. Their proved intrinsic equations do not prove the seven
resolution, exactness or contraction statements.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Additional Mathlib imports provide actual quasi-isomorphisms and chain
homotopies.

Development check `15312320-6a52-4dd6-ae51-82ef588926c1` in that environment
completed a Lake build of this module and exact declaration inspection with no
errors or warnings, for Lean source SHA256
`66c45b9d460fce4935aa869c1db1c932ca9e60fe95188ea3a6895ae9d0037435`.
The inspected declaration is a definition returning `Prop`, with universe
parameters `u`, `v`, `w`, `wI`, `uA`, `vA`, `uR`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
Its target fingerprint is
`8abc8cb8a8c5c33f88dd69a37d43277d966a695a44665d59cb9dc707a0755201`.

A separate print of every component, the conjunction, and the two new
constructions in the same environment (check
`13323b0b-b557-4aea-8405-aa840490f4d6`) was read, including the independent
universe parameters, the placement of joint faithfulness and exactness
hypotheses, the actual image-augmentation in the splitting target, its
prescribed degree-zero retraction, and both composite directions.
The pretty-printer shows the local names `η` and `a` as non-dependent
`have` bindings; each is a beta-redex with the same meaning as the displayed
`let`. The new intrinsic proofs were also inspected for assumptions; they use
only `propext`, `Classical.choice` and `Quot.sound`. Compilation and these
checks do not prove the seven assertions.

The analytic equivariant site, its comparison to a topos, smooth group and
Galois actions, flabbiness/softness, compact-support acyclicity, inverse-system
compatibilities and the Harris spectral-sequence and Shimura specializations
remain distinct obligations. In particular, this pair supplies no input
proof of compact-support acyclicity to the published acyclic-resolution
comparison statements. It introduces no banality assumption and makes no
nonsplit local-global assertion. The broad Harris-Berkovich framework remains
open. Independent acceptance and publication of these statements, and proofs
of their mathematical assertions, are separate requirements.
