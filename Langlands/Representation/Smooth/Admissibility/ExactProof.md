# Admissibility in a smooth short exact sequence

`Langlands.admissibleShortExact` proves the entire published proposition
`Langlands.AdmissibleShortExactStatement` from
`Langlands.Representation.Smooth.Admissibility.ExactStatement`. The closing
theorem has the type `AdmissibleShortExactStatement (G := G) (U := U) (V := V)
(W := W)`, so the group `G` and the carriers `U`, `V`, `W` keep four
independent universes `uG`, `uU`, `uV`, `uW`. The ambient section assumptions
are those of the statement: a group with a topology, and complex module
structures on the three carriers. Everything else is introduced from the
proposition's own binders: the `IsTopologicalGroup` instance, the hypothesis
that every open subgroup contains a compact open subgroup, the three complex
representations `rho`, `sigma`, `tau`, the intertwiners `i` and `p`,
injectivity of `i`, surjectivity of `p`, the equality
`LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap`, and smoothness
of `sigma`. The conclusion is
`IsAdmissible sigma ↔ IsAdmissible rho ∧ IsAdmissible tau`, where
admissibility is the project definition: smoothness together with
`Module.Finite ℂ` of the fixed vectors of **every** open subgroup.

No topology or finite dimension is imposed on the carriers. The proof uses no
local compactness, countability, measure on `G`, chosen splitting,
admissibility premise or theorem-valued input beyond the statement's binders.

## Implemented proof

The module contains two helper theorems and the closing theorem.

1. `fixedVectorMap_exact` holds for an **arbitrary** subgroup `K`, compact or
   not. Let `i_K` and `p_K` be the restrictions
   `Compact.fixedVectorMap rho sigma i K` and
   `Compact.fixedVectorMap sigma tau p K` to fixed vectors. The theorem proves
   Mathlib's `Function.Exact i_K p_K`. If a `K`-fixed vector `v` of `sigma`
   satisfies `p v = 0`, then `v` lies in the kernel of `p`, hence in the range
   of `i`, say `v = i u`. For `k` in `K`, equivariance gives
   `i (rho k u) = sigma k (i u) = sigma k v = v = i u`, and injectivity of `i`
   gives `rho k u = u`. So `u` is `K`-fixed and `i_K u = v` by subtype
   extensionality. Conversely `p (i u) = 0` because `i u` lies in the range of
   `i`, which equals the kernel of `p`. No splitting is chosen.
2. `isAdmissible_iff_of_shortExact` proves the equivalence. It lets `S` be the
   set of compact open subgroups. The statement's cofinality hypothesis says
   exactly that every open subgroup contains a member of `S`. Smoothness of
   `tau` is the published `isSmooth_of_surjective p hp hsigma`. For each
   compact open subgroup `K`, the published
   `Compact.fixedVectorSurjectivity` (instantiated at universes `uG`, `uV`,
   `uW` with the smooth `sigma` and `tau`) gives surjectivity of `p_K`.
   - Forward: if `sigma` is admissible, the published
     `isAdmissible_of_injective i hi` gives admissibility of `rho`. For
     `tau`, the published `isAdmissible_iff_of_cofinal S` reduces
     admissibility to smoothness and `Module.Finite ℂ` of the `K`-fixed
     vectors for `K` in `S`. Finite generation of the `K`-fixed vectors of
     `sigma` then passes along the surjection `p_K` by
     `Module.Finite.of_surjective`.
   - Backward: if `rho` and `tau` are admissible, `isAdmissible_iff_of_cofinal
     S` again reduces admissibility of `sigma` to its given smoothness and to
     compact open `K`. For such `K`, the fixed-vector sequence
     `i_K`, `p_K` is exact by step 1 and `p_K` is surjective, so
     `Module.Finite.of_exact` gives finite generation of the middle term from
     finite generation of both ends.
3. `admissibleShortExact` introduces all binders of the proposition and applies
   `isAdmissible_iff_of_shortExact`.

Admissibility for every open subgroup comes from the cofinality passage in
`isAdmissible_iff_of_cofinal`: fixed vectors of a larger subgroup form a
submodule of those of a smaller one. That theorem and
`isAdmissible_of_injective` carry an `[IsNoetherianRing R]` assumption, which
is satisfied by the field `ℂ` through instance inference. The finiteness
results hold over any ring, so the proof does not convert finite generation to
finite dimension. Smoothness of `rho` is never needed separately, because it
is either part of the assumed admissibility of `rho` or a conclusion of
`isAdmissible_of_injective`.

The Mathlib interfaces, at commit
`5ed2965256430c3649e86755f9576b54eca72435`, are:

- `Module.Finite.of_exact`, `Mathlib/RingTheory/Finiteness/Finsupp.lean`,
  lines 153-164: if `f`, `g` are exact, `g` is surjective, and the outer
  modules are finite, the middle module is finite (Stacks 0519 (1)).
- `Module.Finite.of_surjective`, `Mathlib/RingTheory/Finiteness/Basic.lean`,
  line 247: finite generation passes along a surjective linear map.

## Source and reformulation

The target derives from Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, *Smooth representations*,
revision June 16, 2019: Proposition II.1.3 and Corollary II.1.4, printed/PDF
page 4. Casselman's proposition is fixed-vector exactness for compact open
subgroups, proved by averaging. The corollary deduces that the middle term of
a short exact sequence of smooth representations is admissible exactly when
both ends are. Admissibility and smoothness are defined on page 2, and the
averaging operator on pages 2-3. Worker 261 read pages 1-4 of the retained
original and checked its fingerprint.

- Literature ID: `casselman-2019-smooth-representations`.
- PDF SHA256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- File: `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

Casselman works over a locally profinite group with countability conditions
and a Noetherian coefficient ring containing the rationals. The formal target
replaces these with complex coefficients, a topological group, and
compact-open cofinality. The implemented proof justifies this weakening.
Exactness in the middle (step 1) needs only injectivity of `i` and
range-equals-kernel, for any subgroup. Averaging enters only through the
published `Compact.fixedVectorSurjectivity`, which needs a compact open
subgroup and smoothness of `sigma` and `tau`. Cofinality then reaches every
open subgroup. The proof follows Casselman's route, using Mathlib's
exact-sequence finiteness lemma in place of the corollary's one-line
deduction.

## Dependencies and independence audit

The direct project imports are the following published pairs. Each was read
in the Library snapshot `efef3e8dad656737d40a56704c6373cf894d3cbd`, where the
listed hashes were computed; none is modified.

| Module | Used declarations | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- | --- |
| `Smooth.Admissibility.ExactStatement` | target `AdmissibleShortExactStatement` | `3e0e7e7d92c7da8a00137a2ad51d23ab6550955102538def39c087b243bb1479` | `450aa6d5498149c1c77e2a579311a61b3a715ae768ecd90385a0eb651ead65c8` |
| `Smooth.Admissibility.CofinalProof` | `isAdmissible_iff_of_cofinal` | `b01c589f73cb2488a38477ea95bbb6adda0863507efbcb54e561843e467c112a` | `df9117b7ccc80b412fac95816eda27bb0bb18762909c8b0ec39ff35a9a398b59` |
| `Smooth.Admissibility.EmbeddingProof` | `isAdmissible_of_injective` | `39d5054b926521075ff14f661c16733c8a40e9782b9ba854f66b7d815f8ecccc` | `c43917217a65d2a6b0c1808c5ab739c99d55c5065dca49196ed9e65d131a4808` |
| `Smooth.Transfer.SubquotientProof` | `isSmooth_of_surjective` | `8e26bf64cb2eff5bfdc6037d5d6c52650bd92944a1c9ef0b57c4f12cc3b0d1cd` | `c1f909953edfa360eacae0f2f266025e1dc1ae7000755873f9ad5d3d2985eb0b` |
| `Compact.SurjectivityProof` | `Compact.fixedVectorSurjectivity` | `d1a89efb911951f85a1a691f4f5da3e76101f949eafae0d28b4e193e2fc5a20b` | `5c2ab76bcc362821fcb7363e69e752a0534f043779fe0a415ffbee792fad90f4` |

All module names above are under `Langlands.Representation`.
`Compact.fixedVectorMap` comes from `Langlands.Representation.Compact.Definitions`,
and `IsSmooth`, `IsAdmissible` and `fixedVectors` come from
`Langlands.Representation.Smooth.Definitions`, both through these imports.
The only direct Mathlib import is `Mathlib.RingTheory.Finiteness.Finsupp`.

The complete project import closure is 15 modules:
`Representation.Compact.{Definitions, FiniteMean, ProjectionStatement,
ProjectionProof, SurjectivityStatement, SurjectivityProof}` and
`Representation.Smooth.{Definitions, FixedVectors.Definitions,
Transfer.SubquotientStatement, Transfer.SubquotientProof,
Admissibility.CofinalStatement, Admissibility.CofinalProof,
Admissibility.EmbeddingStatement, Admissibility.EmbeddingProof,
Admissibility.ExactStatement}`. These are foundational smooth-representation
and compact-averaging units. None belongs to, or depends on, the excluded
finite-length bridge and analytic segment classification task `aca8805b`, the
special-head multisegment exhaustion `3bfb61fa`, ordered special-head
existence `ebea9a8a`, quotient coverage `20e4e1c6`, tempered block uniqueness
`52e97845`, `SquareIntegrableLanglandsClassification` (`1cb45da2`),
square-integrable exhaustion `cd8ab97c`, regular exhaustion `bf433f0a`, or
their conclusions. The closure contains no classification, segment, Jacquet
module, induction, `K0` or Aubert-duality module.

## Verification and provenance

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at the commit above. The
module compiles without errors or warnings. Declaration inspection shows that
`Langlands.admissibleShortExact` has universe parameters `uG uU uV uW` and
depends only on `propext`, `Classical.choice` and `Quot.sound`. The file
contains no `sorry`, `admit`, axiom or other placeholder. These are
development checks; acceptance requires the registered proof checks and
independent semantic review.

Worker 261 wrote the Lean proof and this explanation from scratch. No draft or
code from another worker was reused; the published Library results above are
imported, not copied.
