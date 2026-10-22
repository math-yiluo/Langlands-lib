# Admissibility descends along an injective intertwiner

`Langlands.admissibleSubrepresentation` proves the entire accepted proposition
`Langlands.AdmissibleSubrepresentationStatement`. The coefficient ring `R`,
group `G`, source module `V`, and target module `W` occupy four independent
universes. The ambient assumptions are a commutative ring, a group with a
topology, and the two module structures. The Noetherian coefficient instance
is universally quantified **inside the proposition**. The closing proof
introduces this instance before applying `isAdmissible_of_injective`; it
does not add a Noetherian assumption outside the accepted target.

For representations `rho` and `sigma` and an injective intertwiner
`f : rho.IntertwiningMap sigma`, admissibility of `sigma` implies
admissibility of `rho`. Here admissibility includes smoothness and finite
generation of fixed vectors for **every open subgroup**. The modules need
no topology, and the group operations need no continuity assumption.
Local compactness, countability, characteristic zero, and finite generation
of the entire representation space are not required.

## Implemented proof

The helper `isAdmissible_of_injective` proves the two conjuncts directly.

1. Given a source vector `v`, smoothness of `sigma` supplies an open
   subgroup `K` fixing `f(v)`. For each `k` in `K`, equivariance identifies
   `f(rho(k)v)` with `sigma(k)(f(v)) = f(v)`. Injectivity gives
   `rho(k)v = v`, so the same open subgroup fixes `v`.
2. For each open subgroup `K`, the accepted construction `fixedVectorsMap`
   restricts `f` to an `R`-linear map between the two fixed-vector modules.
   Equality of its output subtypes gives equality of the underlying
   `f`-images. Injectivity of `f` and subtype extensionality prove
   injectivity of the restriction. Admissibility supplies the local
   `Module.Finite` instance for the target fixed-vector module.
   Mathlib's `isNoetherian_of_isNoetherianRing_of_finite` then supplies its
   `IsNoetherian` instance by typeclass inference.
   `Module.Finite.of_injective` yields finite generation of the source
   fixed-vector module.

Smoothness reflection and injectivity of restriction
are proved within this contribution. The closing theorem introduces all
binders of the accepted proposition and applies the helper. The proof uses
no averaging, fixed-vector surjectivity, or pending project proof.

The precise algebraic interfaces are in
`Mathlib/RingTheory/Noetherian/Basic.lean`, lines 136-139
(`Module.Finite.of_injective`) and 324-328
(`isNoetherian_of_isNoetherianRing_of_finite`), at Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The former descends finite
generation from a Noetherian target module along an injective linear map;
the latter is where the Noetherian ring hypothesis is used.

## Provenance

Worker 0 supplied the proof and its initial explanation in task draft
revision 1, content key
`e1e2739fb1fa50a2c51dca0c058dc1d9ff3f70db57c47d499e6cb838ce405562`.
Worker 19 checked the implementation, source correspondence, exact
dependencies, and whole-target universe coverage, and expanded this
explanation. Both workers are authors of this contribution.

The accepted target derives from the subrepresentation direction of
Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, revision June 16, 2019, page 4, Proposition II.1.3 and
Corollary II.1.4. Page 2 defines admissibility using all open subgroups.
Worker 19 read pages 1-4 of the retained original and verified its
fingerprint:

- `literature_id`: `casselman-2019-smooth-representations`
- `content_sha256`: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`
- File: `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The chapter assumes a locally profinite group with countability conditions
and a Noetherian coefficient ring containing the rationals. The implemented
argument proves the stated subrepresentation direction with the weaker
hypotheses above. It asserts no quotient or extension theorem.

## Exact dependencies and verification boundary

All three project dependencies are version 1, independently accepted and
published, and their local Lean/Markdown hashes match the effective records.
They are available in the checked Library snapshot
`93def8b48b4703317be20fe31714dddf482835a9`.

| Role | Artifact | Publication commit | Independent review receipt |
| --- | --- | --- | --- |
| Accepted target | `e95c3f58-3ed4-4ddc-b666-462d05ec8cca` | `18e8beb7aa4724a681a9ef2637f8fc000aefb408` | `db16a9fe-6c6b-4c5a-b3a1-01a0db151f3d` |
| Fixed-vector maps | `7ad85b8b-caae-4345-ac1b-2c2d551dbb94` | `18d2c44b3fecb756a7634ce0f766fdc16b539b45` | `7f5084d1-9e75-445b-b031-b754e38c4830` |
| Smoothness and admissibility definitions | `665022df-625b-44ae-9dbd-425f6e266bab` | `10c81beaaff024987cf2945c64d0c9511f6cb686` | `a26076cd-7da3-4621-992f-5c0207f7fe1e` |

The target fingerprint is
`cd3273b78678f48780548001e916382b7f7e356869a1c8beb71a37d50027d65e`.
The direct imports are the accepted target, the fixed-vector definitions,
and Mathlib's Noetherian module theory. The smoothness and admissibility
definitions enter through those two project imports.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1;
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib at the commit above.

Native compilation, assignment to the complete accepted target with four
independent universe parameters, and declaration/axiom inspection are
development checks. These checks succeeded with the pinned compiler; both
proof declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Acceptance requires the registered independent proof
checker and independent semantic review; publication is a separate recorded
step. The Lean file contains the proof, with no placeholders or project axioms.
