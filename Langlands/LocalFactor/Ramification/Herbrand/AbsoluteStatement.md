# Absolute upper ramification arithmetic and continuity statements

Worker 98 authors this statement unit. All eight declarations are Prop-valued
definitions in `Langlands.Ramification.Padic`. They specify targets for later
proofs over the published concrete absolute filtration. No arithmetic
conclusion is used as an assumption in constructing a group or map.

## Objects and quantifiers

Fix an arbitrary prime `p` with `[Fact p.Prime]` and
`F : PadicField.{u} p`. This is any finite extension of the actual p-adic
field. Write `G` for `Field.absoluteGaloisGroup F.Carrier`,
`G^v` for `absoluteUpperRamificationGroup F v`, and `r_L` for
`absoluteFiniteRestriction F L`. Every finite index `L` ranges over all
`FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)`.
The target of `r_L` is the actual `Gal(L/F.Carrier)`. Its Krull topology
is discrete, whereas `G` carries its existing profinite Krull topology.
There is no caller-supplied family of groups, fields or homomorphisms.

The finite group denoted `G_L^v` below is exactly
`canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v`.
It uses the canonical topological realization and integer ring on the
actual subtype field `L`. The universe `u` is arbitrary. The chosen
`AlgebraicClosure F.Carrier` and its intermediate fields have that same
universe by the underlying API; no independently presented extension
carrier is introduced or artificially identified with `F`. The imported
general helper `finiteGaloisPadicField` retains its independent ambient
universe unchanged.

All real indices remain real. The finite-image and right-image clauses
quantify over `v ≥ -1`. Left continuity uses `v > -1`, intersecting only
over `-1 ≤ w < v`. The endpoint `v = -1` is a separate full-group clause.

## Exact declaration, source and dependency correspondence

Page numbers in this table are Serre's printed pages; their PDF page numbers
are seven larger. These are all declarations in the paired Lean file.

| Declaration | Exact assertion | Original source or derived provenance | Principal existing dependencies |
| --- | --- | --- | --- |
| `AbsoluteUpperFiniteImage F` | For every `L` and real `v ≥ -1`, `(G^v).map r_L = G_L^v`. | IV.3 Proposition 14, pp.74–75, and Remark 1, p.75; derived finite projection surjectivity for the inverse system. | `absoluteUpperRamificationGroup`, `absoluteFiniteRestriction`, `canonicalUpperRamificationGroup`, `Subgroup.map`. |
| `AbsoluteUpperInertia F T` | `G^0 = F.absoluteInertia T` for the given arbitrary legitimate `T`. | IV.1 Proposition 1, p.62; IV.3 upper definition, p.74, and infinite construction, p.75; derived comparison of the actual realizations. | Existing `PadicField.absoluteInertia` and spectral closure integers in `Galois.Local.AbsoluteDefinitions`; canonical finite integer rings. |
| `AbsoluteUpperCanonicalInertia F` | `G^0 = F.absoluteInertia F.canonicalTopologicalData`. | Explicit specialization of the preceding comparison. | `PadicField.canonicalTopologicalData`, available for every `F`. |
| `AbsoluteUpperEndpoint F` | `G^(-1) = ⊤`. | IV.3, p.74, and the infinite construction, p.75. | Already supplied by `absoluteUpperRamificationGroup_neg_one`; this clause merely records the boundary. |
| `AbsoluteUpperLeftContinuity F` | For real `v > -1`, `G^v = ⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v), G^w`. | IV.3 Remark 1, p.75, with the explicitly restricted domain convention. | The published real upper filtration and subgroup infimum. |
| `AbsoluteUpperClosedRightImage F` | For every `L` and real `v ≥ -1`, `r_L(R_F(v)) = ⨆ (w : ℝ) (_ : v < w), G_L^w`, with `R_F(v)` as defined in prose below. | Derived from finite-image equality, continuous restriction to a finite discrete group, and subgroup image/supremum laws. It is not a verbatim source assertion. | `Subgroup.topologicalClosure`, the actual Krull topology, `absoluteFiniteRestriction`, canonical finite upper groups. |
| `AbsoluteUpperWildInertia F` | `R_F(0) = ⨅ L, (lowerRamificationGroup (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier 1).comap r_L`. | Derived from IV.2 Proposition 7 and Corollaries 1,3, pp.67–68; IV.3 real/upper conventions, pp.73–74; and the closed-right image comparison plus profinite separation. | Actual finite first lower groups, `Subgroup.comap`, closed right supremum, all finite Galois restrictions. |
| `AbsoluteHerbrandArithmetic.{u}` | For every prime `p` and every `F : PadicField.{u} p`, the conjunction of all seven clauses, universally quantifying `T` in `AbsoluteUpperInertia`. | Internal organization of precisely the preceding statement families. | The seven proposition definitions in this file. |

Here `r_L` in subgroup map/comap notation means
`(absoluteFiniteRestriction F L).toMonoidHom`. Both image clauses assert
equality, strengthening the construction's elementary image containment.
Exact finite projection surjectivity uses the finite quotient theorem and
compactness of the inverse system of finite ramification groups. It does
not follow merely by taking images of an arbitrary intersection.

## Inertia comparison and all-field realization

`T : F.TopologicalData` is arbitrary, with its legitimate p-adic valuation
extension, canonical module topology and local-field structure. The existing
`F.absoluteInertia T` comes from the action on the residue field of the
spectral valuation ring in the algebraic closure. This file imports
`Langlands.Galois.Local.AbsoluteDefinitions` directly and reuses that subgroup.
It does not define inertia to be `G^0`.

The absolute filtration is constructed instead from canonical finite
integer-ring groups. Relating those finite rings and residue actions to
the spectral closure integers is a substantive arithmetic and realization
comparison. The asserted equality must account for this comparison for
every `T`; no definitional equality of the integer-ring implementations is
claimed. `AbsoluteUpperCanonicalInertia` exposes the specialization to the
already constructed `F.canonicalTopologicalData`. Consequently the family
applies to every finite p-adic field, without an extra existence premise.

## Left boundary and jump convention

The imported finite real lower group is `G_ceil(u)`, and the upper group is
`G_psi(v)`, for the constructed inverse Herbrand function `psi`. This is
Serre's convention on p.73: at a break the group retains the value from
the left. The absolute left-continuity formula uses a genuine subgroup
infimum over the restricted interval `[-1,v)`. The proof variable in
`⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v)` excludes every other real index.

At `v = -1` that interval is empty. Instead of inferring a boundary value
from that empty intersection, the aggregate separately includes the
already established full-group endpoint. The imported construction also
proves that `G^w = ⊤` for `w ≤ -1`; thus the restricted formula agrees
with Serre's unrestricted intersection over `w < v` using that extension.
This unit chooses the restricted formulation and does not add an assumption
at the endpoint.

## Closed right limits and wild inertia

For prose only, set

`R_F(v) = (⨆ (w : ℝ) (_ : v < w), G^w).topologicalClosure`.

The Lean file writes this expression directly in both relevant clauses.
The supremum is in the subgroup lattice, and its closure is taken in the
actual absolute Galois group. Since the filtration is decreasing, the
family with `w > v` is directed under subgroup inclusion; its supremum
agrees with its union as a set. The closure is still essential in the
absolute setting. It is neither dropped nor replaced by `G^v`.

For a continuous homomorphism to a finite discrete group, the image of a
subgroup's closure equals its image: continuity gives containment in the
closure of the image, which is already closed, and the opposite containment
follows from inclusion in the closure. Subgroup image preserves suprema.
Together with exact finite-image equality, this explains the derived
right-image formula. It requires no single interval of stabilization
simultaneously valid for every finite quotient.

At zero, each finite extension has a positive interval on which
`0 < psi(w) ≤ 1`. On that interval the ceiling lower index is exactly `1`,
so the finite positive upper supremum is the first **lower** ramification
group `G_1`. For larger positive parameters monotonicity keeps the group
inside `G_1`. The endpoint of this interval may depend on the extension.
In general `G^1 = G_psi(1)` need not equal `G_1`.

Serre IV.2 identifies `G_1` as a p-group, with prime-to-p quotient `G_0/G_1`.
This is why its intersection of finite restriction preimages describes
absolute wild inertia. Closed subgroups of the profinite absolute Galois
group are determined by their images in all its finite Galois quotients.
Applying that fact to the closed positive upper limit and the right-image
formula yields the stated wild comparison. The equality is an explicit
proposition to prove; its two sides are not made equal by a naming convention.
No separate actual absolute wild-inertia object was present in the imported
Galois or ramification interfaces. No uniform absolute stabilization or
absolute eventual triviality is asserted.

## Source reading and declaration checks

The original source is Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, GTM 67, Springer (1979), registered as
`serre-1979-local-fields`. The retained file is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The chapter hypotheses on printed p.61 and the cited passages on
pp.62,67–68,73–75 were read as text. The cited pages were also inspected as
page images, in particular the ceiling convention, upper/lower subscripts,
quotient formula, and infinite left-continuity intersection. No
source-specific errata note was present in the Library notes.
The finite p-adic fields here satisfy the source's complete discrete
valuation and separable residue extension setting.

The complete unapplied types were inspected with universe printing.
Each component has outer parameters `{p}`, `[Fact p.Prime]`, and
`F : PadicField.{u} p`; only `AbsoluteUpperInertia` additionally takes
`T : F.TopologicalData`. All return `Prop`. The aggregate itself has
type `Prop` with universe parameter `u`; its prime, primality, field and
realization quantifiers are inside the proposition. The finite-field and
real-index quantifiers are inside their respective component definitions.
The aggregate's printed body was also inspected to verify this scope.
Exact Lean-service inspection of `AbsoluteHerbrandArithmetic` succeeded
with `statement_returns_prop = true`, with no compilation errors or warnings.

This module does not prove the arithmetic families. It does not use
reciprocity, class-field existence, Hasse–Arf, conductor transport, or
the aggregate as a construction hypothesis. The finite arithmetic
statement module and existing residue exactness proofs are unchanged.
An abelianized comparison with finite abelian quotients is outside this
unit.
