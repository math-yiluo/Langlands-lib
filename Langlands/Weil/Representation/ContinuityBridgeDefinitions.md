# Bundled continuity presentation

This pair supplies a presentation of the existing
`Langlands.Weil.RepresentationContinuity` proposition using the published
`Langlands.FiniteRepresentation` category and predicates. It does not prove any
of the five substantive continuity equivalences.

The group and carrier have independent universes `uG` and `uV`. The scalar field
is the usual normed complex field throughout. A carrier of dimension zero is
allowed.

`carrierNormedAddCommGroup A` pulls the supremum norm on
`Fin (Module.finrank ℂ A) → ℂ` back along the linear equivalence supplied by
`Module.finBasis ℂ A`. `carrierNormedSpace A` supplies its compatibility with the
original complex module structure. The additive and module structures and the
representation are retained. These are explicit local constructions, not global
instances. In dimension zero the coordinate index is empty and the carrier is
the zero vector space. The comparison statement separately requires that this
norm's topology agrees with the canonical module topology.

`HasContinuousOrbits` and `HasContinuousAction` use `moduleTopology ℂ A` on the
carrier. The latter uses the product topology on `G × A`. They introduce no
choice of basis or norm.

The interface map is:

| Existing unbundled expression for `ρ` | Bundled expression for `of ρ` |
| --- | --- |
| `Continuous (fun g => (ρ g).toContinuousLinearMap)` | `IsContinuous` |
| `∀ v, Continuous (fun g => ρ g v)` | `HasContinuousOrbits` |
| `Continuous (fun x : G × V => ρ x.1 x.2)` | `HasContinuousAction` |
| `(ρ.comp I.subtype).ker` | `inertiaKernel I` |
| Openness of this kernel in `I` | `HasOpenInertiaKernel I` |
| Finiteness of `Set.range (fun i : I => ρ (i : G))` | `HasFiniteInertiaImage I` |
| Openness of `ρ.ker` in `G` | Openness of `A.representation.ker` |

These are proposed comparisons, not identifications asserted by this definition
pair. The separate comparison statement specifies and the separate proof must
establish them.

`ContinuityClauses A I` records, in the original order, continuity versus orbit
continuity, joint continuity, open inertia kernel, and open full kernel, followed
by the equivalence of open inertia kernel with finite inertia image **and closed
inertia kernel**. `OperatorContinuityClauses I ρ` is the original unbundled
expression for one representation, copied without changing its logical content.

`BundledRepresentationContinuity` quantifies the bundled expression over every
topological group and every open, compact, nonarchimedean subgroup, followed by
every finite-dimensional bundled complex representation. Normality of the
subgroup is not added. The original `Continuity.lean` and `Continuity.md` are
unchanged. This is a generic presentation bridge, with no assertion about an
actual local Weil group or a parameter classification.

This is internal, derived interface work. Its mathematical provenance is the
published `Basic`, `Predicates` and `Continuity` pairs in this directory, and
Mathlib's `Module.finBasis`, `NormedAddCommGroup.induced` and
`NormedSpace.induced`. The original literature references and their scope remain
those documented in the unchanged `Continuity.md`; this pair introduces no new
literature claim. The implementation uses Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.

Author: Worker 38.
