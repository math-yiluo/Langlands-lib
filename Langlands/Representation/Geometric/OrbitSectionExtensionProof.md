# Compact section extension by finite clopen gluing

The theorem `Langlands.Geometric.closedOrbitSectionExtension` proves exactly
`Langlands.Geometric.ClosedOrbitSectionExtension.{uG,uV}`, as defined in
`OrbitSectionExtensionStatement`. The group and representation carrier
universes remain independent.

## Statement and scope

Let `G` be a nonarchimedean locally compact Hausdorff sigma-compact group,
`P,Q` closed subgroups, and `w : G`. Write `Z = cosetOrbit P Q w` for the
actual orbit of `P w⁻¹` in the left-coset quotient `P \ G`. Let `U` be an
open subset of that quotient containing `Z`, with `Z` closed in the
subspace `U`.

For every smooth complex representation `A` of `P` and every
`g : CompactFunctions (orbitStabilizer P Q w)
(A.obj.ρ.comp (stabilizerToInducing P Q w))`, the theorem produces
`f : CompactFunctions P A.obj.ρ` such that

- every nonzero value `f(x)` has `quotientMap P x ∈ U`;
- `f(w⁻¹ * q) = g(q)` for every `q : Q`.

Here `orbitStabilizer P Q w` is the subgroup of `Q` corresponding to
`Q ∩ wPw⁻¹`, and `stabilizerToInducing` sends its elements to `P` by
conjugation by `w⁻¹`. All evaluations use the existing `Induction.eval`.
The output is an element of the existing `CompactFunctions` type, so it
has the required covariance, one uniform open right stabilizer, and
compact projected nonzero support. The support condition concerns the
image of the actual nonzero locus under the quotient map.

The set `U` need not be invariant under `Q`. There are no
finite-dimensionality, admissibility, or finite-length assumptions on
`A`. The theorem supplies existence of an extension; it does not assert
a canonical or natural choice of extensions.

## Implemented proof

The proof uses local covariant sections, compact clopen subsets of the
ambient quotient, and a finite gluing argument.

First, `locallyClosed_of_closed_in_open` proves that a subset closed
relative to an open set containing it is locally closed in the ambient
space. It writes the relatively closed subset as the intersection of
that open set with an ambient closed set, using the subtype topology.
The final theorem applies this to `Z` and imports the proved
`cosetOrbitHomeomorph P Q w hP hQ hw`. This identifies
`(orbitStabilizer P Q w) \ Q` with the actual orbit subspace. Its
representative formula sends the class of `q` to the point represented
by `w⁻¹ * q`.

The private helper `exists_open_orbit_agreement` starts with an ambient
smooth covariant function whose value at `w⁻¹ * q` equals the given
orbit section at `q`. It forms the difference
`smoothOrbitRestriction P Q w σ f - g`. The published
`Induction.isClosed_quotientSupport` says that its projected nonzero
support is closed. Its complement is therefore open in the stabilizer
quotient. Transport through the orbit homeomorphism gives an open
subset of the orbit. The published
`Induction.quotientMap_preimage_quotientSupport` identifies membership
in this complement with equality of the two section values. Finally,
the subtype topology realizes this open subset as the intersection of
the orbit with an ambient open set `W`. Thus equality persists at
every orbit point lying in `W`.

The helper `finite_orbit_gluing` glues a finite family of compact
ambient sections, each agreeing with `g` on the orbit points inside
its assigned compact clopen set `Cᵢ ⊆ U`. It uses a cutoff operation
whose evaluation is the input value on `Cᵢ` and zero elsewhere.
Starting from the zero compact section, insertion of one patch updates
the section by

```text
f' = cutoff(Cᵢ, patchᵢ) + (f - cutoff(Cᵢ, f)).
```

The cutoff evaluation law makes `f'` equal to `patchᵢ` on `Cᵢ` and
equal to `f` off `Cᵢ`. Finite induction proves that its nonzero
support stays inside `U`, and that its orbit restriction equals `g`
on the union of the selected sets and zero on the rest of the orbit.
Overlaps cause no ambiguity because each patch has the same prescribed
orbit value there. All operations are on actual `CompactFunctions`;
compactness and uniform smoothness are preserved by their existing
additive structure.

The helper `extension_of_local_sections` combines these steps. For
each `q : Q`, it takes a compact ambient section with the prescribed
point value, obtains an agreement neighborhood `W`, and chooses a
compact clopen set containing the orbit point and lying inside
`W ∩ U`. The image of the projected support of `g` under the orbit
homeomorphism followed by subtype inclusion is compact in `P \ G`.
The chosen clopen sets cover it, so compactness yields a finite
subcover. Applying `finite_orbit_gluing` to this finite family gives
the required section. Every nonzero value of `g` has its orbit point
in this cover; outside the cover `g` is zero. This proves equality
on the entire orbit, as well as the ambient support condition.

Finally, `closedOrbitSectionExtension` supplies all inputs to that
assembly from proved constructions:

- `Induction.compactLocalSection` and
  `Induction.compactLocalSection_apply` give the point-value patch at
  `x = w⁻¹ * q` with value `Induction.eval _ _ g.val q`. The smoothness
  argument is `A.property`; the local constructor is called with the
  quotient neighborhood `Set.univ`.
- `Induction.exists_compactClopen_quotientNeighborhood P hP` gives
  the compact clopen set inside `W ∩ U`.
- `Induction.compactQuotientCutoff` and
  `Induction.eval_compactQuotientCutoff` give the actual cutoff and
  its conditional evaluation formula.

Thus the public theorem assumes no local section, cutoff, orbit
homeomorphism, surjectivity, or extension operator. These intermediate
inputs occur only in private assembly helpers and are instantiated
by proved constructions in the final theorem.

## Provenance

This is an internal direct-section proof of the published proposition.
It derives the result from the induction function carriers, smooth
orbit restriction, the canonical coset-orbit homeomorphism, and the
local-section and quotient-cutoff constructions identified above,
together with elementary topology and finite induction.

The motivating source is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), sections
5.3–5.15, printed pages 461–465 / PDF pages 22–26, read in full.
Section 5.11 gives exactness for compactly supported sheaf restriction;
sections 5.14–5.15 describe the orbit/stabilizer comparison, with
case III of 5.15 relevant to the Mackey application. The proof here
implements finite covariant patching. It does not formalize the
source's sheaf comparison or prove the full Mackey filtration theorem.
The open subset `U` here is a subset of `P \ G`, not the source's
localization subgroup.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Retained original SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Author: Worker 182.
