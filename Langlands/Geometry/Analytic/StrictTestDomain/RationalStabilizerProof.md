# Open setwise stabilizers of actual rational loci

Authors: Worker 552 (Lean proof and explanation); Worker 36 (task-supplied proof route).

`rationalLocusStabilizerOpen` proves the exact published proposition
`RationalLocusStabilizerOpenStatement.{u,v}`. For an ultrametric normed field
`K`, an actual presented strict affinoid algebra `P`, a topological group `G`,
and a homomorphism `ρ : G →* Aut P` with norm-continuous forward
algebra-element orbits, every actual unit-radius rational locus has an open
setwise stabilizer. The field and group remain in independent universes.
The target and its imported dependencies are unchanged.

The reusable theorem `isOpen_rationalLocusStabilizer` gives this conclusion
for specified data. The preceding lemmas expose the compact denominator bound
and a perturbation criterion for individual bounded maps and automorphisms.
They use only the hypotheses present in the target, allowing an incomplete
coefficient field, a trivial valuation, a zero algebra, and empty spectra,
loci, or numerator tuples. There is no uniform operator-bound assumption or
topology on the automorphism group.

The proof is the following internally derived argument, implementing the
route supplied by Worker 36 in the task context.

1. `exists_pos_le_denominator` proves that some positive real `ε` satisfies
   `ε ≤ x(d.denominator)` for every `x ∈ d.locus`. Each rational inequality
   is closed because both evaluations are continuous, so the locus is a
   closed subset of the compact actual spectrum. At a locus point, a zero
   denominator would force every numerator to have zero seminorm, contradicting
   `d.no_common_zero`. The continuous denominator evaluation is therefore
   positive on the locus. Mathlib's `IsCompact.exists_forall_le'` supplies
   the uniform positive lower bound, also when the compact set is empty.

2. `comap_mem_locus_of_displacement_lt` treats any actual bounded algebra
   endomorphism `φ`. Suppose the norm displacements of the denominator and
   every numerator are strictly smaller than the lower bound `ε`. At a
   locus point `x`, the normalized spectrum bound gives
   `x(φ(b) - b) ≤ ‖φ(b) - b‖ < ε ≤ x(b)`. The published strong triangle
   inequality, through `IsNonarchimedean.add_eq_right_of_lt`, then gives
   `x(φ(b)) = x(b)`. For each numerator the same triangle inequality gives
   `x(φ(f_j)) ≤ max(x(φ(f_j) - f_j), x(f_j)) ≤ x(b)`.
   Thus the actual spectrum pullback along `φ` lies in the original locus.

3. `locus_image_eq_of_displacement_lt` is the reusable stabilization
   criterion. It assumes these finite displacement bounds for both the
   forward and inverse algebra maps of an automorphism `g`. The existing
   spectrum action uses inverse pullback:
   `((g • x) a) = x(g.inv(a))`. Applying the bounded-map criterion to
   `g.inv` gives the inclusion of the image of the locus into the locus.
   Applying it to `g.hom` gives `g⁻¹ • x ∈ d.locus` for every locus point
   `x`; the group action identity `g • (g⁻¹ • x) = x` gives the reverse
   inclusion. The result is equality of the actual subsets.

4. `isOpen_rationalLocusStabilizer` chooses the lower bound and makes all
   these finitely many displacement inequalities hold near the identity
   in `G`. Continuity of the forward orbits is assumed, and the published
   `continuous_inv_apply` derives continuity of the inverse orbits from it
   by composition with group inversion. At the identity every displacement
   is zero. `Filter.eventually_all` combines the numerator estimates,
   including an empty tuple. The stabilization criterion shows that the
   preimage under `ρ` of the existing subgroup `locusStabilizer d` is a
   neighborhood of the identity. `Subgroup.isOpen_of_mem_nhds` makes this
   subgroup open. The final theorem closes the published target directly.

The source of the rational inequalities and no-common-zero data is
Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
printed/PDF p. 9, Exercise 2.2.2(ii), here specialized to unit radii.
The actual bounded spectrum and evaluation topology follow Definitions
1.2.3 and 1.2.5 on printed/PDF p. 4; Exercise 1.2.4 explains the normalized
bound, and Fact 1.2.6 provides the compactness context. The registered source
is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These pages were read for this proof. The source discusses Banach rings and
complete coefficient fields; the proof here uses the already published
compactness and nonarchimedean theorems for the Library's actual normed
algebras, without adding completeness to the target.

The motivation is Berkovich's unfinished *Etale equivariant sheaves on
p-adic analytic spaces* (1995–1996), section 1.1, printed/PDF pp. 1–2.
Those pages define analytic automorphism neighborhoods using finite compact
domain-preservation conditions together with spectral bounds on functions.
The registered folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`;
the member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
These pages were also read. The perturbation criterion and proof above are
internal derived reasoning, not a claimed theorem from that manuscript.
Their conclusion supplies the rational-locus setwise stabilizer condition
under the explicit algebra-orbit hypothesis. It establishes no comparison
with the full analytic automorphism topology, transported local-section
continuity, analytic G-space construction, or etale site.
