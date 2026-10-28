# Vanishing of anti-invariant distributions supported on finitely many orbits

The theorem
`Langlands.HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing`
proves exactly
`FiniteOrbitAntiInvariantVanishingStatement.{uG, uX}`.
The acting group and ambient space retain their independent universes and
all the hypotheses of the published statement. The ambient action may have
infinitely many orbits. The distribution is the full complex algebraic dual
of the actual locally constant, compactly supported test-function space,
with the statement's convention that support in `Z` means annihilating every
test function vanishing on `Z`.

## Induction on the supported orbits

The helpers lie in the namespace `FiniteOrbitVanishingProof`.
The orbit quotient of an invariant subspace injects into the ambient orbit
quotient, by `orbitQuotientInclusion_injective`. A finite union of orbits
therefore has finite image in the ambient quotient and a finite orbit
quotient as a subspace. Apply the published
`Langlands.Topology.FiniteOrbitProof.exists_relOpen_orbit` to the closed
invariant support subtype. Transferring its open set to the ambient space
produces an orbit relatively open in the support. This step requires
finiteness only of the supported orbits.

Removing that orbit leaves a closed invariant set and strictly decreases
the finite cardinality of its image in the ambient orbit quotient, as shown
by `remove_relOpen_orbit`. The lemma `vanishing_of_orbit_removal` performs
strong induction on this cardinality. Empty support makes every test
function vanish on the support, so the distribution is zero. This treatment
also allows an empty finite set of representatives and repeated orbit
representatives.

## Removing one relatively open orbit

Let `Z` be the current closed support and `O` an orbit relatively open in
`Z`. The proof first descends the distribution to `Z`, then restricts it to
the open orbit inside `Z`.

For descent it uses the actual complex linear map
`SchwartzBruhat.restrictClosed hZ`, its evaluation law
`SchwartzBruhat.restrictClosed_apply`, and the published theorem
`SchwartzBruhat.closedRestrictionSurjective`. The supported distribution
kills the kernel of restriction. Mathlib's quotient linear map and
`LinearMap.quotKerEquivOfSurjective` give a distribution `E` on `Z` with
`E (restrictClosed hZ f) = D f`. The helper `exists_descent` proves this
algebraic factorization directly.

A homeomorphism preserving a subset in both directions restricts to a
homeomorphism of that subtype. The lemmas `restriction_pullback` and
`descent_pushforward` express the pointwise commutation of restriction with
pullback and transfer group invariance and anti-invariance to `E`. The
orbit-preserving hypotheses on the original homeomorphism supply exactly
the preservation needed on `Z` and on `O`.

The published `SchwartzBruhat.extendZero` supplies extension by zero from
`O` to `Z`. Its evaluation lemmas give its values on and off `O`. Compose
`E` with this map to obtain a distribution `F` on the orbit. The lemmas
`extension_pullback` and `extension_dual_pushforward` transfer group
invariance and anti-invariance to `F`. The orbit inherits the continuous
transitive action and the required topological properties: `Z` is closed
in the ambient space, and `O` is open in `Z`. The published theorem
`homogeneousAntiInvariantVanishing` consequently gives `F = 0`.

For a test function vanishing on `Z \ O`, its restriction to `Z` vanishes
off `O`. The helper `exists_extension_eq` identifies this restricted
function as the extension by zero of a test function on `O`. To establish
that image description, `exists_restriction_of_support_subset` observes
that the original test function has compact clopen support contained in
the subset. The inducing subtype inclusion pulls this compact set back to
a compact set, and continuous pullback preserves local constancy. Thus its
restriction has compact support. Extensionality and the pointwise extension
laws recover the original test function. This argument needs only a
topological ambient space; the extension map itself is used for the open
subset `O`.

It follows that `D` annihilates every test function vanishing on
`Z \ O`. The induction applies to that smaller closed invariant support.

## Dependencies, scope and provenance

The general helper
`finiteOrbitVanishing_of_homogeneous_and_subspace` derives the target from
the published homogeneous-vanishing and closed-restriction-surjectivity
propositions. The final theorem supplies both published proofs, so it has
no extra premise. All restriction, extension, test-function and distribution
objects are the existing Library constructions.

The proof reuses the finite-orbit topology theorem, the shared subspace
maps, the homogeneous-vanishing theorem and the closed-restriction theorem
by Lean name. The orbit-count induction, algebraic descent and pullback
compatibilities in this module are internal consequences of those results
and Mathlib's invariant-subspace and quotient constructions.

The source motivation is Bernstein and Zelevinsky (1976),
*Representations of the group GL(n,F), where F is a non-Archimedean local
field (survey)*, Theorems 6.9–6.10, printed pages 54–55, registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Those pages were read. As the statement's Markdown explains, this is an
internal finite-orbit variant of their orbit-by-orbit reduction, rather
than a transcription of their constructive-action formulation. The
implemented route descends to the closed support before taking the open
orbit, preserving the published target's full telescope. It adds no
countability condition on the space, transitivity condition on the ambient
action, or equivariance condition on the homeomorphism beyond preservation
of the supported orbits in both directions.
