# Proof that normalized parabolic induction preserves finite character coinvariants

Author: Worker 784.

The closed theorem `Langlands.Whittaker.parabolicInducedCoinvariantFiniteness`
in `Langlands.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof`
has type exactly
`Langlands.Whittaker.ParabolicInducedCoinvariantFinitenessStatement.{uF,uV}`.
The field universe `uF` and the coefficient universe `uV` stay independent.
The theorem adds no parameters or hypotheses. The target pair and everything it
imports are unchanged. All other declarations in the module are private helpers.

Notation follows the statement's Markdown: `G = GL_n(F)`, `P = B.parabolic F`,
`M = B.Levi F`, `U = upperUnipotent n F`, and
`U_M = Subgroup.pi Set.univ (fun i => upperUnipotent (B.size i) F)`.
The proof works for an arbitrary smooth `σ`. Its only assumption on `σ` is the
statement's premise: the `U_M`-character quotient is finite-dimensional for
every locally constant character. It covers all characters `θ` of `U`,
including trivial and degenerate ones, and every positive block shape.

## Reduction to canonical topological data

The private proposition `Body p F τ n B hG χ` is the target's body for three
inputs: a field topology `τ`, a topological-group certificate `hG` for
`GL_n(F)` under `τ`, and a covariance character `χ` of `P`. It covers every
`σ`, with the coefficient premise, every locally constant `θ`, and finite
dimension of the `θ`-quotient of
`Induction.smoothInduced P (twist χ (σ.representation.comp leviProjection))`.

The supplied `T` enters the target only through `T.topology`,
`T.generalLinearTopologicalGroup n` and `T.parabolicHalfModulus B`. The main
theorem first writes `n = m + 1`, using `0 < n`. It then proves
`T.topology = F.canonicalTopologicalData.topology` by composing the two
published equalities `topology_eq_canonicalModule`. The published
`T.parabolicHalfModulus_eq B F.canonicalTopologicalData` identifies the two
half-modulus characters. A local statement `key` quantifies over the topology,
the character and the certificate. Substituting both equalities (`rintro … rfl
rfl hG`) reduces it to the private canonical case `core`. The certificate is a
proposition, so proof irrelevance handles it. Nothing is transported along a
non-definitional equality of instances.

## The finite orbit filtration (BZ76 §7.12(1))

`core` installs the canonical topology, local-field structure, Hausdorff and
locally compact structures, and the sigma-compact structure on `GL_{m+1}(F)`.
The covariance `cov = twist χ (σ.representation.comp leviProjection)` is smooth:
`isSmooth_twist_iff` uses the open kernel of the half-modulus
(`isOpen_ker_parabolicHalfModulus`), and `isSmooth_comp` uses continuity of
`leviProjection`. Local constancy of `θ` makes its kernel open: the kernel is
the fiber over `1` of a locally constant function. So `θ` is bundled as an
`Induction.SmoothCharacter`.

The published `unipotentOrbit` (`Whittaker.UnipotentOrbitProof`) gives a finite
ordered family `s : OrderedDoubleCosets P U m` of `U`-orbits on `P \ G`.
Its representatives are `s.representative i = permutation (e i).val`, where
`e : Fin m ≃ MinimalRepresentatives B (singletons (m+1))`. The initial unions are
open and the orbits cover the quotient. The support filtration
`s.supportFiltration` of the compact induction restricted to `U` becomes an
`ObjectRepFiltration` of length `m` through
`ObjectRepFiltration.ofSubrepresentations`. Its initial step is zero and its
last step is everything.

`Parabolic.parabolicQuotientCompact` makes `P \ G` compact. Then the published
`rawRestrictedCompactSmoothIso` (`Geometric.CompactSmoothComparison`) identifies
the restricted compact induction with the restricted smooth induction. Next,
`Jacquet.Localization.representationEquiv` and `restrictionEquiv`
(`Jacquet.LocalizationTransport`) identify the `⊤`-quotient of that restriction
with the target quotient
`Coinvariants (Induction.smoothInduced P cov) U θ`. So it suffices to prove
finite dimension for the restricted compact induction.

## Graded pieces and compact localization (BZ76 §7.12(3))

Fix `i` and let `r = s.representative i`. The Library's orbit is the `U`-orbit
of the coset of `r⁻¹`. Its stabilizer is
`orbitStabilizer P U r = {q ∈ U | r⁻¹ q r ∈ P}`, and the map to the inducing
group is `stabilizerToInducing P U r : q ↦ r⁻¹ q r`. With `w = r⁻¹` this is the
source's `H_w = U ∩ w⁻¹ P w` and `ρ_w(h) = ρ(w h w⁻¹)`.

The published `closedSubgroupMackeyFiltration` (`Geometric.ClosedSubgroupMackeyProof`)
identifies the `i`-th graded piece with the compact induction from the stabilizer
of `cov ∘ stabilizerToInducing P U r`. This piece is smooth because
`stabilizerToInducing` is continuous. The published `compactLocalization`
(`Whittaker.CompactLocalizationProof`, Worker 672) applies to the closed
stabilizer (`isClosed_orbitStabilizer`). It identifies the `θ`-quotient of the
graded piece with the quotient of `cov ∘ stabilizerToInducing P U r` by the full
stabilizer and the restricted character `θ|_{H}`. These comparisons are composed
through `representationEquiv`. They play the role of the source's 2.23 and the
duality of 2.27–2.30.

## The embedded Levi unipotent group (BZ76 §7.12(4))

`conj_leviEmbedding_mem` shows `r · ι(u) · r⁻¹ ∈ U` for every `u ∈ U_M`, where
`ι = B.leviEmbedding` and `r = permutation w` for a minimal representative `w`.
By `permutation_conjugate_entry`, the `(x, y)` entry of the conjugate is the
entry of `ι(u)` at `(w⁻¹ x, w⁻¹ y)`. Write these indices as `B.index i a` and
`B.index j b`. If `i ≠ j`, the entry vanishes (`leviEmbedding_apply_ne`).
If `i = j` and `y < x`, the minimal-representative condition `w.property.1 i`
says `w` is strictly monotone on block `i`. That gives `b < a`, so the
unitriangular block entry vanishes. The diagonal entries are `1`.

This defines `j : U_M →* orbitStabilizer P U r`, `u ↦ r ι(u) r⁻¹`. It satisfies
`stabilizerToInducing P U r (j u) = leviInParabolic u`, which is the source's
inclusion `w H_w w⁻¹ ⊇ U ∩ G_β` in the Library's `r = w⁻¹` convention.
The map is continuous because `B.leviEmbeddingContinuous` is.

## Trivial half-modulus and the coefficient premise (BZ76 §7.12(5))

`determinant_upperUnipotent` shows that every unitriangular matrix has
determinant one. So each block of `u ∈ U_M` has determinant norm one, and `u`
lies in `normOneLevi`. Then `parabolicHalfModulus_section`,
`leviHalfModulus_eq_one` and `normOneLevi_le_ker_leviModulus` give
`χ(leviInParabolic u) = 1`. With `leviProjection_section`, the stabilizer piece
satisfies `piece (j u) v = σ.representation u v`. The normalized covariance
therefore restricts to `σ.representation` on the embedded `U_M`.

The pulled-back character `η = θ ∘ subtype ∘ j` is locally constant by
`IsLocallyConstant.comp_continuous`. The premise makes
`Coinvariants σ.representation U_M η` finite-dimensional. Every generator
`σ(u)v − η(u)v` of its relations is the stabilizer relation for `j u`. So the
`U_M` relations lie inside the stabilizer relations, and `Submodule.factor`
surjects the finite-dimensional coefficient quotient onto the stabilizer
quotient (`stabilizerCoinvariants_finite`). Hence every graded quotient is
finite-dimensional. This premise replaces the source's argument, which uses
irreducibility and cuspidality of `ρ` to compute these coefficient quotients.

## Finite-dimension propagation (BZ76 §7.12(1), via 2.35)

`finiteDimensional_of_filtration` takes an object filtration whose graded
character quotients are finite-dimensional and concludes the same for the whole
quotient. It uses only right exactness. Write `C_k` for the character quotient of the
`k`-th step, and induct over the steps with `Fin.induction`. Step `0` is the
zero subrepresentation, so `C_0` is a subsingleton.

For the successor step, the published `map_range_eq_ker` and `map_surjective`
(`Jacquet.LocalizationExactnessProof`) apply with trivial auxiliary subgroup `⊥`.
They show that
`C_k → C_{k+1} → (graded k quotient) → 0` is exact. The private
helpers `stepInclusion`, `stepEmbedding` and `adjacent_exact` repeat the
private helpers of the same names in the Library's
`Jacquet.LocalizationFiltrationCollapseProof`, which cannot be imported.
`Submodule.fg_of_fg_map_of_fg_inf_ker` then gives finite generation of `C_{k+1}`.
The last step is the whole representation, and its inclusion is surjective,
so the ambient quotient is a quotient of a finite-dimensional space.

The source obtains `dim E_{U,θ} = Σ dim 𝓕_c(X_i)_{U,θ}` from exactness.
The Lean proof shows only finite dimension, by subadditivity under extensions.
It proves neither the factorial bound nor the dimension-one statement.

## Original source and provenance

This is an internal conditional derivation from I. N. Bernshtein and
A. V. Zelevinskii, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys **31:3** (1976), 1–68.
Registered source: `bernstein-zelevinsky-1976-representations-gln`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Theorem 7.12, proof steps (1)–(5) on printed pp.60–61, was read for this proof.
Printed pages equal one-based PDF pages.

The correspondence is as follows:

- Step (1): the ordered orbit filtration and exactness.
- Step (3): the stabilizer `H_w = U ∩ w⁻¹ P w` with `ρ_w(h) = ρ(w h w⁻¹)`.
- Step (4): the containment `w H_w w⁻¹ ⊇ U ∩ G_β`.
- Step (5): restriction from `H_w` to `U ∩ G_β = ∏ U_{n_i}`.

The implemented route differs from the source in three ways:

- It replaces the cuspidal coefficient argument by the statement's
  arbitrary-character finiteness premise.
- It uses the Library's normalized covariance. Its half-modulus is trivial on
  the unitriangular embedded Levi elements.
- It works directly with character quotients and right exactness instead of
  the dual `Hom` spaces.

The Library's orbit representative `r` corresponds to the source's `w = r⁻¹`.
All Library results are imported by their Lean names. No source proof text is
copied.
