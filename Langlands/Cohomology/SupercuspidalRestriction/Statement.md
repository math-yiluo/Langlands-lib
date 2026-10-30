# Restriction of supercuspidal representations to a subgroup with compact center

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

The published `SupercuspidalExt.CompactInductionSupercuspidalExtVanishingStatement`
concludes `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0`. Its hypothesis is that the
restriction of `π` to the open subgroup `G₀` is a finite direct sum of
irreducible representations with compactly supported matrix coefficients.
Harris (1997, p.96) obtains this hypothesis by restricting a supercuspidal
representation to an open subgroup `GJ^0` with compact center. This module
states when the hypothesis holds:

- in general, for an open normal subgroup `H` with `H ∩ Z(G)` compact and
  `Z(G) H` of finite index, and an irreducible representation whose matrix
  coefficients are compactly supported modulo the center;
- for `GL_n(F)`, a `p`-adic field `F`, and the subgroup `G°` of matrices whose
  determinant is a unit. This part includes the needed direction of
  Harish-Chandra's theorem.

It defines one subgroup and five propositions, including a conjunction. It
proves two facts about the subgroup and one implication between the
propositions. None of the propositions is proved here.

## Objects

- `G` is a group in `Type` with a topology making it a Hausdorff, locally
  compact, totally disconnected, σ-compact topological group. These are
  Bernstein–Zelevinsky's `l`-groups countable at infinity.
- `SmoothRep.{0, 0, 0} ℂ G` is the Library's category of smooth complex
  representations. `π.IsIrreducible` is the Library's irreducibility over a
  field.
- `HasCompactSmoothCoefficientsModCenter ρ` is the Library's predicate from
  `Langlands.Representation.Classification.FixedCentralSplittingStatement`.
  For every smooth dual vector `ℓ` and vector `v`, the support of
  `g ↦ ℓ(ρ(g) v)` lies in the preimage of a compact subset of
  `G / Z(G)`.
- `SupercuspidalExt.HasCompactCoefficients σ` is the published predicate: all
  matrix coefficients of `σ` against smooth dual vectors have compact support.
  `SupercuspidalExt.restriction ℂ G H` is the published restriction functor.
- For a `p`-adic field `F : PadicField.{0} p`, `F.Carrier` carries the
  canonical topology `F.canonicalTopologicalData.topology`. `GL_n(F)` is the
  Library's `GeneralLinear n F.Carrier` with `F.canonicalGeneralLinearTopology n`
  and `F.canonicalGeneralLinearTopologicalGroup n`. The module installs these
  as local instances, as `Langlands.Correspondence.AutomorphicRelations` does.
- `unitDeterminantSubgroup F n` is `G° = {g ∈ GL_n(F) | det g ∈ O_F^×}`. It is
  defined as the kernel of `g ↦ ‖det g‖`, for the canonical norm
  `F.canonicalNorm`: Mathlib's spectral norm, which is the unique extension of
  the `p`-adic norm to `F`. The ring of integers is `{‖x‖ ≤ 1}`, so its units
  are the elements of norm one. `mem_unitDeterminantSubgroup` states this
  description and is proved by `Iff.rfl`.
- `GeneralLinear.IsSupercuspidal` is the Library's supercuspidality of Worker
  23: admissibility, and vanishing of the Jacquet coinvariants for every
  proper block parabolic and every conjugate of its unipotent radical.

## The propositions

| Lean | Meaning |
| --- | --- |
| `CompactModCenterRestrictionStatement G` | For every open normal subgroup `H` with `H ⊓ Z(G)` compact and `Z(G) ⊔ H` of finite index, and every irreducible `π` with `HasCompactSmoothCoefficientsModCenter`, there are `m` and irreducible `σ : Fin m → SmoothRep ℂ H` with compactly supported coefficients such that `restriction π ≅ ⨁ σ`. |
| `UnitDeterminantSubgroupStatement F n` | `G°` is open in `GL_n(F)`, `G° ∩ Z` is compact, and `Z G°` has finite index. |
| `GLHarishChandraStatement F n` | Every smooth complex representation of `GL_n(F)` that is supercuspidal in the Library's sense satisfies `HasCompactSmoothCoefficientsModCenter`. |
| `GLSupercuspidalRestrictionStatement F n` | The restriction to `G°` of an irreducible supercuspidal representation of `GL_n(F)` is isomorphic to `⨁ σ` for finitely many irreducible smooth representations `σ i` of `G°` with compactly supported matrix coefficients. |
| `GLSupercuspidalRestrictionStatements F n` | The conjunction of the three `GL_n` propositions. |

`unitDeterminantSubgroup_normal` proves that `G°` is normal, as the kernel of
a homomorphism. The module installs the Library's Hausdorff and local
compactness certificates for the canonical topology of `GL_n(F)`
(`F.canonicalGeneralLinearT2Space`, `F.canonicalGeneralLinearLocallyCompactSpace`)
as local instances, alongside the topology and the topological group
structure.

## How the pieces fit

The theorem `glSupercuspidalRestriction_of_compactModCenter` proves that
`GLSupercuspidalRestrictionStatement F n` follows from
`CompactModCenterRestrictionStatement` at `G = GL_n(F)`, from
`UnitDeterminantSubgroupStatement F n` and from `GLHarishChandraStatement F n`.
It applies the general statement at `H = G°`, with
`unitDeterminantSubgroup_normal`. The general statement at `GL_n(F)` needs
`TotallyDisconnectedSpace` and `SigmaCompactSpace` instances for the canonical
topology. Instance search finds neither in the Library (checked in the
private test below), so the theorem takes them as instance arguments. Both
properties are proved in the Library, but not as instances. The public theorem
`PadicField.TopologicalData.generalLinearSigmaCompactSpace` in
`Langlands.Group.GL.CountabilityProof`, applied to `F.canonicalTopologicalData`,
gives σ-compactness for this topology, so a caller can supply that argument
with it. Total disconnectedness is proved only by private theorems named
`generalLinearTotallyDisconnected`, in
`Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` and
`Langlands.Representation.Tensor.FactorMatchingProof`, for the matrix-unit
topology of a supplied `F.TopologicalData`, which is the canonical topology
when that data is `F.canonicalTopologicalData`. Private declarations cannot be
used outside their modules, and a search of the Library's Lean files found no
public theorem stating total disconnectedness of `GL_n(F)`. Because the
theorem has these extra arguments, the `GL_n` restriction statement is also
stated separately.

Together with openness of `G°` and the published complex
`CompactInductionSupercuspidalExtVanishingStatement` at `G = GL_n(F)`, it
gives `Ext^{n+1}_{GL_n(F)}(c-Ind_{G°}^{GL_n(F)} V, π) = 0` for every
irreducible supercuspidal `π`. That application also needs the measure
hypotheses of the vanishing statement. This is the shape of Harris's
argument.

## Why the statements are expected to hold

This argument follows Bernstein–Zelevinsky 1976 (BZ). The general statement
is derived: BZ prove it for `GL_n(F)` and `G°`, and the proof uses only the
listed properties.

1. *Schur's lemma.* `G` is an `l`-group countable at infinity, so every
   endomorphism of the irreducible `π` is a scalar (BZ 2.11). In particular
   the center acts by scalars.
2. *Finite decomposition.* `Z(G) H` is a normal subgroup of finite index,
   because `Z(G)` and `H` are normal. By BZ Lemma 2.9(b), the restriction of
   `π` to `Z(G) H` is a finite direct sum of irreducible representations. The
   center acts by scalars, so their `H`-submodules are their
   `Z(G) H`-submodules, and each summand is irreducible for `H`. This is the
   proof of BZ Lemma 3.26.
3. *Smoothness.* Each summand is an `H`-stable subspace of a smooth
   representation, and `H` is open. Its vectors have open stabilizers in `H`.
4. *Compact coefficients.* Let `σ` be a summand and `q` the projection of
   `π` onto it. A smooth dual vector `ℓ` of `σ` is fixed by an open subgroup
   of `H`, which is open in `G`. So `ℓ ∘ q` is a smooth dual vector of `π`, and
   the coefficients of `σ` are restrictions to `H` of coefficients of `π`.
   Their supports lie in `H ∩ p⁻¹(C)` for a compact `C ⊆ G/Z(G)`, where
   `p : G → G/Z(G)` is the quotient map. The map `H → H Z(G)/Z(G)` is open
   with compact kernel `H ∩ Z(G)`, and `H Z(G)/Z(G)` is an open, hence closed,
   subgroup. So `H ∩ p⁻¹(C)` is compact. This is BZ 3.21, (3) ⇒ (4), where BZ
   remark that the smooth dual does not depend on whether `G` or the open
   subgroup `G°` is used.
5. *The subgroup `G°`* (BZ 3.20). `G°` is open, because the norm of the
   determinant is locally constant on `GL_n(F)`. For `n ≥ 1` its
   intersection with the center, the scalars `a` with `‖a‖ⁿ = 1`, is `O_F^×`
   embedded as scalars, which is compact. The valuation of the determinant
   identifies `GL_n(F)/G°` with `ℤ`, since `det` is onto `F^×` and
   `F^×/O_F^× ≅ ℤ`. The center maps onto `nℤ`, so `Z G°` has index `n`. For
   `n = 0` the group is trivial.
6. *Harish-Chandra's theorem* (BZ 3.21, (1) ⇔ (3)). A quasi-cuspidal
   representation, one whose Jacquet modules for all proper standard
   parabolics vanish (BZ 3.18), has matrix coefficients that are finite
   modulo the center. Here finite modulo `Z` means supported in `Z · K` for a
   compact `K` (BZ 1.20). This is equivalent to the Library's predicate,
   because compact subsets of `G/Z` lift to compact subsets of `G`. The
   Library's supercuspidality includes vanishing for the standard proper
   block parabolics, so it implies quasi-cuspidality. BZ write matrix
   elements as `⟨ξ̃, π(g⁻¹)ξ⟩`; inversion does not affect compactness modulo
   the center.

## Provenance

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
p.96 (PDF p.22): "Let `GJ^0` denote the stabilizer of the connected
component `R_N^1` of `M_N` … Now `GJ^0` has compact center. Hence `π_v`,
viewed as a representation of `GJ^0`, is still supercuspidal (i.e., its
matrix coefficients are compactly supported). Thus, as in [BZ, Theorem
2.44], `π_v|GJ^0` is injective and projective in the category of smooth
representations." The source does not mention the decomposition of
`π_v|GJ^0` into finitely many irreducible representations, which BZ 2.44
requires. `CompactModCenterRestrictionStatement` supplies it. Its hypotheses,
`H` normal and `Z H` of finite index, are not checked for Harris's `GJ^0`
here; that requires the Drinfeld tower and its group action, which are not
in the Library. Harris 1999 p.312 repeats the step: "since `π_v` is
supercuspidal, the higher Ext's vanish".

| Source | Lean |
| --- | --- |
| BZ 3.20, `G° = {g | det g ∈ R^*}`; (a) `G° ∩ Z` compact; (b) `G°` open normal, `G/G°·Z` finite | `unitDeterminantSubgroup`, `unitDeterminantSubgroup_normal`, `UnitDeterminantSubgroupStatement` |
| BZ 3.21 (Harish-Chandra), (1) quasi-cuspidal ⇒ (3) matrix elements finite modulo the centre | `GLHarishChandraStatement` |
| BZ 3.21, (3) ⇒ (4), and 3.26 | `GLSupercuspidalRestrictionStatement` |
| BZ 2.9, 2.11 and the proofs of 3.21 and 3.26, for a general subgroup; Harris 1997 p.96 | `CompactModCenterRestrictionStatement` |

## Scope

- Complex coefficients only, as in the published complex vanishing statement
  and in BZ. Groups are in `Type`, so `F : PadicField.{0} p`.
- Only the direction of Harish-Chandra's theorem used here is stated. The
  converse, and the characterization through `G°`, are not.
- Harris's group `GJ`, its subgroup `GJ^0` and the Drinfeld tower are not
  formalized. The general statement is the form in which they would be used.
- The finite length of `π|_{G°}` is part of the conclusion; the number of
  summands and their conjugacy under `GL_n(F)` are not described.

## Registered sources

- `bernstein-zelevinsky-1976-representations-gln`: Bernstein and
  Zelevinsky, *Representations of the group GL(n,F) where F is a
  non-Archimedean local field*, Russian Math. Surveys 31:3 (1976), 1-68,
  SHA-256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  The printed page equals the PDF page. Used: 1.20 (p.11); 2.9 (p.17); 2.11
  (p.18); 2.39-2.41 (p.26); 3.18 (p.34). These were read in the text layer.
  3.20 and 3.21 with its proof (pp.34-35) and 3.25-3.26 (p.36) were also read
  on the rendered scans.
- `harris-1997-drinfeld-cohomology`: Harris 1997, PDF SHA-256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`; p.96
  (PDF p.22), and the group `GJ` on pp.79-80 (PDF pp.6-7). Read in the text
  layer.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; p.312
  (PDF p.14), read on the rendered scan. Provenance only.

## Formal dependencies and checks

Direct project imports, in Library commit
`c5a40b0f54880b1825ea05214c2b066f68bfc156`:

| Module | Author | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.Cohomology.SupercuspidalExt.Statement` | Worker 3 | `f7e3f1d1ec7bf54178be094a654eee3a7619c4d2347a5462288bf266e4d450fd` |
| `Langlands.Representation.Classification.Supercuspidal` | Worker 23 | `c13ba8ffad11de2c3b2861c4afc385be2663b3e76963d5e89807ba92c753f9f1` |
| `Langlands.Representation.Classification.FixedCentralSplittingStatement` | Worker 19 | `48ace7be0156943408440f4e6f1adcd7af9399169ae86c5810b144b672c2b40a` |
| `Langlands.Group.GL.Padic` | Worker 6 | `803a2561ddc85a54c7846a421d37ed5dc61b8974157b02b72c26bc41d96e1722` |

From them the module uses `restriction` and `HasCompactCoefficients`,
`GeneralLinear.IsSupercuspidal`, `HasCompactSmoothCoefficientsModCenter`, and
`PadicField.canonicalGeneralLinearTopology` with the topological group,
Hausdorff and local compactness certificates. It also uses
`PadicField.canonicalNormedField` and `PadicField.canonicalNorm` from
`Langlands.LocalField.Definitions`, and Mathlib's `normHom`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Check `08d21021-e92a-4803-9623-a57cabc4602c` built this Lean file from a draft directory against
the published imports, with no errors or warnings. Check `cd7e9f34-770f-433f-a9f9-33b5d47eb8e1` built the
same file with Lake from the workspace, against Library `c5a40b0f`, with no
errors or warnings. Both inspected `GLSupercuspidalRestrictionStatements` as a
`Prop`-valued definition, depending only on `propext`, `Classical.choice` and
`Quot.sound`.

Check `0f3f72aa-4849-4471-80b8-f132e7f2c276` compiled a test file against
the same Lean file, with no errors or warnings, and its output was read. It
printed the subgroup and the five propositions with universes, and the types
of the three theorems. All binders listed above are present, and all groups
are in `Type`. The conjunctions and the implication theorem depend only on
the three standard axioms. The test file also proves, by `Iff.rfl`, that
`GLHarishChandraStatement F n` unfolds to the Library's admissibility and
Jacquet-vanishing conditions for the canonical topology. It elaborates the
conjunction at `PadicField.rational p`, that is `ℚ_p`, and checks that the
identity matrix lies in `G°`. Check `d24fbaf0-d664-4e59-ad07-f15d3d436715` is
a private test in which instance search failed to find
`TotallyDisconnectedSpace` and `SigmaCompactSpace` for the canonical topology
of `GL_n(F)`, and `TotallyDisconnectedSpace` for `F`. These checks establish
well-formed statements. They do not prove any of the propositions.

Check `9ee26d36-77e2-4e60-8169-592663d5eb35`, a later private test with no
errors or warnings, elaborated
`F.canonicalTopologicalData.generalLinearSigmaCompactSpace n` as a proof of
`SigmaCompactSpace (GeneralLinear n F.Carrier)` for
`F.canonicalGeneralLinearTopology n`, the topology this module uses.
