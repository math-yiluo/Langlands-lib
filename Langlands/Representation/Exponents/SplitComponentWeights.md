# Compact-open generalized weight spaces of a central action

Author: Worker 1507. Module `Langlands.Representation.Exponents.SplitComponentWeights`,
namespace `Langlands`.

This file gives the generic algebra behind the characteristic subspaces of
Renard, *Représentations des groupes réductifs p-adiques* (French edition dated
9 July 2026), VII.1.1, printed p. 220 / PDF p. 226. A group `A` acts on a
representation `π` of a group `M` through a homomorphism `ι : A →* M` whose image
is central. The actual split-component and normalized-Jacquet specialization is
in `Langlands.Representation.Exponents.NormalizedJacquetSplitComponent`.

The uniform-power algebra reuses the published `characterSpace` and
`IsGeneralizedEigencharacter` (with `mem_characterSpace` and
`isGeneralizedEigencharacter_iff`) from `Langlands.Representation.Exponents.Jacquet`.
No parallel character-space definition is introduced.

## Setting and universes

`R : Type uR` is a commutative ring. `A : Type uA` and `M : Type uM` are groups.
`V`, `W`, `X` (universes `uV`, `uW`, `uX`) are `R`-modules. `π : Representation R M V`,
`ι : A →* M` and `χ : A →* Rˣ` are arbitrary. All six universes are independent.
Centrality of the image is the explicit hypothesis
`hι : ∀ t : A, ι t ∈ Subgroup.center M` wherever it is used.

## Uniform character spaces

- `characterSpace_mono π χ` (for a monoid `A`): `characterSpace π χ d` increases
  with `d`. Each factor of the infimum is a finite generalized eigenspace, and these
  are monotone in the exponent.
- `map_mem_characterSpace_of_intertwining f hf χ d`: a linear map `f` with `σ a ∘ f = f ∘ π a`
  for all `a` maps `characterSpace π χ d` into `characterSpace σ χ d` with the same `d`.

## Compact-open fixed generalized character spaces

- `fixedCharacterSpace π ι χ K d := fixedVectors π K ⊓ characterSpace (π.comp ι) χ d`
  for any `K : Subgroup M` and `d : ℕ`. `mem_fixedCharacterSpace` gives membership:
  `v ∈ fixedVectors π K ∧ ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0`.
- `fixedGeneralizedCharacterSpace π ι χ K := ⨆ d : ℕ, fixedCharacterSpace π ι χ K d`.
  `mem_fixedGeneralizedCharacterSpace` gives membership:

  `v ∈ fixedVectors π K ∧ ∃ d : ℕ, ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0`.

  The power `d` is chosen before `t`, so one `d` works for every `t`. The proof
  uses that the supremum is directed (`fixedCharacterSpace_mono`).
- Monotonicity: `fixedCharacterSpace_mono` (increasing in `d`),
  `fixedCharacterSpace_antitone` and `fixedGeneralizedCharacterSpace_antitone`
  (increasing as `K` shrinks). Both come from `characterSpace_mono` and the published
  `fixedVectors_antitone`.
- Comparisons: `fixedCharacterSpace_le_fixedGeneralizedCharacterSpace` and
  `fixedGeneralizedCharacterSpace_le_fixedVectors`.
- Stability. `comp_apply_central` shows that `π m` commutes with every `π (ι t)`
  when `ι` has central image. Then `apply_mem_fixedCharacterSpace_conj` shows that
  `π m` maps the `K`-fixed space into the `conjSubgroup m K`-fixed space with the
  same `d`, where `conjSubgroup m K = m K m⁻¹` is the published conjugate.
  `apply_mem_fixedCharacterSpace_of_mem_center` shows that a central `z` preserves
  the `K`-fixed space, since `z K z⁻¹ = K`. `apply_mem_fixedGeneralizedCharacterSpace`
  shows that every `π (ι t)` preserves the `K`-fixed generalized space.
- `map_mem_fixedCharacterSpace`: an intertwiner `f : π.IntertwiningMap σ` maps
  `fixedCharacterSpace π ι χ K d` into `fixedCharacterSpace σ ι χ K d`. It combines
  the published `map_mem_fixedVectors` with `map_mem_characterSpace_of_intertwining`.

## The generalized weight subrepresentation

Assume `[TopologicalSpace M] [IsTopologicalGroup M]`. The compact open subgroups
form the published type `HarishChandraSchwartz.CompactOpenSubgroup M`, an open
subgroup together with compactness. Its operations `K.conj m` and `K.inf L` are reused.

- `generalizedWeightSpace π ι χ hι : Subrepresentation π` has underlying submodule
  `⨆ K : CompactOpenSubgroup M, fixedGeneralizedCharacterSpace π ι χ K.toSubgroup`.
  This is the union over compact open `K` and powers `d`. Its `M`-stability field
  (Levi stability) sends the `K`-piece with power `d` into the `K.conj m`-piece with
  the same `d`, by `apply_mem_fixedCharacterSpace_conj`. It uses only the centrality
  hypothesis `hι` and the fact that conjugates of compact open subgroups are compact open.
- `fixedGeneralizedCharacterSpace_le_generalizedWeightSpace` and
  `fixedCharacterSpace_le_generalizedWeightSpace` include each piece.
- `directed_fixedGeneralizedCharacterSpace`: the pieces form a directed family, since
  `K.inf L` is compact open and contained in both `K` and `L`.

## Restriction of intertwiners

Under the same topological-group hypotheses:

- `map_mem_generalizedWeightSpace`: an intertwiner `f : π.IntertwiningMap σ` maps
  `generalizedWeightSpace π ι χ hι` into `generalizedWeightSpace σ ι χ hι`.
- `generalizedWeightMap ι χ hι f` is the restricted intertwiner between the two
  subrepresentations, with `generalizedWeightMap_apply` (value `f v`, by `rfl`).
- `generalizedWeightMap_id` and `generalizedWeightMap_comp` are the identity and
  composition laws, both proved by extensionality.

## Smooth-character convention

`IsGeneralizedWeight π ι χ hι`, under `[TopologicalSpace A]`, is

`IsOpen (χ.ker : Set A) ∧ generalizedWeightSpace π ι χ hι ≠ ⊥`.

Renard's "caractère lisse" is a locally constant character. A homomorphism to `Rˣ`
is locally constant exactly when its kernel is open, so the convention is written
as an open kernel. This is the same convention as the published `IsJacquetExponent`,
`IsCentralExponent` and `Induction.SmoothCharacter`.

## Locally profinite membership and comparisons

The membership and comparison laws assume `[NonarchimedeanGroup M]` and
`[WeaklyLocallyCompactSpace M]`. These are exactly the hypotheses used by the
published `compactOpenSubgroupBasis` and `exists_compactOpen_fixing_finite`, which
give compact open subgroups inside every identity neighbourhood and one fixing any
smooth vector. No Hausdorff, second-countability or field hypothesis is added.

- `nonempty_compactOpenSubgroup M`: such an `M` has a compact open subgroup. This
  makes the directed union nonempty.
- `mem_generalizedWeightSpace`: `v ∈ generalizedWeightSpace π ι χ hι` if and only if
  `∃ K : CompactOpenSubgroup M, v ∈ fixedVectors π K.toSubgroup ∧
  ∃ d : ℕ, ∀ t : A, ((π (ι t) - (χ t : R) • 1) ^ d) v = 0`.
  This is the displayed compact-open membership condition, with no choice of `K`
  fixed in advance.
- `mem_generalizedWeightSpace_of_isSmooth hπ`: for smooth `π`, the condition reduces
  to `∃ d, ∀ t, ((π (ι t) - χ t • 1) ^ d) v = 0`. The compact open subgroup comes
  from `exists_compactOpen_fixing_finite`.
- `generalizedWeightSpace_toSubmodule_of_isSmooth`: for smooth `π`, the underlying
  submodule is `⨆ d, characterSpace (π.comp ι) χ d`.
- `generalizedWeightSpace_ne_bot_iff hπ`: for smooth `π`,
  `generalizedWeightSpace π ι χ hι ≠ ⊥ ↔ IsGeneralizedEigencharacter (π.comp ι) χ`.
  So nontriviality is the generic generalized-eigencharacter predicate of the
  restricted action.
- `generalizedCentralCharacterSpace_le_generalizedWeightSpace hπ χZ hχ`: comparison with
  the published full-center machinery of `Langlands.Representation.Exponents.Central`.
  If `χZ : Subgroup.center M →* Rˣ` restricts to `χ` along `ι`, then
  `generalizedCentralCharacterSpace π χZ ≤ generalizedWeightSpace π ι χ hι`. Only this
  inclusion is proved. The split component is generally smaller than the center, and
  no converse is claimed.
- `isGeneralizedWeight_iff_isOpen_ker_and hπ`: for smooth `π`, `IsGeneralizedWeight`
  is `IsOpen χ.ker ∧ IsGeneralizedEigencharacter (π.comp ι) χ`.

## Open kernel is automatic

These results take coefficients in a field `k` (universe `uR`).

- `isOpen_induced_ker_of_isGeneralizedEigencharacter_comp`: for smooth `π` over a
  topological group `M`, a generalized eigencharacter of `π.comp ι` has open kernel
  for the topology on `A` induced by `ι`. The induced topology is a group topology
  (Mathlib `isTopologicalGroup_induced`), and `π.comp ι` is smooth for it (the published
  `isSmooth_comp`). The published `isOpen_ker_of_isGeneralizedEigencharacter` then applies.
- `isOpen_ker_of_isGeneralizedEigencharacter_comp`: the same for any topology on `A`
  making `ι` continuous, since that topology is finer than the induced one. No
  topological-group structure on `A` is assumed.
- `isGeneralizedWeight_iff`: for smooth `π` over a nonarchimedean, weakly locally
  compact `M` and a continuous central `ι`,
  `IsGeneralizedWeight π ι χ hι ↔ IsGeneralizedEigencharacter (π.comp ι) χ`.

## Source correspondence (Renard VII.1.1, printed p. 220 / PDF p. 226)

| Renard | Lean |
| --- | --- |
| `(r^G_P V)^{K_M}_χ = {v ∈ (r^G_P V)^{K_M} \| ∃ d ∈ ℕ, ∀ t ∈ A, (r^G_P(π)(t) − χ(t) Id_V)^d · v = 0}` | `fixedGeneralizedCharacterSpace π ι χ K`, `mem_fixedGeneralizedCharacterSpace` |
| `t K_M t⁻¹ = K_M` for `t ∈ A`, so `A` acts on `(r^G_P V)^{K_M}` | `apply_mem_fixedCharacterSpace_of_mem_center`, `apply_mem_fixedGeneralizedCharacterSpace` |
| `K'_M ⊂ K_M ⇒ (r^G_P V)^{K_M}_χ ⊂ (r^G_P V)^{K'_M}_χ` | `fixedGeneralizedCharacterSpace_antitone` |
| `(r^G_P V)_χ = ⋃_{K_M} (r^G_P V)^{K_M}_χ`, `K_M` compact open in `M` | `generalizedWeightSpace`, `mem_generalizedWeightSpace` |
| `χ` ranges over the smooth characters of `A` | open kernel in `IsGeneralizedWeight` |
| `χ` is an exponent when the space is nontrivial | `IsGeneralizedWeight` (second conjunct) |

Here the abstract `ι : A →* M` stands for the split component of the Levi acting
on a representation of `M`. Renard's `d ∈ ℕ` may be zero, as here; the power zero
contributes only the zero vector. Renard works with admissible representations;
these definitions are stated for every representation, and the laws for every smooth
one. This is a domain extension of the definitions only. The fixed spaces are
defined for every subgroup `K`, but the union uses only compact open subgroups, as
in the source. Renard's text writes the union of subspaces; here it is the supremum
of submodules, which equals the union because the family is directed
(`directed_fixedGeneralizedCharacterSpace`, used in `mem_generalizedWeightSpace`).

## Retained boundaries

This file proves none of the following, and they are not encoded as hypotheses:
the decomposition `(r^G_P V)^{K_M} = ⊕_χ (r^G_P V)^{K_M}_χ` and (VII.1.1.1);
finiteness of the exponent set; admissibility or finite length; the Remark for
`P = G` and its comparison with III.1.10; the Lemma (i)/(ii) comparing induction
and restriction exponents; Casselman's criterion (VII.1.2); real parts, chambers,
temperedness, Langlands data and classification.

- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
