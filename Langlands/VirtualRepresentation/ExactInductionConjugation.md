# Induction along conjugate embeddings

Author: Worker 5134. Module `Langlands.VirtualRepresentation.ExactInductionConjugation`.
It is a helper for the proof of `HenniartGlobalizationStatement` (Henniart 2000,
§3.4). There the induced representation `Ind_{W_{E'_u}}^{W_{F_v}}` coming from a global
induced representation must be compared with a generator induced from the Weil group of
a conjugate extension.

## Definitions

- `FiniteRepresentation.induceAlongConjEquiv φ ψ hφ hψ g hg A`. Let `φ, ψ : H →* G` be
  injective homomorphisms whose ranges have finite index, with `ψ h = g * φ h * g⁻¹`
  for all `h`. This is an equivalence of `G`-representations between
  `induceAlong ψ hψ A` and `induceAlong φ hφ A`. An equivariant function `f` for the
  range of `ψ` goes to `x ↦ f (g * x)`, and the inverse is `x ↦ f (g⁻¹ * x)`. The two
  representations act by right translation, so the intertwining property is
  associativity.
- `ExactGrothendieckGroup.conjAlong φ g : H →ₜ* G` is the conjugate continuous
  homomorphism `h ↦ g * φ h * g⁻¹` (`conjAlong_apply`).
- `ExactGrothendieckGroup.conjCodRestrict φ S g hg : H →ₜ* S`. The hypothesis `hg` says
  that `y ∈ range φ ↔ g * y * g⁻¹ ∈ S` for every `y : G`, so conjugation by `g` carries
  the range of `φ` exactly onto the subgroup `S`. The definition is `conjAlong φ g`
  corestricted to `S`, using the Library's `codRestrictOfRange`. Its value is
  `g * φ h * g⁻¹` (`conjCodRestrict_apply`).

## Results

- `ExactGrothendieckGroup.continuousInduceAlong_eq_of_conj`: let `φ` and `ψ` be open
  embeddings of topological groups whose ranges have finite index, with
  `ψ h = g * φ h * g⁻¹`. Then `continuousInduceAlong ψ hψ = continuousInduceAlong φ hφ`
  on continuous exact virtual representations. The proof checks this on the classes of
  continuous representations using `induceAlongConjEquiv`, then uses `hom_ext`.
- `isOpenEmbedding_conjAlong`: `conjAlong φ g` is an open embedding when `φ` is one. It is
  `φ` followed by the homeomorphism `x ↦ g * x * g⁻¹`.
- `range_conjAlong`: under `hg`, the range of `conjAlong φ g` is `S`.
- `continuousInduce_characterClass_eq_along_conj`: let `φ : H →ₜ* G` be an open embedding
  with finite-index range, `S` an open finite-index subgroup, and `hg` as above. For every
  continuous character `θ` of `S`,
  `continuousInduce S hSo [θ] = continuousInduceAlong φ hφ [θ ∘ conjCodRestrict φ S g hg]`.
  The proof rewrites the left side as induction along `conjAlong φ g`, which has range
  `S` (Library `continuousInduce_characterClass_eq_along`). Then
  `continuousInduceAlong_eq_of_conj` replaces `conjAlong φ g` by `φ`.

## Provenance

These results are standard: induction is invariant under conjugating the embedded
subgroup. Henniart (2000), §3.4, uses this implicitly when it identifies the local
component of an induced global representation with an induced generator. The
definitions are auxiliary and have no separate literature definition.
