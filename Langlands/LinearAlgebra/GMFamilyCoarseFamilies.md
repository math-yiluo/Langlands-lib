# Induced families on arbitrary subspaces and families of Levi components

This module supplies three facts about `(G, M)`-families in the Euclidean model of
[GMFamilies](GMFamilies.md) that are used for descent to a subspace which need not be a Levi
flat (J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7,
`arthur-1988-invariant-trace-formula-I`).

- `extendParamL b a₁` is extension of parameters `extendParam b a₁` (precomposition with the
  orthogonal projection to `b`) as a continuous linear map; `contDiff_extendParam` records its
  smoothness.
- **Induced families are families** (`isFamily_inducedFamily`). For a root set `R`, a subspace
  `b ≤ a₁` and a family `c₁` on `a₁`, the induced family `inducedFamily R b a₁ c₁` on `b` is a
  family. The first condition follows from `inducedFamily_eq_of_extension` of
  [GMFamilyInducedValues](GMFamilyInducedValues.md): on each coarse chamber the induced function
  is `c₁ P₁ ∘ extendParam b a₁` for any fine chamber `P₁` above it. For the compatibility across a
  coarse wall, two fine chambers over adjacent coarse chambers are compared through
  `family_eq_of_protected_signs`: the roots whose sign changes all restrict to multiples of the
  common wall, so the two values agree on the wall.
- **Levi components.** For a face `Q` of a Levi flat `a`, `isLeviSpace_leviRoots_of_mem_faces` shows that `a` is
  still a Levi flat for the roots `leviRoots R Q` of the Levi component, `isRootSet_leviRoots`
  that these form a root set, and `isFamily_union` that `S ↦ c (Q ∪ S)` is a family for them
  whenever `c` is a family for `R` (simple roots of `S` stay simple for `Q ∪ S`, by the private
  lemma `mem_simpleRoots_union`).
- **Smooth relative supplementary functions** (`exists_smooth_cQM`). Applying the Library's
  `smoothExtension` to each Levi component gives functions `cQ Q`, smooth for every `Q`, equal to
  `cQM R a c Q` at every parameter where the `θ`-denominators of the Levi component do not
  vanish (and `0` off the faces).
