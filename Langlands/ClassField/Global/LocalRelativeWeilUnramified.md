# Local relative Weil maps at places of ramification index one

Author: Worker 5137.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
describes, at a place `w` of `E` above a finite place `z` of `F` with ramification index
one, which elements of the local Weil group `W_{F_z}` come from `W_{E_w}`, and which are
sent into the idele class group `C_E` by a local relative Weil map
`ι : W_{F_z} → W_{E/F}`. These are standard facts of local class field theory (an
unramified extension `E_w / F_z` of residue degree `f` has `W_{E_w}` equal to the
elements of `W_{F_z}` whose degree is divisible by `f`); the proofs below use only
results already in the Library.

## `Langlands.Weil.Local.mem_extensionWeilMap_range_iff_dvd`

For an extension `f : F → E` of p-adic fields such that the absolute inertia of `F` lies
in the image of `G_E → G_F` (hypothesis `hI`), an element `g` of `W_F` lies in the
image of `extensionWeilMap F E f` exactly when the residue degree
`extensionResidueDegree F E f` divides the integer degree `localDegreeInt F g`.

- Forward: `localDegreeInt_extensionWeilMap` says the degree of the image of `x` is the
  residue degree times the degree of `x`.
- Backward: if the degree of `g` is `f · m`, choose `x ∈ W_E` of degree `m`
  (`localDegree_surjective`). Then `g' = g · ι(x)⁻¹` has degree zero, so its Galois
  projection lies in inertia (`localResidueDegree_ker` and the defining property of
  `W_F`). By `hI` that projection comes from `G_E`; hence the projection of `g`, being
  the product of the projections of `g'` and of the image of `x`, lies in the image of
  `G_E`, and `extensionWeilMap_range` (the image of `W_E` is the preimage of the image of
  `G_E`) concludes.

## Valuations (section `Valuation`)

- `discreteValuation_padicField`: the normalized discrete valuation of the canonical
  topological data of `padicField w` is the valuation `Valued.v` of the completion
  `K_w`. Both are surjective valuations with the same valuation ring
  (`discreteValuation_eq_of_vle`, `topologicalData_vle`,
  `valuedAdicCompletion_surjective`).
- `discreteValuation_padicFieldAt`: the same statement for the package transported to
  an equal residue prime (by `subst`).

## Ramification index one (section `Unramified`)

Here `w` lies over `z` and `he` says that the ramification index of `w` over `𝓞 F` is
one.

- `ramificationIndex_eq_of_ramificationIdx_eq_one`: the canonical absolute ramification
  indices of `F_z` and `E_w` agree. Both are the valuation of `p`; the valuation of the
  image of `p` under the completion map is the ramification index (one) times the
  valuation in `F_z` (`FiniteExtension.valuation_completionMap`).
- `absoluteInertia_le_completionGaloisRange`: absolute inertia of `F_z` lies in the image
  of `G_{E_w}`, by the Library criterion
  `PadicField.absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq`.
- `mem_completionWeilMap_range_iff`: an element of `W_{F_z}` lies in the image of
  `W_{E_w}` exactly when the residue degree of `E_w / F_z` divides its degree; this is
  the first lemma with the previous inclusion.

## The inverse image of `C_E` (section `Inverse`)

Here `E / F` is Galois, `c` is a class family satisfying `FundamentalClass.Restriction c`
(hypothesis `h`).

- `mem_range_restrictionInclusion_self_iff`: the image of `W_{E/E}` in `W_{E/F}` under
  `restrictionInclusion` is the idele-class subgroup `ideleClassSubgroup c F E`. By
  `range_restrictionInclusion` an element lies in that image exactly when its projection
  to `Gal(E/F)` is trivial, which is the definition of the idele-class subgroup through
  the exactness of `C_E → W_{E/F} → Gal(E/F)`.
- `mem_ideleClassSubgroup_iff`: let `ι : W_{F_z} →* W_{E/F}` satisfy the compatibility
  `hι` with the embedding `closurePlaceEmbedding z w : E → \bar{F_z}` (the projection of
  `ι g` to `Gal(E/F)` corresponds to the Galois projection of `g`). Then `ι ℓ ∈ C_E`
  exactly when `ℓ` lies in the image of `W_{E_w}`. This is the Library lemma
  `conj_mem_range_restrictionInclusion_iff` applied with the subfield `E` itself, the
  place `w` and the trivial coset representative, followed by the previous lemma.
