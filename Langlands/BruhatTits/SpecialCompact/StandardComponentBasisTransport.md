# Basis members do not depend on the compatible split component

Lean module: `Langlands.BruhatTits.SpecialCompact.StandardComponentBasisTransport`, namespace
`Langlands.BruhatTits.SpecialCompact`.

## Purpose

`StandardParabolicBasisMember i ν J q K` (module `StandardBasisProperty`) is the conjunction of
the Iwahori intersection decomposition of `K` along `M_J`, `N_J` and the opposite `N̄_J`, and the
contraction and cofinality clauses of Renard, *Représentations des groupes réductifs p-adiques*,
V.5.2(ii)–(iv), for the chambers `C_A`, `C_A^+`, `C_A^{++}` and `C_A(ε)` of one compatible split
component `q : A → S` of `M_J`, mapped into `G(F)`. `SimultaneousStandardBasisAt` supplies basis
members for *some* compatible split component of each standard Levi. This module proves that the
property does not depend on which compatible split component is used, so a basis for one
component is a basis for any other.

## Contents

- `ContractionAndCofinality.mono` (any topological group `H`): the six clauses of
  `ContractionAndCofinality K M N Nbar CA CAplus CAstrict CAeps` quantify over the points of the
  four chamber sets only, so they pass to smaller chamber sets: if `CA ⊆ CA'`,
  `CAplus ⊆ CAplus'`, `CAstrict ⊆ CAstrict'` and `CAeps ε ⊆ CAeps' ε` for every `ε`, the clauses
  for the primed sets give the clauses for the unprimed sets. The subgroups `K`, `M`, `N`, `Nbar`
  are unchanged.
- `IsCompatibleStandardSplitComponent.exists_cocharacter_eq`: for compatible split components
  `q : A → S` and `q' : A' → S` of the same `M_J` (`G` connected reductive, `i` maximal split,
  `ν` generic, `J ⊆ Δ`), every cocharacter `c` of `A` has a cocharacter `c'` of `A'` with
  `q' ∘ c' = q ∘ c` in the cocharacters of `S`.
- `map_comp_latticeSection_eq`: if `q' ∘ c' = q ∘ c`, the common-uniformizer values
  `latticeSection F A' c'` and `latticeSection F A c` have the same image in `G(F)` under
  `q' ≫ i` and `q ≫ i`.
- `characterNorm_componentCharacterRestriction_eq`: under the same equation, for every character
  `α` of `S` the norm of the restriction of `α` to `A'` at `latticeSection F A' c'` equals the norm
  of the restriction of `α` to `A` at `latticeSection F A c`.
- `image_componentChamber_subset`: for every condition `p : ℝ → Prop`, the image in `G(F)` of the
  part of `C_A` where every restricted simple root outside `J` has norm satisfying `p` is
  contained in the corresponding image for `A'`. With `p = (· ≤ 1)`, `(· < 1)` and `(· < ε)` these
  are the images of `C_A^+`, `C_A^{++}` and `C_A(ε)`, that is `standardComponentCAplus`,
  `standardComponentCAstrict` and `standardComponentCAepsilon`.
- `standardComponentCA_subset`: `standardComponentCA i q ⊆ standardComponentCA i q'`.
- `StandardParabolicBasisMember.of_compatibleComponent`: if `K` is a standard-parabolic basis
  member for `J` with respect to `q'`, it is one with respect to `q`.

Exchanging the two components, the chamber images for `q` and `q'` are equal; the module states
the inclusions only, which is what the transport needs.

## Proofs

`exists_cocharacter_eq`: the cocharacter `q ∘ c` of `S` annihilates every root in `J`
(`IsCompatibleStandardSplitComponent.pairing_eq_zero`, module `StrictChamberPowerBasis`). A
cocharacter of `S` annihilating `J` lifts to every compatible split component of `M_J`
(`IsCompatibleStandardSplitComponent.exists_cocharacter_lift_of_annihilates`, module
`StandardLeviWeakChamberTransport`), whose hypothesis that a standard cocharacter for `J` exists is
discharged by `standardCocharacter` (module `StandardCocharacterProof`).

`map_comp_latticeSection_eq`: both maps factor through `i`, and
`CocharacterUniformizer.map_latticeSection` identifies the image of a lattice-section value under a
homomorphism of split tori with the lattice-section value of the image cocharacter.

`characterNorm_componentCharacterRestriction_eq`: `characterNorm_latticeSection` gives the norm as
`q_F ^ (-⟨χ, c⟩)` with `q_F` the residue cardinality, and `componentCharacterRestriction_pairing`
rewrites `⟨α|_A, c⟩` as `⟨α, q ∘ c⟩`; the given equation finishes.

`image_componentChamber_subset` and `standardComponentCA_subset`: a point of the image for `A` is
the image of some `latticeSection F A c`; `exists_cocharacter_eq` gives `c'`, the lattice-section
value at `c'` lies in `C_A'`, it has the same image in `G(F)`, and the norm conditions transfer by
`characterNorm_componentCharacterRestriction_eq`, since the characters
`standardParabolicComponentCharacters i ν J q` are the restrictions of the simple roots outside `J`.

`of_compatibleComponent`: the Iwahori intersection decomposition does not mention the component and
is kept; the contraction and cofinality clauses transfer by `ContractionAndCofinality.mono` with
the four inclusions above.

## Provenance

The basis-member property formalizes Renard V.5.2 (see the Markdown of `StandardBasisProperty`).
The independence from the choice of split component is internal: it follows from the published
results named above, and shows that the images in `G(F)` of the chambers used in Renard V.5.2
depend only on `J`, not on the chosen compatible split component of `M_J`.
