# Detecting nonzero rational characters by the actual valuations

Authors: Worker 1521 (Lean proofs and text) and Worker 1171 (proposed the route through the
perfect uniformizer pairing and the three structural reductions).

This module proves that the actual valuation map `rationalCharacterValuation G` detects nonzero
rational characters. It does this unconditionally along split tori. For a connected reductive `G`,
it does this under each of three published Library propositions that are still unproved:

- `Langlands.GroupScheme.CentralSplitTorusCharacterStatement`;
- `Langlands.GroupScheme.CentralTorusCharacterStatement`;
- `Langlands.GroupScheme.CharacterRestrictionStatement`.

The conclusion in every case is

`∃ g : rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0`.

The witness along a split torus `s : T ⟶ G` is the image `s(ϖ^c)` of a uniformizer point, named
`splitTorusUniformizerPoint s c`.

The module proves none of the three structural propositions. It does not prove
`Langlands.Plancherel.RationalCharacterTensorParameterStatement` either. It is the detection input
that a proof of that statement combines with the integer linear algebra of the tensor parameter.
The conclusion is written out as an explicit formula, so this module does not depend on any
packaging of it as a named predicate.

## Provenance

The content is internal: it consists of deductions from published Library definitions and
theorems, with no new source claim. It uses:

- `Langlands.GroupScheme.CocharacterUniformizer.latticePairing_isPerfPair`: the integer pairing
  `latticePairing T` of a split torus `T` is perfect;
- `Langlands.Plancherel.RenardCartan.rationalCharacterValuation_map_uniformizerSection`: the
  valuation of `s(ϖ^c)` on `χ` is `⟨r(χ), c⟩`, where `r(χ)` is `characterRestrict s χ` viewed in
  `characterLattice T` and `ϖ^c` is `uniformizerSection T (ofAdd c)`;
- `Langlands.GroupScheme.CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus`:
  a nonzero character of a torus that is affine and locally of finite type is nonzero on some
  homomorphism `𝔾_m ⟶ Z`;
- `Langlands.GroupScheme.isSplitTorus_gm` and `Langlands.GroupScheme.characterRestrict_comp`;
- `Langlands.GroupScheme.splitComponentStatement`: a connected reductive group has a split
  component.

## Setting

`F : Type u` is a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), of any characteristic. `G` is a group scheme over `Spec F`.
Everything lives in the namespace `Langlands.Plancherel.RationalValuationDetection`.

## Declarations

`splitTorusUniformizerPoint s c`: for a commutative group scheme `T` over `Spec F`, a
homomorphism `s : T.toGrp ⟶ G` and a cocharacter `c : cocharacterLattice T`, this is the rational
point `s(ϖ^c) = rationalPoints.map s (uniformizerSection T (ofAdd c))` of `G`. Here
`uniformizerSection T` is the published uniformizer section of the cocharacter lattice. The
definition only names this point; it needs no splitness hypothesis.

`rationalCharacterValuation_splitTorusUniformizerPoint s c χ`: the valuation of `s(ϖ^c)` on `χ`
equals `latticePairing T (equivCharacterLattice T (characterRestrict s χ)) c`. This is
`rationalCharacterValuation_map_uniformizerSection` with the point written through the definition.

`exists_map_uniformizerSection_ne_zero s hT hχ`: let `T` be a commutative group scheme over
`Spec F` that is a split torus (`hT : IsSplitTorus T.toGrp`), and let `s : T.toGrp ⟶ G`. If
`characterRestrict s χ ≠ 0`, then some cocharacter `c` of `T` has
`(rationalCharacterValuation G (splitTorusUniformizerPoint s c)).toAdd χ ≠ 0`.
Proof: `rationalCharacters.equivCharacterLattice T` sends the nonzero restricted character to a
nonzero `α ∈ characterLattice T`. The pairing is perfect, so the left map
`latticePairing T` is injective and `latticePairing T α` is a nonzero linear form. Pick `c` with
`⟨α, c⟩ ≠ 0`. By the previous formula this pairing is the valuation of `s(ϖ^c)` on `χ`.

`exists_rationalCharacterValuation_ne_zero_of_splitTorus s hT hχ`: under the same hypotheses,
some rational point `g` of `G` has `(rationalCharacterValuation G g).toAdd χ ≠ 0`. Take
`g = s(ϖ^c)` from the previous lemma.

`exists_rationalCharacterValuation_ne_zero_of_centralSplitTorusCharacter hS hG hχ`: assume
`hS : CentralSplitTorusCharacterStatement.{u}`, a connected reductive `G` and a nonzero rational
character `χ`. Then some rational point `g` has nonzero valuation on `χ`. Proof:
`hS F G hG χ hχ` gives a central split torus `i : A.toGrp ⟶ G` with `characterRestrict i χ ≠ 0`.
Its first component gives `IsSplitTorus A.toGrp`, and the split-torus lemma applies.

`exists_rationalCharacterValuation_ne_zero_of_centralTorusCharacter hS hG hχ`: the same
conclusion from `hS : CentralTorusCharacterStatement.{u}`. Proof: `hS` gives a central closed
torus `i : Z.toGrp ⟶ G`. It also gives `IsAffineHom` and `LocallyOfFiniteType` for the structure
morphism of `Z`, `IsTorus Z.toGrp`, and `characterRestrict i χ ≠ 0`.
`exists_gm_characterRestrict_ne_zero_of_isTorus` gives `φ : 𝔾_m ⟶ Z` with
`characterRestrict φ (characterRestrict i χ) ≠ 0`. By `characterRestrict_comp` this is
`characterRestrict (φ ≫ i) χ ≠ 0`. Since `𝔾_m` is a split torus (`isSplitTorus_gm`), the
split-torus lemma applies to `φ ≫ i`. Centrality and closedness of `i` are not used.

`exists_rationalCharacterValuation_ne_zero_of_characterRestriction hR hG hχ`: the same conclusion
from `hR : CharacterRestrictionStatement.{u}`. Proof: `splitComponentStatement F G hG` gives a
split component `i : A.toGrp ⟶ G`. By `hR`, `characterRestrict i` is injective, so
`characterRestrict i χ ≠ 0`. A split component is a central split torus, so `A` is a split
torus, and the split-torus lemma applies.

## Scope

All results keep the field universe `u` and the local-field instances unchanged. The three
conditional theorems take the full universe-`u` structural propositions as hypotheses, and those
hypotheses are explicit. Nothing here assumes splitness of `G`, a rank condition, or
characteristic zero.
