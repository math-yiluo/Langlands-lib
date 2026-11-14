# Torus character-kernel reduction for a norm-law homomorphism

This derived supporting construction proves the kernel identity of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Lemma 11.1.3,
printed p. 422, PDF p. 453, on rational points (the restriction paragraph after
Proposition 11.1.5, printed p. 423, PDF p. 454). It does so from the norm
characterization of the torus Kottwitz map in Proposition 11.1.1, printed
p. 421, PDF p. 452. The November 2024 corrections leave these assertions
unchanged.

## What is proved

The imported [reduction module](TorusCharacterKernelReduction.md) defines `TorusCharacterKernelInputs` as the conjunction of two unconditional
propositions that must be proved separately:

* `TorusKottwitzExistenceStatement` (KP Proposition 11.1.1). The proof uses
  only its second component: the constructed `torusKottwitz` satisfies the norm
  law at every finite Galois splitting extension.
* `NormalizedIntermediateValuationStatement`: every finite extension `L` of
  `UnramifiedClosure F` inside `SeparableClosure F` has a unique surjective
  integer normalization of its spectral valuation. The proof uses only the
  existence part, through `normalizedIntermediateValuation_spec`, which makes
  `normalizedIntermediateValuation F L` equivalent to `intermediateValuation F L`.

`TorusCharacterKernelInputs.torusCharacterKernel` proves the existing
`TorusCharacterKernelStatement` from this conjunction. It is a conditional
reduction. It does not prove the target or either input unconditionally.

The theorem `characterValuationKernel_eq_comap_torsion_of_normLaw` is the main
step for one torus. Take a nonarchimedean local field `F`, an `F`-torus `T`,
and any homomorphism `κ` from the points over `UnramifiedClosure F` to the
inertia coinvariants of the geometric cocharacters. Suppose `κ` satisfies
`TorusNormLawAt` at one finite Galois extension `L` of `UnramifiedClosure F`
that splits `T`, and `normalizedIntermediateValuation F L` is equivalent to
`intermediateValuation F L`. Then the rational-character valuation kernel of
`T(F)` is the inverse image of torsion under `κ` composed with extension of
rational points. This theorem has no further hypotheses.

## The implemented proof

The KP proof of Lemma 11.1.3 reduces to the maximal split quotient and uses
functoriality of the Kottwitz map. The Lean proof takes a different route. It
uses only the norm law at a single splitting field together with an explicit
computation on extended points.

*Norm of an extended point.* For a finite Galois extension `M/L`, the
relative norm of the extension of an `L`-point `x` is `x ^ |Gal(M/L)|`
(`relativeNorm_relativeExtend`). Two successive rational extensions agree with
the direct extension under the tower base-change comparison
(`towerBaseChangeIso_rationalExtend`). Combining these with the norm law
(`normLaw_pow_card`) shows that `κ(x)` raised to the power `n = |Gal(L/K)|`
is the image in the inertia coinvariants of the split valuation of the
extension of `x` to `L`. Here `x` is the extension of a rational point and
`K = UnramifiedClosure F`.

*Kernel points map to torsion.* Let `x` be in the character kernel over `F`.
The published descent theorem `characterValuationKernelDescent_proof` places
its extension to `K` in the character kernel for the fixed-field valuation.
Extension of valuations (`characterValuationKernel_le_comap`) then places the
extension to `L` in the character kernel for `intermediateValuation F L`. The
tower comparison is transported in three separate lemmas. On a split torus,
character-kernel membership for an equivalent valuation forces the split
valuation to be trivial (`splitValuation_eq_one_of_mem`). This uses the
pairing formula `splitValuation_pairing` and nondegeneracy of
`cocharacterDualEquiv`. Hence `κ(x) ^ n = 1`.

*Torsion points lie in the kernel.* If `κ(x)` has finite order, so does
`κ(x) ^ n`. The image in the inertia coinvariants is therefore additively
torsion. Each base-field character `χ` gives an integral functional that is
invariant under the Galois action. It descends through the coinvariants
(`Representation.Coinvariants.lift`), so it vanishes on torsion classes
(`functional_eq_zero_of_isOfFinAddOrder`). The pairing of a character with an
extended cocharacter equals the pairing over `L`
(`latticePairing_extendGeometricCocharacters`, through
`characterLattice_baseChange_tower_hom`). The pairing of the base change of `χ`
with the split valuation of the extended point is therefore zero
(`latticePairing_eq_zero_of_isOfFinAddOrder`). By `splitValuation_pairing`,
the value `χ(x)` has integer order zero for the normalized valuation of `L`.
The equivalence of valuations and the extension chain `F ⊆ K ⊆ L` then give
`val_F(χ(x)) = 1` (`valuation_rationalCharacterEval_eq_one_of_pairing`).

*Shared assembly.* The imported theorem `TorusCharacterKernelInputs.torusCharacterKernel`
chooses a finite Galois splitting field `L` inside `SeparableClosure F` for the
base change of `T` to `K`, using `exists_finiteGaloisSplittingField_inside`. It
transfers splitness to the base change from `F` along the tower comparison
`IsSplitTorus.of_iso`. The first input supplies the norm law and the second the valuation normalization. Its two membership arguments give the same target as the one-torus theorem here specialized to `κ = torusKottwitz F F T hT`.

## Provenance

The provenance is derived. Lemma 11.1.3 and its restriction to rational points
are the source statements. The route through the norm law and explicit
extended-point computations is internal to this Library. It is designed to
avoid the maximal-split-quotient and functoriality arguments, which the
Library does not yet contain. The original target and every module it imports
are unchanged.


The common relative-norm, rational-extension and cocharacter-pairing lemmas are imported from `TorusCharacterKernelReduction`; their statements are unchanged. The `_hom`, `_of_normLaw` and `_of_isEquiv` names distinguish the helper formulations retained in this module.
