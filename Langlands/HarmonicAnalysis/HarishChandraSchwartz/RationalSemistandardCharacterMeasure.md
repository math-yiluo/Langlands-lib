# Source measures on every actual semistandard Levi

Namespace
`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure`.
This derived source-normalization adapter supports the weighted synthesis of
Waldspurger's invariant spectral families.
It applies to every actual intrinsic semistandard index and each of its
`LeviModel` witnesses. It uses the model's actual rational-point inclusion
homeomorphism; neither the literal Levi nor the inducing representation is
replaced by an arbitrary comparison object.

The source is J.-L. Waldspurger (2003), *La formule de Plancherel pour les
groupes p-adiques*, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.1, printed page 239 (PDF page 5), fixes the split-component character
measure and the local measure-preservation convention for restriction.
VI.3, printed page 302 (PDF page 68), fixes orbit measure by local
measure preservation of twisting. The finite-kernel and self-twist
cardinality formulas below are derived from the published constructions
implementing those conventions. The proof route generalizes the actual
standard-Levi adapter in `StandardLeviCharacterMeasure`, reusing its
underlying rational source measures and the existing class-pullback laws.

The field has arbitrary characteristic, the canonical nonarchimedean
local-field topology and independent universe `u`. Representation carriers
have independent universe `uV`. The ambient scheme is affine and locally
of finite type. The index supplies the actual closed connected reductive
Levi model, so no ambient splitness or quasi-splitness is required. Rank
zero is included. The point-group topology is always the canonical one;
no representation-carrier topology is introduced.

Write `L = m.scheme`, `M = RationalSemistandard.levi p` and
`eM = m.pointHomeomorph : L(F) ≃ₜ* M`. The displayed actual split component
is `s : T.toGrp ⟶ L`, with affine `T` and `hs : IsSplitComponent s`.
The intrinsic split-center image is `CL = range(s(F))`; its literal image
is exactly `CM = m.splitCenter s = eM(CL)`. The normality instances are
mathematical consequences of `hs` and `m.splitCenter_le_center`; the
adapter retains the instances needed by the existing quotient APIs.
The displayed literal central quotient has its Borel measurable space
and Haar measure `mu`. The intrinsic quotient uses its Borel measurable
space. These Haar measures retain the source's scale when the caller
supplies the source Haar normalization; the adapter adds no scalar.

The premise `hindex : (RenardCartan.splitValuationImage s).FiniteIndex`
remains explicit. It concerns the actual split valuation image and is an
outstanding structural obligation of the standing program. It is not a
new permitted external assumption. Imported results derive finiteness of
the restriction kernel and self-twist group from this premise.

`unitaryCharacterHomeomorph` is the existing canonical transport on
unitary unramified characters, from the intrinsic rational norm family to
`m.normCharacters` on the literal Levi. `unitaryCharacterHaar` pushes the
actual `rationalUnitaryUnramifiedCharacterHaar` through it. The Haar and
finite-measure instances and `unitaryCharacterHaar_univ` retain exactly the
restriction-kernel-cardinality mass. This is generally not a probability
measure.

`centralQuotientHomeomorph` is induced by the actual inclusion equivalence.
`intrinsicQuotientHaar` pulls `mu` back through it, and
`map_intrinsicQuotientHaar` proves exact pushforward equality.
`intrinsicDiscreteSeriesClass` is the existing square-integrability-
preserving pullback of a discrete-series class. The class remains
represented on the literal Levi in the family; this intrinsic class is
auxiliary to the source-measure comparison.

`characterHomeomorph_map_stabilizer` proves that the intrinsic self-twists
map to exactly the literal self-twists. The proof applies injectivity of
class pullback and its twisting law in both directions. `stabilizer_card`
uses the resulting group equivalence, and
`finite_literalDiscreteSeriesStabilizer` transports the published
intrinsic finiteness result. No independent self-twist finiteness
hypothesis is needed mathematically. Later lemmas retain a `Finite`
instance to elaborate the existing literal orbit measure; the preceding
theorem supplies it.

`orbitHomeomorph` composes the existing orbit-stabilizer homeomorphisms
with the quotient of the actual character homeomorphism. Its orbit-map
formula proves that it sends the class of `omegaL` twisted by `z` to the
class of `omega` twisted by the transported character. No topology on the
whole smooth dual is needed.

`normalizedOrbitMeasure` pushes the existing
`rationalNormalizedDiscreteSeriesOrbitMeasure` through this homeomorphism.
Its finite-measure instance reuses `RationalOrbitIntegration`.
`normalizedOrbitMeasure_eq` proves equality with the exact literal
`discreteSeriesOrbitMeasure` using `unitaryCharacterHaar`, by comparing
measurable sets, the orbit-map square and the stabilizer cardinalities.
The `_eq_smul_map` and `_univ` formulas retain the reciprocal self-twist
factor and total mass:

- the orbit measure is `|SelfTwists(omega)|⁻¹` times the character-measure
  pushforward along twisting;
- its total mass is `|RestrictionKernel(s)| / |SelfTwists(omega)|`.

`isLocallyMeasurePreserving_normalizedOrbitMap` specializes the published
local measure-preservation theorem. `isFiniteMeasure_literalOrbitMeasure`
transfers the finite-measure instance to the exact measure in the existing
wave-packet integral. Every lemma in this pair is proved.

This adapter does not prove the valuation-image finite-index premise,
choose a source special compact, compare unrelated split components or
Levi models, or transport inter-parabolic normalized comparisons. It does
not construct density, source constants, wave packets, global synthesis,
a global form or Schwartz membership. Those additional
constructions and exact targets are separate.
