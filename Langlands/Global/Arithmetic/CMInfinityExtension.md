# Extending CM infinity characters through a finite class quotient

This module constructs the base continuous character used for unramified
CM infinity-type realization. It uses the actual arithmetic ideles and
idele classes of an arbitrary CM number field `K : Type u`. There is no
chosen imaginary-quadratic subfield.

## Construction and provenance

The construction is derived from the finite-obstruction argument in Guy
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
un corps p-adique* (2000), Section 3.5, Lemma 1 and its proof, printed
p.450 (one-based PDF p.12). Registered source:
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Worker 1231 read that page directly. The original uses a quotient by
the conjugation norm and a character-extension argument. This module
instead uses a continuous power map into a subgroup of finite index;
the construction is internal and the resulting theorem is derived.

Write `J` for the idele group, `C` for the idele class group, `U` for
`integralIdeles K`, and `H` for its image `integralIdeleClasses K`.
The coordinates of an element of `U` are valuation units at every
finite place, and its archimedean coordinates are unrestricted.
`infinityProjection` is the continuous homomorphism `J → (InfiniteAdeles K)ˣ`
induced by the archimedean projection of the adele ring.

For a continuous infinity character `η` trivial on global integral units,
`integralInfinityCharacter η` is its restriction to `U`.
`integralInfinityCharacter_ker` proves it is trivial on the kernel of
`U → H`. Indeed, an integral principal idele comes from an ordinary
unit of `𝓞 K`, by the published `principalIdeleUnitCriterion`.
`integralClassCharacterHom` descends this homomorphism using
`MonoidHom.liftOfSurjective`. `integralClassCharacter` equips this
descent with its proved continuity.

Set `h = classExponent K = Nat.card (IntegralIdeleClassQuotient K)`.
The published `integralIdeleClassQuotientFinite` proves this quotient
finite, and its group identity makes it nonempty, so `h > 0`.
The finite-group identity `q ^ h = 1` shows `c ^ h ∈ H` for every
`c ∈ C`. `classPower` is the continuous homomorphism `C → H`
sending `c` to `c ^ h`. The definition `extendedCharacter η hη`
composes this map with `integralClassCharacter η hη`.
Its exact formula on integral ideles is

`extendedCharacter η hη (class x) = η (infinityProjection x) ^ h`.

This formula also proves triviality on any integral idele whose
archimedean projection is one. No abstract extension theorem or
extension datum is assumed.

## Global-unit obstruction

For an anticyclotomic integral infinity type `a`, let
`t = NumberField.Units.torsionOrder K`. Mathlib proves `t > 0` and
that the `t`-th power kills every torsion unit.
Mathlib's `IsCMField.unitsMulComplexConjInv` places
`ε / complexConj(ε)` in the torsion subgroup for every
`ε : (𝓞 K)ˣ`. The lemma `coordinate_diagonal_ratio` identifies its
complex image with the corresponding infinity-coordinate ratio.
The anticyclotomic formula for `InfinityType.toCharacter` expresses
its value as a product of integral powers of these ratios.
Consequently `toCharacter_global_unit` proves that the character
of the scaled type `t * a` is trivial on every global integral unit.

The theorem `exists_base_character` applies the extension construction
to this character. It gives the positive common multiplier `n = h * t`
and a continuous Hecke character `ψ`, whose infinity character is
`InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)`.
It also gives its value on every integral idele as the value of that
infinity character on the archimedean projection. The identity
`toCharacter_scale` proves the common scaling formula directly from
the finite product defining the infinity character.
Conjugate self-duality is supplied by the later antisymmetrization step.

## Topology

The units topology on `J` controls both an adele and its inverse.
The everywhere-integral subset of the finite restricted product is
open because each local valuation subring is open.
`isOpen_integralIdeles` pulls this open set back along the finite
value projection and the finite inverse projection, then intersects
the preimages. The local criterion that an element and its inverse
are integral exactly when its valuation is one identifies this
intersection with `U`.

The quotient map `J → C` is open. Restricting its domain to the open
subgroup `U`, and its codomain to the image `H`, gives an open,
continuous, surjective map `U → H`, with the subspace topology on `H`.
Thus `integralIdelesToClasses_isQuotientMap` is an actual quotient-map
proof. Its continuity criterion proves the descended character
continuous. Finally, the power map is continuous into `C`; the
subspace criterion proves `classPower : C → H` continuous.
The construction uses these existing topologies throughout.
