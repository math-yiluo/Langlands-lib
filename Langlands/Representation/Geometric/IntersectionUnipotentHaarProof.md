# Haar scaling on the actual unipotent intersection

Authors: Worker 76 (proof draft) and Worker 799 (review, revision and
submission).

The module proves the published proposition
`Langlands.Geometric.PadicIntersectionUnipotentHaarModulus.{uF}` from
`Langlands.Representation.Geometric.IntersectionUnipotentHaarStatement`.
Its closing theorem is

```
Langlands.Geometric.padicIntersectionUnipotentHaarModulus :
  PadicIntersectionUnipotentHaarModulus.{uF}
```

The theorem is unapplied and keeps the arbitrary field universe `uF`.
The statement's Lean/Markdown pair and its imported pairs are preserved.

## Groups, action and conclusions

The quantifiers are those of the published statement: every prime `p`, actual
finite p-adic extension `F`, supplied compatible `T : F.TopologicalData`,
natural rank `n`, block shapes `B, C`, permutation `w`, refinement `S` of `B`,
and full triple `hS : IsIntersectionRefinement B C w S`. In particular, the
proof does not require a positive rank or a minimal representative.

Use exactly the groups and maps of the statement:

```
M = B.leviSubgroup F.Carrier
N = C.leviSubgroup F.Carrier
V = C.unipotentSubgroup F.Carrier
g = GeneralLinear.permutation n F.Carrier w
L = General.intersectionIn M N g
U = intersectionSource M V g
eL = refinedLeviIntersectionEquiv F.Carrier B C w S hS
eU = refinedUnipotentIntersectionEquiv F.Carrier B C w S hS
ι = General.intersectionToCorrectionNormalizer M N M V g
      M.le_normalizer
      (C.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
```

Thus `U` is the literal ambient subgroup `M ∩ g⁻¹ V g`, and `L` is
`M ∩ g⁻¹ N g` viewed inside `M`. The map `ι` acts by the ambient matrix's
conjugation. The canonical continuous multiplicative equivalences `eL` and
`eU` send refined Levi and radical coordinates to these actual intersections.
All topologies come from the supplied `T.topology`.

For `m : L` set `c(m) = T.refinedLeviModulus B S (eL.symm m)`.
The first conclusion, for every Borel measurable structure on `U` and every
supplied Haar measure `μ`, is

```
μ.map (HaarModulus.normalizerConj U (ι m)) = (c(m) : NNReal)⁻¹ • μ.
```

The second is the equality of positive homomorphisms

```
((HaarModulus.normalizerCharacter U).comp ι).comp eL.toMulEquiv.toMonoidHom
  = T.refinedLeviModulus B S.
```

The measure law does not assume a particular normalization, regularity or
coordinate-product form for `μ`. The character uses its published canonical
Borel structure.

## Transport of an arbitrary Haar measure

The proof installs the actual field and general-linear topological instances,
the published local compactness of `U`, the topology on `B.Levi F.Carrier`,
and the published local compactness of the refined radical. For the supplied
Borel structure on `U`, `BorelSpace.measurable_eq` identifies it with
`borel U`. The refined radical also receives its Borel structure.

Fix `m : L` and a supplied Haar measure `μ`. Put `ν = μ.map eU.symm`.
The continuous group equivalence transports the Haar property by
`ContinuousMulEquiv.isHaarMeasure_map`. Write

```
a = HaarModulus.normalizerConj U (ι m)
b = HaarModulus.normalizerConj (refinedUnipotent F.Carrier B S)
      (refinedLeviNormalizer F.Carrier B S (eL.symm m)).
```

The independently published theorem `padicRefinedUnipotentHaarModulus`
applied to `ν` gives `ν.map b = c(m)⁻¹ • ν`.
The published `refinedUnipotentIntersectionEquiv_normalizerConj`, evaluated
at `eL.symm m`, gives `a ∘ eU = eU ∘ b`. The inverse identities for `eU`
and `Measure.map_map` give `ν.map eU = μ`. Every map here is measurable
because it is continuous between spaces equipped with their Borel structures.
Consequently, the implemented calculation is

```
μ.map a
  = (ν.map eU).map a
  = (ν.map b).map eU
  = c(m)⁻¹ • ν.map eU
  = c(m)⁻¹ • μ.
```

The middle scalar step uses `Measure.map_smul`. This proves the first
conjunct for the original arbitrary Haar measure.

## Identification of the character

The proof compares the positive homomorphisms pointwise using `MonoidHom.ext`
and `Units.ext`. Equip `U` with its canonical Borel structure, the one used by
`normalizerCharacter`. Local compactness gives a positive compact set `K₀`;
take `μ = haarMeasure K₀`, so `μ K₀ = 1`. Mathlib's instances make this
measure a Haar measure and regular, as `normalizerCharacter_smul_map`
requires.

For `m` in the refined Levi, write
`χ(m) = HaarModulus.normalizerCharacter U (ι (eL m))` and
`d(m) = T.refinedLeviModulus B S m`. The published
`HaarModulus.normalizerCharacter_smul_map` gives
`χ(m) • μ.map a = μ`, with `a` the conjugation for `eL m`.
The first conjunct, already proved above for every Borel structure and every
Haar measure, applies to this `μ` at `eL m`; with `eL.symm (eL m) = m` and
`smul_smul` it gives `(χ(m) * d(m)⁻¹) • μ = μ`. Evaluation on `K₀`, the normalization
`haarMeasure_self`, and the coercion from `NNReal` to `ENNReal` yield
`χ(m) * d(m)⁻¹ = 1`. Since `d(m)` is a unit, `mul_inv_eq_one₀` concludes
`χ(m) = d(m)`.

## Provenance and scope

This is an internal coordinate-transport consequence of the published
refined-radical Haar theorem and the canonical action-compatible continuous
equivalences. It does not reproduce a separate proof from the literature.
The mathematical conventions are those documented in the target statement:
Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), registered source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
section 1.7 (printed pages 443–444) and section 6.3 (printed page 468).
Section 1.7 uses the inverse automorphism in the integrand, so the forward
pushforward has the inverse modulus. Section 6.3 supplies the intersection
triple motivating the actual groups. The arbitrary-permutation formulation
with a supplied full refinement triple is the Library's derived formulation.
The preceding source audit found no applicable project erratum, and a search
of the project's errata notes on 2026-10-29 found none for this source.

This proof supplies the actual unipotent-intersection Haar-character bridge.
It does not construct the relative quotient-integral comparison, prove
normalization cancellation, or prove `PadicParabolicOrbitJacquetComparison`.
