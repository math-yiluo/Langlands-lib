# Target cosets for actual CM moduli and scheme transitions

This module proves that two genuine transporter arrows with the same target
right coset induce the same actual CM moduli transition. It constructs the
resulting map on the quotient of transporter arrows, valued in actual scheme
morphisms, conditional on the existing exact representability target. It also
proves that an element of the level subgroup induces the identity scheme map.
The latter is a calculation on the actual frame orbits, propagated through the
moduli construction; it is not inferred from the transporter functor laws alone.

## Transporters and their target cosets

For compact-open levels `U` and `V` in a topological group `G`, an existing
transporter `f : U ⟶ V` retains its element and the condition
`f.element⁻¹ * U * f.element ≤ V`. The relation
`CompactOpenLevel.targetCosetSetoid U V` is

```
f ~ g  iff  f.element⁻¹ * g.element ∈ V.subgroup.
```

Thus it compares the right cosets of the **target** subgroup. Reflexivity,
symmetry and transitivity follow from the subgroup laws and the group identities.
`TargetCosetArrow U V` is the quotient of this actual transporter set. No
quotient category or composition of these quotient arrows is defined here.

`RightOrbit.translate_eq_of_target_coset` proves the central equality on the
existing right-orbit quotient. For a representative `x`, the orbit of `x * f`
is the orbit of `x * g`: the required target-subgroup witness is `f⁻¹ * g`, and
`(x * f) * (f⁻¹ * g) = x * g` follows from the right action laws. Quotient
induction extends this calculation to every source orbit. The corresponding
`InvariantOrbit` equality follows by subtype extensionality. Monodromy
invariance is retained by the existing translation maps.

## Actual polarized and Harris classes

`PolarizedWeilLevel.levelTower_map_eq_of_target_coset` installs the actual
right action on the Weil-compatible adelic frame type. It applies the orbit
calculation to each polarized action object and each actual level structure.
`PolarizedWeilLevel.isoClassTower_map_eq_of_target_coset` descends that equality
through the existing rational-isogeny quotient by quotient induction.

`HarrisNumericalWeilLevel.isoClassTower_map_eq_of_target_coset` retains the
original Harris opposite-group convention. It transports the coset-membership
hypothesis through the existing continuous group equivalence with scalar-linear
similitudes, using preservation of inverse and multiplication and
`hodgeLevelFunctor_obj_mem`. It then applies the polarized-class equality and
uses extensionality of the determinant and numerical subtypes. It makes no new
assumption that dimension is invariant under arbitrary rational isogenies.

The generic polarized result retains the explicit tensor comparison,
composition, unit and associativity coherence, unitor comparison, symmetry,
Picard-zero stability, Mumford-square and universal-base-change hypotheses. It
also retains the actual dual and evaluation data already carried by each
polarized object, the relative finite Weil-transition and adelic-comparison
hypotheses, torsion finite etaleness, invertibility of all torsion indices,
finiteness and etaleness of roots of unity, quasi-separatedness, the chosen
geometric point with finite fibers, and pair additivity. The Harris result uses
the existing arithmetic datum, signature charts, CM section, reflex structure,
positive pair additivity and original numerical and determinant conditions.

## Geometric families and the exact moduli presheaf

In namespace `HarrisTaylorCMWeilLevel`, the following equalities propagate the
same calculation through the existing actual constructions:

- `geometricClassTower_map_eq_of_target_coset` specializes the numerical result
  at every actual geometric point, retaining that point's algebraically closed
  field. Its finite-fiber property is the existing proved property.
- `compatibleGeometricFamilyTower_map_eq_of_target_coset` applies the pointwise
  equality and uses function and subtype extensionality. The family construction
  retains connectedness and local Noetherianity.
- `unpointedClassTower_map_eq_of_target_coset` uses the named geometric
  prerequisites of the actual connected admissible CM base.
- `disconnectedClassTower_map_eq_of_target_coset` applies that equality on each
  actual connected open component, including the empty-product case.
- `smallLevelClassPresheafTower_map_eq_of_target_coset` gives equality of natural
  transformations on the exact category of componentwise admissible schemes
  over the original CM field `F`, restricted to the original sufficiently small
  levels. It retains the named duality-naturality and polarization-base-change
  hypotheses of the presheaf construction.

`smallCMTargetCosetSetoid` is the inverse image of the generic target-coset
setoid along the underlying transporter of a full-subcategory arrow.
`SmallCMTargetCosetArrow` is its actual quotient. The full subcategory retains
all underlying transporter elements and their inclusion conditions.

## Actual scheme maps

A family `R` has exactly the existing type `CMLevelRepresentation` at each
small level. Its bases belong to the exact componentwise admissible test
category. Each representation includes smoothness, projectivity via an actual
projective-space immersion, and a natural isomorphism from lifted Yoneda to the
fixed moduli presheaf. The already constructed `representedCMBaseTower` obtains
all transitions by fully faithful Yoneda preimage; the new construction supplies
no arbitrary scheme transitions.

`representedCMBaseTower_map_eq_of_target_coset` rewrites the proved equality of
moduli natural transformations inside this preimage formula.
`representedCMSchemeTower_map_eq_of_target_coset` forgets to the underlying
actual scheme maps. The definition `representedCMTargetCosetMap` uses this
proved equality as the well-definedness proof for a quotient lift. Its `_mk`
equation recovers the existing actual scheme transition of any representative;
therefore its interpretation on actual test-scheme classes is precisely the
existing `representedCMBaseTower_map_classes` equation for that representative.
Its `_over` equation proves that every quotient-induced map commutes with the
structure maps to `Spec F`.

`representedCMSchemeTower_map_eq_id_of_mem` compares an endomorphism whose
element belongs to the level subgroup with the identity transporter. Their
inverse-product belongs to that subgroup, so the actual orbit-derived equality
identifies their maps; only then is the functor's identity law applied.
`representedCMTargetCosetMap_id` records the identity transporter class.
`representedCMTargetCosetMap_comparison` proves the square with the existing
canonical comparison of any two exact representing choices, by quotient
induction and the comparison's naturality. Those comparisons come from the
identity of the same moduli presheaves.

`cmTargetCosetMap` specializes this construction to witnesses chosen from a
proof of exactly `CMRepresentabilityStatement`, with all its original named
prerequisites. It returns morphisms between the corresponding existing
`cmSchemeTower` objects. It supplies no proof of that existence proposition.

## Source and scope

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed p.91, one-based PDF p.99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The original passage uses monodromy-invariant level orbits and gives right
translation by composition of a frame with a transporter element. The present
coset equality and quotient lift are derived from that orbit convention and the
existing Lean construction; the source does not name these internal interfaces.

The original passage also asserts representability and finite-etale Galois
covers under its running arithmetic hypotheses. This module proves neither
representability nor that geometric assertion. Exact existence, the applicable
division/global hypotheses, comparison with the original moduli problem and
admissibility of representers remain separate obligations. It does not prove
faithfulness, transitivity or freeness of a quotient-group action, finite
etaleness or a torsor/cover property, a canonical-model theorem, uniformization,
or coefficient descent. A normal-level quotient-group scheme action is not yet
constructed by this module; the actual identity calculation here is its kernel
prerequisite. The restricted test category is retained throughout.
