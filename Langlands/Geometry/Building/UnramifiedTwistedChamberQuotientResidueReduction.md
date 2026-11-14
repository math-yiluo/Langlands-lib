# Residue quotient for a Frobenius lift implies the chamber quotient input

`UnramifiedTwistedChamberQuotientResidueReductionStatement` is the implication
from `UnramifiedTwistedResidueQuotientStatement` to
`UnramifiedTwistedChamberQuotientStatement`, at arbitrary universe `u`.
`unramifiedTwistedChamberQuotientResidueReduction` proves this implication.

This is an internal assembly result. Both statements use the same host data:
the local field `F`, the connected reductive `G`, the maximal split torus over
`K = inertiaFixedField F`, the building data `D, C, h6, hD`, the finite-level
cocycle `c` and the twisted-fixed point `y`. Neither statement adds a
hypothesis to them. The proof chooses one automorphism `φ` of `K` and proves
the chamber quotient input for this `φ` from the residue quotient data that the
hypothesis supplies for the same `φ`.

## Implemented proof

### The Frobenius lift

`exists_fixedField_arithmeticFrobenius F` (module
`Langlands.Galois.Local.SeparableUnramifiedFrobenius`) supplies an
automorphism `φ` of `K` over `F` with two properties:

1. for every finite intermediate field `E` and every `σ`, some integer power
   satisfies `σ⁻¹ * φ ^ n ∈ E.fixingSubgroup`; this is the density clause of
   the target;
2. on the integers of `K`, `fixedFieldIntegerAut F φ` reduces to the map
   `t ↦ t ^ Nat.card 𝓀[F]` on the residue field; this is the Frobenius-lift
   hypothesis of the residue quotient statement.

The main theorem `unramifiedTwistedChamberQuotient_of_residueQuotient`
introduces the host data and installs the same residue-field instances as both
statements: `Fintype.ofFinite`, `(residueToFixedField F).toAlgebra` and
`fixedFieldResidueIsAlgClosure F`. It applies the hypothesis to this `φ` and
obtains `R`, `P`, `q` and `θP` with the following properties:

- `P` lies in the fixer of `y`, and `q` is surjective;
- `θP` restricts the twist `g ↦ c φ * φ(g) * (c φ)⁻¹`, and `q ∘ θP` is the
  canonical Frobenius descent of `q`;
- `ker q` stabilizes every chamber with a closure presentation through `y`;
- `P` acts transitively on these chambers.

### Transport of a presented chamber

The general theorem `hasChamberClosurePresentation_semilinear` works for any
building datum `B` over `K` with a semilinear apartment datum `A`, any `σ` and
any `c`. Assume the apartment action of `σ`:

- `hroots`: precomposing with it sends affine roots to affine roots;
- `hfacet`, `hclosure`: it sends the facet and the facet closure through `x`
  onto those through its image.

Then, if `Y` has a closure presentation `(g, x₀, x)` through `y` and
`c • σ y = y'`, the image of `Y` under `z ↦ c • σ z` has the closure
presentation `(c * σ(g), σ x₀, σ x)` through `y'`. The proof rewrites
`c • σ(g • apartmentMap w)` as `(c * σ(g)) • apartmentMap (σ w)` with
`action_smul`, `action_apartmentMap` and `mul_smul`. Genericity of `σ x₀`
follows from `hroots`. The facet equation and the closure membership follow
from `hfacet` and `hclosure`.

### Assembly of the finite-field quotient

The general theorem `hasFiniteFieldChamberQuotient_semilinear` uses the same
data and hypotheses, with finite `κ`, algebraic `Ω`, and a point `y` fixed by
`z ↦ c • σ z`. It takes the residue quotient data in exactly the shape the
residue quotient statement provides, with twist `g ↦ c * σ(g) * c⁻¹`, and
concludes `HasFiniteFieldChamberQuotient κ Ω` for this twist and
`z ↦ c • σ z` at `y`. Its proof:

1. chooses a chamber `Y₀` with a closure presentation through `y` by
   `exists_chamberClosurePresentation`;
2. presents its image under `z ↦ c • σ z` through `y` by the previous theorem,
   using that `y` is fixed;
3. obtains `h ∈ P` with `c • σ '' Y₀ = h • Y₀` by transitivity;
4. uses the kernel clause for `Y₀`, and passes the remaining data on unchanged.

### Specialization to the host building

In the section `SemilinearPresentation`, three lemmas specialize the published
Galois facet results to `UnramifiedBuildingDescent.buildingData` and
`UnramifiedBuildingDescent.semilinearData`:

- `semilinearData_affineRoot_comp` comes from
  `KPApartmentData.exists_affineRoot_comp_galoisAction`. That theorem is proved
  in this module from `galoisAffineFunctional`, its surjectivity,
  `galoisAffineFunctional_mem_affineRoots_iff` and
  `galoisAffineFunctional_apply_map`.
- `semilinearData_image_facet` comes from `KPApartmentData.image_facet_galois`.
- `semilinearData_image_facetClosure` comes from
  `KPApartmentData.image_facetClosure_galois`.

By definition, the apartment field of `buildingData` is `D`, so its apartment
and affine roots are those of `D`; the apartment action of `semilinearData`
is `galoisAction`. Each lemma checks this definitional identification in its own declaration with a
raised heartbeat limit, because identifying the base-changed group of `D`
with `baseChanged F K G` unfolds a pullback. The main theorem has a raised
limit for the same reason.

The main theorem applies `hasFiniteFieldChamberQuotient_semilinear` to
`semilinearData`, the residue fields `𝓀[F]` and
`IsLocalRing.ResidueField (fixedFieldIntegers F)`, `σ = φ`,
`c φ`, the three specialized lemmas, the fixed-point equation `hy φ` and the
residue quotient data. With the density clause of `φ`, this is the target
conclusion. The final theorem is the same implication packaged by the
Prop-valued statement.

## Scope

The residue quotient statement is not proved here. Its proof is the
geometric part: the parahoric model, the reductive quotient of its special
fibre, Frobenius compatibility, and the correspondence between chambers and
Borel subgroups. This module does not use any proof of the downstream chamber,
generator-chamber, through-fixed-point or cocycle-vanishing statements.
