# Tensoring with an endomorphism of the structure sheaf

Internal helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement`.

## `tensorMap_id_unitEnd`

For a module `G` on a scheme `Y` and an endomorphism `φ` of the structure sheaf,

`tensorMap (𝟙 G) φ ≫ (tensorRightUnitor G).hom =
  (tensorRightUnitor G).hom ≫ (unitEndCoefficient φ ⊤ • 𝟙 G)`,

where `unitEndCoefficient φ ⊤ = φ(1)` is the global function by which `φ` multiplies
and `r • 𝟙 G` is the Library's multiplication of a morphism by a global function
(`Langlands.Scheme.Modules.globalHomSMul`). So `𝟙 ⊗ φ` on `G ⊗ 𝒪_Y` becomes
multiplication by `φ(1)` on `G`.

## Proof

On presheaves the identity is checked on pure tensors `g ⊗ a` over each open `U`:
`φ(a) • g = (a · φ(1)|_U) • g = φ(1)|_U • (a • g)`, using `unitEndCoefficient_app`,
`unitEndCoefficient_res` and commutativity of the scalar action. The sheaf statement
follows by applying sheafification and the naturality of the comparison
`sheafifyForgetIso`, as in the Library proof of `tensorRightUnitor_naturality`.

## Provenance

Derived for this proof; a standard fact about the unitor.
