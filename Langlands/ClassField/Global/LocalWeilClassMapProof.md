# Existence of local Weil class maps at completions

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`.

This module proves the published proposition
`Langlands.ClassField.Global.LocalWeilClassMapExistenceStatement.{u}`
(module `Langlands.ClassField.Global.LocalWeilClassMapStatement`) as the theorem
`Langlands.ClassField.Global.localWeilClassMapExistence`, with no hypotheses.

The proof has two steps.

1. `localWeilClassMapExistence_of_weilReciprocity` derives the statement from the published
   proposition `Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{u}`
   (module `Langlands.ClassFieldTheory.Local.WeilReciprocityStatement`). Only its existence
   half is used: geometric Weil reciprocity candidates for every `p`-adic field.
2. `localWeilClassMapExistence` applies this to the published theorem
   `Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness`
   (module `Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof`).

The local statement is the Weil–Shafarevich theorem in Tate, *Number theoretic
background* (1979), §1.2, printed p.5 (PDF p.14). The Weil group `W_{E/F} = W_F/W_E^c`
is an extension of `Gal(E/F)` by `Eˣ` whose class `α_{E/F}` is the fundamental class.
Equivalently, `W_F` maps to the extension attached to a fundamental class, compatibly
with the Galois projection and with reciprocity on `W_E`.

## `Langlands.Weil.Local.FiniteGaloisTower.exists_weilClassMap`

Data: `hW : WeilReciprocityExistenceUniqueness.{u}`; `p`-adic fields `F, E` with
`f : F →ₐ[ℚ_p] E`; an instance `inst : Algebra F E` with `inst = extensionAlgebra F E f`,
`FiniteDimensional F E` and `IsGalois F E`; a topology `τ` on `E` with
`τ = E.canonicalTopologicalData.topology`; an invariant family `J` with
`RelativeClassFormation` and `ArithmeticNormalization`; a candidate `e` for `E`
satisfying `GeometricWeilReciprocityRelation`; and a normalized cocycle
`z : NormalizedTwoCocycle Gal(E/F) Eˣ` whose class is fundamental for `J.relative F E`.

Conclusion: there is a continuous homomorphism `κ : W_F →ₜ* z.Extension` such that

- for `g ∈ W_F` and `x ∈ E`, the image of `κ g` in `Gal(E/F)` acts on `x` as
  `localProjection F g` does, through `extensionFieldEmbedding F E f : E → \bar F`;
- for `y ∈ W_E`, `κ (extensionWeilMap F E f y) = (inl (reciprocityUnits E e y))⁻¹`.

The algebra structure and the topology are taken as arbitrary instances equal to the
given ones, so that the theorem applies to completions, whose own instances are equal but
not syntactically the same.

Proof. Substitute `inst` and `τ`. Then take `κ = weilClassMap F E f hW hgal J hJ hA e he z hz`
from the published module `Langlands.Weil.Local.FiniteGaloisFundamental`. The two
properties are its lemmas `weilClassMap_projection_apply` and
`weilClassMap_extensionWeilMap`.

For the reader, this is how that module builds `weilClassMap`.
`finiteGaloisClass_isFundamental` shows that the class of the Library's Weil pushout
cocycle `finiteGaloisCocycle` is fundamental; this is where `hW` is used. Fundamental
classes are unique, because `J.relative F E` is injective (the `RelativeImages` component
of `RelativeClassFormation`). So this class equals the class of `z`. Let `ψ` be the
continuous equivalence of extensions `NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq`
(Worker 1556), which is the identity on `Eˣ` and on `Gal(E/F)`. Then
`weilClassMap = ψ ∘ finiteGaloisPushout`. Its two properties follow from
`finiteGaloisPushout_projection_apply` and `finiteGaloisPushout_extensionWeilMap`
(`Langlands.Weil.Local.FiniteGaloisPushout`), since `ψ` preserves projections and unit
inclusions.

## `Langlands.ClassField.Global.towerPadicField_topology_eq`

For a finite place `w` of `E` above `v`, the completion topology of `E_w` equals
`(towerPadicField v w).canonicalTopologicalData.topology`. Proof: `towerPadicField v w`
is `padicFieldAt w h` with `h : residuePrime w = residuePrime v`. After generalizing the
prime and substituting `h`, this is the Library's `completion_topology_eq w`.

## `Langlands.ClassField.Global.localWeilClassMapExistence_of_weilReciprocity`

`WeilReciprocityExistenceUniqueness.{u} → LocalWeilClassMapExistenceStatement.{u}`.

Proof. Introduce the data of the statement. Apply `exists_weilClassMap` with:

- `F = padicField v`, `E = towerPadicField v w`, `f = completionPadicAlgHom v w`;
- the completion algebra `F_v → E_w`, equal to `extensionAlgebra` by
  `Algebra.algebra_ext`, since `completionPadicAlgHom` is the completion map;
- the finiteness instance `FiniteExtension.local_finite` of the statement;
- the completion topology, by `towerPadicField_topology_eq`;
- the cocycle `CompletionClassExtension.representative v w a`, whose class is `a` by
  `cohomologyClass_representative`.

The conclusions are those of the statement: `completionClosureEmbedding v w` is by
definition `extensionFieldEmbedding` for `completionPadicAlgHom v w`;
`completionWeilMap v w` is `extensionWeilMap`; and the projection and inclusion of
`CompletionClassExtension v w a` are those of the representative's extension.

## `Langlands.ClassField.Global.localWeilClassMapExistence`

`LocalWeilClassMapExistenceStatement.{u}`.

Proof. Apply `localWeilClassMapExistence_of_weilReciprocity` to
`LocalClassField.geometricWeilReciprocityExistenceUniqueness`, which proves
`WeilReciprocityExistenceUniqueness.{u}` unconditionally.

## Provenance

`exists_weilClassMap` is the local Weil–Shafarevich theorem as stated in Tate (1979),
§1.2, printed p.5, for the Library's actual local Weil groups. Its proof is internal,
assembled from the cited and derived results above. The reduction theorem, the topology
lemma and the final theorem are internal.
