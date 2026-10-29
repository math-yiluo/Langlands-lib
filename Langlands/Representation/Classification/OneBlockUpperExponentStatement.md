# Upper exponent bounds of `GL_n` on the single-block product Levi

Worker 978 and Worker 544 state `Langlands.GLOneBlockUpperExponentStatement.{uF, uV}`.
This is a closed proposition definition. It asserts no Lean proof. It is an
algebraic adapter for the sufficiency direction of the `GL_n` exponent
criterion: it moves the ordinary upper Jacquet exponent bounds of a
representation of `GL_n(F)` to the refined exponent hypothesis of the
product-Levi chamber argument, for the single-block Levi.

## Objects and quantifiers

The statement quantifies every prime `p`, every `F : PadicField.{uF} p`, every
supplied realization `T : F.TopologicalData` of its topology, every rank `n`
with a proof `hn : 0 < n`, every complex vector space `V : Type uV` in an
independent universe, and every representation
`π : Representation ℂ (GeneralLinear n F.Carrier) V`. All topologies are the
ones induced by `T` (`T.topology`, and the finite product and unit topologies
built from it).

`V` may be zero. No irreducibility, finite length, finite dimension,
`Nontrivial V`, central character, temperedness, Jacquet-module comparison or
exponent transport is assumed.

## Hypotheses

1. `IsAdmissible π` for the topology of `T`.
2. The ordinary upper exponent bound. This is the right-hand side of
   [`GLTemperedExponentCriterionStatement`](TemperedExponentStatement.md),
   copied literally. For every ordered block shape
   `B : GeneralLinear.BlockShape n`, every
   `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` with `T.IsJacquetExponent B π χ`,
   and every `a : Fin B.length → F.Carrierˣ` with
   `Monotone (fun i => T.normalizedAbs (a i : F.Carrier))`, one has
   `‖(χ a : ℂ)‖ ≤ 1`.

The criterion's central-character hypothesis and its analytic side are not
premises here.

[`T.IsJacquetExponent B π χ`](../Exponents/Jacquet.md) says that `χ` has open
kernel and is a generalized eigencharacter of `T.splitCentreJacquet B π`. That
is the normalized Jacquet module `B.JacquetModule π` of the standard upper block
parabolic `P_B`, with the action `a · [v] = δ_B(a)^(-1/2) [π(a) v]` of the block
scalars `B.blockScalarLevi F.Carrier a`, where `δ_B = T.leviModulus B` and the
square root is the canonical positive one (`T.splitCentreJacquet_mk`).

## Conclusion

Put

```text
C := CuspidalSupport.LeviAdmissibility.oneBlock n hn
e := ScalarLayer.oneBlockLeviEquiv T hn
σ := π.comp e.toMonoidHom
```

Here `C` is the [published block shape](../../Group/GL/OneBlockShape.md) of `n`
with one block of size `n`, and `e` is the
[published topological group isomorphism](TemperedOppositeJacquetScalarLayerAssembly.md)
`C.Levi F.Carrier ≃ₜ* GeneralLinear n F.Carrier`, `g ↦ g ⟨0, _⟩`. No
replacement definition of either is introduced. The conclusion is literally

`ProductLeviChamber.UpperExponentHypothesis T C σ`.

By the published definition
([`ProductLeviChamberBoundProof`](ProductLeviChamberBoundProof.md)), this means
the following. Take any refinement `D : Geometric.BlockRefinement C`, any
character `ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ` with open kernel
that is a generalized eigencharacter of

```text
(T.normalizedRefinedJacquet C D σ).comp
  ((Geometric.flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier))
```

and any `a : Fin (C.flatten D).length → F.Carrierˣ` such that

```text
∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
  T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))
```

Then `‖(ψ a : ℂ)‖ ≤ 1`. The chambers are closed: equal adjacent absolute values
and the central scalar directions are included.

## Provenance (internal, derived)

There is no original-literature source for this statement. It joins two
published interfaces through their actual definitions: the exponent condition
of `GLTemperedExponentCriterionStatement`, whose sources (Silberger 1978 and
1979, Waldspurger 2003) are recorded in its Markdown, and the refined core
hypothesis `ProductLeviChamber.UpperExponentHypothesis`. The published
[Jacquet source map](../../../notes/jacquet/source-map.md) records the upper
inverse-half normalization and the closed monotone chamber that both endpoints
use.

The statement is expected to hold because, for the single-block Levi, the
refined data are the ordinary data written in other coordinates. The
correspondence below is the intended proof content. It is explained here; it is
neither a hypothesis of the Lean statement nor stated or proved in Lean.

Fix a refinement `D` of `C`, let `j₀ := ⟨0, _⟩` be the unique outer index, and
put `B := D j₀`. Since `C.size j₀ = n`, `B` is an ordinary block shape of `n`.

- **Jacquet quotient.** `T.normalizedRefinedJacquet C D σ` acts on
  `Geometric.RefinedJacquetModule C D σ`, the coinvariants of `σ` for
  `Geometric.refinedUnipotent F.Carrier C D`. Membership in that subgroup is
  coordinatewise, so `e` maps it onto `B.unipotentSubgroup F.Carrier` (a
  preimage of `u` is the tuple with the single entry `u`). With that subgroup
  image equality,
  [`Jacquet.coinvariantsMapEquiv`](../CuspidalSupport/GroupTransport.md) and
  [`B.jacquetModuleEquiv π`](../Jacquet/Parabolic.md) give a linear equivalence
  `Q : RefinedJacquetModule C D σ ≃ₗ[ℂ] B.JacquetModule π` with `Q [v] = [v]`.
- **Modulus.** For `m` in the refined Levi, put
  `r(m) := PadicField.TopologicalData.refinedLeviBlock C D j₀ m`, the inner
  coordinate in `B.Levi F.Carrier`. Then `e (m.val)` is
  `B.leviEmbedding F.Carrier (r m)`. By
  [`T.refinedLeviModulus_apply`](../Geometric/RefinementDefinitions.md),
  `T.refinedLeviModulus C D m` is a product over `Fin 1`, so it equals
  `T.leviModulus B (r m)`. Both
  [`T.normalizedRefinedJacquet_mk`](../Geometric/RefinementFunctors.md) and
  `T.normalizedJacquet_mk` multiply the unnormalized action by the inverse of
  the positive square root of this modulus. Hence
  `Q (T.normalizedRefinedJacquet C D σ m x) = T.normalizedJacquet B π (r m) (Q x)`.
- **Block scalars.** `C.flattenBlockEquiv D` is the actual `finSigmaFinEquiv`.
  Put `f : Fin B.length ≃ Fin (C.flatten D).length`,
  `f i := C.flattenBlockEquiv D ⟨j₀, i⟩`; it is surjective because the outer
  index is unique. Let `α b := b ∘ f.symm`, with inverse `α.symm a = a ∘ f`.
  The published `Geometric.flattenedLeviEquiv_blockScalarLevi_apply` and
  `PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv`
  ([`ProductLeviDualOppositeAdapter`](ProductLeviDualOppositeAdapter.md)) show
  that the refined block scalar at `α b` has unique component
  `B.blockScalar F.Carrier b = B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b)`.
  They account for the actual flattened size transports; `C.flatten D` and `B`
  are not assumed definitionally equal.
- **Characters.** Put `χ := ψ.comp α`. Then `χ (α.symm a) = ψ a`. Its kernel
  is the preimage of `ψ.ker` under the continuous coordinate reindexing `α`, so
  it is open.
- **Generalized vectors.** By the two items above, `Q` intertwines the refined
  scalar action at `α b` with `T.splitCentreJacquet B π b`. `Q` is injective, so
  a nonzero generalized vector stays nonzero, and
  `ProductLeviDualOpposite.map_pow_sub_smul` carries each power of the defect
  operator. The same natural power works for all `b`. This gives
  `T.IsJacquetExponent B π χ`, with no generalized-eigenspace decomposition or
  finite-dimensionality argument.
- **Chamber.** Since `C.length = 1`, the blockwise condition has the single
  index `j₀`. It says that `i ↦ T.normalizedAbs (a (f i))` is `Monotone`, which
  is the ordinary chamber condition for `α.symm a`.

The ordinary bound at `B`, `χ` and `α.symm a` then gives
`‖ψ a‖ = ‖χ (α.symm a)‖ ≤ 1`. For `V = 0` there is no nonzero generalized
vector and the conclusion holds vacuously.

The opposite direction is already implemented in
`ProductLeviTemperedFactorization` (`innerCoords`,
`flattenedLeviEquiv_blockScalarLevi_val`, `refinedLeviModulus_blockScalarLevi`,
`exists_refinedJacquet_embedding`, `jacquetExponent_bound_of_core`), and these
lemmas are useful models for the proof.

The admissibility hypothesis is part of the requested interface. The
correspondence above does not use it, because both exponent notions carry their
own open-kernel conditions. A proof may ignore it.

## How it is meant to be used (not claimed)

With a unitary central character of `σ`, the published
`ScalarLayer.tempered_of_upperExponentHypothesis` turns the conclusion into
temperedness modulo the centre on the single-block Levi. The published
`isTemperedModCenter_comp_continuousMulEquiv` transports temperedness along
`e`. Together with this adapter they give the sufficiency direction of
`GLTemperedExponentCriterionStatement`. That assembly is not stated or proved
here.

## Not claimed

- No proof of this statement.
- No analytic estimate, temperedness, square-integrability or Haar-measure
  transport.
- Neither direction of `GLTemperedExponentCriterionStatement`, and no use of it
  as a premise.
- No converse. The necessity direction (core hypothesis to ordinary bounds) is
  `ProductLeviTemperedFactorization.jacquetExponent_bound_of_core`. It is
  neither restated nor used.
- No subgroup-image equality, isomorphism of Jacquet quotients, or general
  transport of generalized exponents along group isomorphisms is stated in
  Lean; these are obligations of the proof.

## Lean dependencies

- `Langlands.Representation.Classification.TemperedExponentStatement`:
  `GLTemperedExponentCriterionStatement`, whose exponent condition is copied,
  and through it `T.IsJacquetExponent`, `IsAdmissible` and `T.normalizedAbs`.
- `Langlands.Representation.Classification.ProductLeviChamberBoundProof`:
  `ProductLeviChamber.UpperExponentHypothesis`, and through its imports
  `CuspidalSupport.LeviAdmissibility.oneBlock`
  (`Langlands.Group.GL.OneBlockShape`), `T.normalizedRefinedJacquet`,
  `Geometric.flattenedLeviEquiv`, `BlockShape.flatten` and
  `BlockShape.flattenBlockEquiv`.
- `Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly`:
  `ScalarLayer.oneBlockLeviEquiv`.

This pair is authored for the pinned Lean 4.34.0 environment and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` (environment artifact
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`).
