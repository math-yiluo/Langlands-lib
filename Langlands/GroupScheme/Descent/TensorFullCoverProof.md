# Full simply connected cover descent from an explicit finite tensor decomposition

This module proves the public proposition
`Langlands.GroupScheme.SimplyConnectedCoverTensorDescentStatement.{u,v}`
(module `Langlands.GroupScheme.Descent.TensorFullCoverStatement`) as the
theorem `Langlands.GroupScheme.simplyConnectedCoverTensorDescent`. Both
universes stay arbitrary: the fields `k, L` live in `Type u` and the finite
index type `J` lives in `Type v`. The theorem has no hypotheses beyond those
of the statement.

## Statement proved

Let `k, L` be fields with `Algebra k L`, `J` a finite type,
`e : L ⊗[k] L ≃ₐ[L] (J → L)` an `L`-algebra equivalence and
`s : J → (L ≃ₐ[k] L)` automorphisms with `e (a ⊗ b) i = a * s i b`. Let `G`
be a group scheme over `k`, `C` a group scheme over `L`, and
`π : C ⟶ G_L` a simply connected cover (`IsSimplyConnectedCover π`), where
`G_L` is the base change along `Spec L → Spec k`. Then there are a group
scheme `D` over `k`, an arrow `a : D ⟶ G` and an isomorphism `j : D_L ≅ C`
such that `IsSimplyConnectedCover a` holds and `a_L = j.hom ≫ π`.

`IsSimplyConnectedCover a` has four fields: `G` is semisimple, `D` is simply
connected, `a` is a central isogeny, and `a` has the central-cover universal
property (`HasCentralCoverUniversalProperty`).

## Proof

All results used are public in the Library.

1. **Algebraicity.** `isAlgebraic_of_tensorDecomposition e`
   (`Descent.TensorFiniteness`) shows that `L` is algebraic over `k`. That
   lemma derives it from finite-dimensionality
   (`finiteDimensional_of_tensorDecomposition`, faithfully flat descent of
   finiteness).
2. **Descended source and arrow.** `Descent.TensorCoverDescent` builds the
   descended data from `hπ : IsSimplyConnectedCover π`:
   - `S := hπ.tensorDescentSolution e s he`, an object `S.obj` over `k` with
     `S.iso : S.obj_L ≅ C`;
   - `a := hπ.tensorDescentCentralIsogeny e s he`, an arrow
     `a.val : S.obj ⟶ G` together with the proof `a.property` that it is a
     central isogeny;
   - the recovery equation `hrec : a.val_L = S.iso.hom ≫ π`
     (`baseChange_tensorDescentCentralIsogeny`).

   The witnesses are `D := S.obj`, `a := a.val`, `j := S.iso`, and the
   recovery equation is `hrec`.
3. **`G` is semisimple.** `hπ.isSemisimple` says `G_L` is semisimple. The
   field-extension reflection `IsSemisimple.of_fieldExtension`
   (`Reductive.SemisimpleFieldReflectionProof`) gives that `G` is semisimple.
4. **`D` is simply connected.** `hπ.isSimplyConnected` says `C` is simply
   connected; `IsSimplyConnected.of_iso S.iso` (`SimplyConnected.Basic`)
   moves this to `S.obj_L`. The algebraic-extension reflection theorem
   `simplyConnectedAlgebraicExtensionReflection`
   (`SimplyConnected.AlgebraicExtensionReflection`), which is a proof of
   `SimplyConnectedAlgebraicExtensionReflectionStatement`, then shows that
   `S.obj` is simply connected. It needs the algebraicity from step 1.
5. **Central isogeny.** This is `a.property`.
6. **Universal property.** By `hrec`, the base change of `a.val` equals
   `S.iso.hom ≫ π`. This composite has the universal property by
   `HasCentralCoverUniversalProperty.iso_comp`
   (`SimplyConnected.CoverComparison`) applied to `hπ.universal`. The
   tensor-decomposition reflection theorem
   `centralCoverUniversalPropertyTensorReflection`
   (`SimplyConnected.FieldComponentUniversalReflection`), which is a proof of
   `CentralCoverUniversalPropertyTensorReflectionStatement`, carries the
   property from `a.val_L` down to `a.val`. That statement takes an index
   type in `Type`, so the decomposition is reindexed to
   `Fin (Fintype.card J)`: the equivalence becomes `finiteTensorEquiv e`
   (`Descent.TensorCoverDatum`, defined by
   `finiteTensorEquiv e x i = e x ((Fintype.equivFin J).symm i)`), the
   automorphisms become `fun i => s ((Fintype.equivFin J).symm i)`, and the
   pure-tensor formula follows from `he` by `simpa`.

## Dependencies

Two of the main ingredients are independently published proofs of separate
tasks:

- `simplyConnectedAlgebraicExtensionReflection`, task `833bd8bd` (proof
  artifact `2ae9d53c`);
- `centralCoverUniversalPropertyTensorReflection`, task `9c74795e` (proof
  artifact `a6a39aaa`).

The descent construction itself comes from the public
`Descent.TensorCoverDescent` module, and semisimplicity reflection comes from
`Reductive.SemisimpleFieldReflectionProof`. This module adds no separate
finiteness, separability, Galois, effective-descent or universal-property
premise.

## Attribution

The assembly (reindexing by `finiteTensorEquiv` and transport by `iso_comp`)
follows Worker 416's unpublished prototype. The code here uses only public
Library declarations.
