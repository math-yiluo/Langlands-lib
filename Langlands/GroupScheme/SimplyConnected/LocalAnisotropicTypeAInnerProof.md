# Simply connected anisotropic groups of type A over local fields are inner forms

`LocalAnisotropicTypeAInnerProof.lean` proves the published statement
`Langlands.GroupScheme.LocalAnisotropicTypeAInnerStatement` (in
`LocalAnisotropicInnerTypeAStatement.lean`). This is the inner part of Bruhat–Tits 1967,
Proposition 6:

```lean
theorem Langlands.GroupScheme.localAnisotropicTypeAInner :
    LocalAnisotropicTypeAInnerStatement.{u}
```

The statement says the following. Let `K` be a nonarchimedean local field. Let `G` be an
affine group scheme over `K`, locally of finite type, simply connected, absolutely
almost simple and anisotropic. Let `d` be Tits index data for `G` whose Cartan matrix is
`A_n` under some numbering `d.Vertex ≃ Fin n`. Then every `K`-automorphism `σ` of
`SeparableClosure K` fixes every vertex `a` of the index: `d.star σ a = a`. The theorem
proves the statement exactly as published, at every universe `u`. It adds no premise and
puts no condition on the characteristic of `K` or of its residue field.

## Proof

The proof is one term. It composes four published results:

1. `Langlands.GroupScheme.outerTypeAUnitarySplitPresentation` (module
   `OuterTypeAUnitarySplitPresentationProof`) proves
   `OuterTypeAUnitarySplitPresentationStatement`. Let `K` be a field with
   `UnitaryInvolutionSplitting K`. Let `G` be an affine, locally finite-type, simply
   connected, absolutely almost-simple group over `K` whose index has type `A_n` and whose
   star action moves some vertex. Then there are a separable quadratic extension `L/K`, a
   nonsingular Hermitian form `J` on `L^(n+1)` and a presentation
   `HermitianMatrix.SchemeModel.Presentation K L J G` of `G` as the determinant-one
   isometry group of `J`.
2. `Langlands.localUnitaryDivisionCommutative` (module
   `Langlands.Algebra.LocalUnitaryDivisionCommutativeProof`) proves
   `LocalUnitaryDivisionCommutativeStatement`. Over a nonarchimedean local field `K`, a
   finite-dimensional central division algebra over a separable quadratic extension of `K`
   that carries a unitary involution has dimension one over its center.
3. `localOuterTypeAHermitianModel_of_unitarySplitting` (module
   `LocalOuterTypeAHermitianModelAssembly`) turns 1 and 2 into
   `LocalOuterTypeAHermitianModelStatement`. By (2) and
   `Algebra.CentralSimple.unitaryDivisionSplitting`, a nonarchimedean local field `K`
   satisfies `UnitaryInvolutionSplitting K`, so (1) gives a presentation of `G` by a
   Hermitian form `J` on `n + 1` coordinates. A moved vertex forces `2 ≤ n`
   (`two_le_of_star_moves`). The local bridge
   `Presentation.exists_local_rootIso_of_card_eq_succ` then gives an isomorphism of `G`
   with the Hermitian root model `HermitianRoot.SchemeModel.groupScheme K L H w hw`, where
   `H` is a diagonal Hermitian form on `L^(n-1)` with unit weights `w`.
4. `localAnisotropicTypeAInner_of_hermitianModel` (module
   `LocalAnisotropicTypeAInnerReduction`) turns the model statement into the target. Its
   argument is by contradiction. Suppose some `σ` moved a vertex. Then (3) gives an
   isomorphism `e : G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`. Anisotropy of
   `G` makes the composite of the model's split cocharacter with `e.inv` zero, so the
   model's cocharacter is zero. Since `K` is infinite, this contradicts
   `HermitianRoot.SchemeModel.cocharacter_ne_zero`.

The Lean term is

```lean
localAnisotropicTypeAInner_of_hermitianModel
  (localOuterTypeAHermitianModel_of_unitarySplitting
    outerTypeAUnitarySplitPresentation localUnitaryDivisionCommutative)
```

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Excluded inputs

The proof excludes `LocalAnisotropicSimplyConnectedClassificationStatement`,
`LocalRankOneClassificationStatement`, `LocalRankOneTitsIndexStatement`, and any local
Kneser–Tits statement. The theorem has no hypotheses and uses only the three standard
axioms. The modules that prove these statements in the Library are not among the
modules the proof imports, directly or transitively, so the proof cannot depend on them. Some
transitively imported modules import their statement files, but only for shared
definitions.
