# Base change of Čech perfect models for flat separated families

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.FlatPerfectModelBaseChange`.

All schemes, commutative rings and module categories use an arbitrary common
universe `u`. Let `f : X ⟶ Spec R` be flat and separated, `L` an actual line
bundle on `X`, and `𝒰` a finite ordered affine cover of `X`. Suppose `K` is a
strictly perfect integer-indexed complex of `R`-modules and
`v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend embeddingUpNat` is a
quasi-isomorphism. Strict perfectness means boundedness with finite projective
terms, and the Čech complex is the actual alternating cochain complex with its
canonical extension by zero to integer degrees.

`quasiIso_baseChange_cechRepresentative_of_flat φ f L 𝒰 v hK` proves that
ordinary degreewise scalar extension of `v` along any ring homomorphism
`φ : R ⟶ S` remains a quasi-isomorphism. Choose an upper bound `b` for `K`.
The extended Čech complex vanishes above the cardinality of the cover's index
type, so both complexes vanish above the maximum of these bounds. The terms of
`K` are flat because they are projective. The terms of the extended Čech complex
are flat by the imported flat-family line-bundle Čech result. The imported
`quasiIso_baseChange_map_of_flat` therefore applies.

For a Cartesian square with maps `g : Y ⟶ X`, `f' : Y ⟶ Spec S`,
`f`, and `Spec.map φ`, the module proves:

- `quasiIso_cechBaseChangeCochainMap_of_flat hp L 𝒰 v hK`: the actual
  Čech base-change chain map is a quasi-isomorphism.
- `isIso_perfectModelBaseChange_cechDerivedComparison_of_flat hp L 𝒰 v hK`:
  the specified map
  `perfectModelBaseChange hp L hK (Q.map v ≫ cechDerivedComparison f 𝒰 L.obj)`
  is invertible.
- `cechPerfectModelBaseChangeIso_of_flat hp L 𝒰 v hK`: the resulting
  isomorphism from `Q` of the scalar extension of `K` to the actual derived
  relative global sections of the pulled-back line bundle on `Y`.
- `cechPerfectModelBaseChangeIso_of_flat_hom`: the forward map of this
  isomorphism is exactly the specified `perfectModelBaseChange`.

The first two geometric results apply the imported detection criteria to the
scalar-extension quasi-isomorphism just proved. The isomorphism constructor
uses the imported constructor with that hypothesis, and the forward-map
identity follows by definition. Thus the map is the existing scalar adjunct
applied to the named source Čech comparison.

This is internal infrastructure derived from the imported algebraic
scalar-preservation theorem and the existing actual geometric Čech
comparisons. There is no flatness assumption on the change of base, and no
properness or noetherian hypothesis. The module assumes a strictly perfect
representative and its quasi-isomorphism `v`; it does not construct them or
assert any further compatibility with open restriction. It does not prove
relative cube detection.
