# The theorem of the square for Picard-zero families

Module `Langlands.AlgebraicGeometry.Picard.SquareTheorem` is a helper module
for the proof of `Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`.
It proves the Picard-zero form of the theorem of the square for a rigidified family on
`T ×_S B`, where `B/S` is an abelian scheme with `HasDualScheme B` and
`T : Over S` is arbitrary. The result is an isomorphism of underlying line
bundles, and it is conditional. Both theorems take explicit proofs of four
Library propositions as arguments: `pullbackTensorComparisonIsIsoStatement`
(`preservation`), `PicardZeroLineBundleClassificationStatement`
(`classification`), `PicardZeroPullbackStatement` (`stability`) and
`Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions`
(`globalFunctions`). This module proves none of them. Each is proved elsewhere
in the Library, as `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`,
`picardZeroLineBundleClassification`, `picardZeroPullback` and
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`, so a caller
can supply them. Everything is in the namespace `Langlands.AbelianScheme`.

## Statements

* `nonempty_shearBundle_iso preservation classification stability globalFunctions B hB L hL`:
  for a rigidified family `L` on `T ×_S B` with `IsPicardZeroFamily B L`,
  there is an isomorphism of line bundles on `(T ×_S B) ×_S B`

  `shearBundle B L ≅ q^* L ⊗ pr^* L`,

  where `L` stands for its underlying bundle,
  `shearBundle B L` is the pullback along `(t, b, b') ↦ (t, b * b')`,
  `q = (relativeSpace B.X.hom).map (relativeFst B T)` is
  `(t, b, b') ↦ (t, b')`, and `pr = (relativeProjection B.X.hom).app _` is
  `(t, b, b') ↦ (t, b)`. The tensor product is `LineBundle.tensor preservation`.
* `pairOver B z x : Z ⟶ relativeOver B T` is the point `(z, x)` of
  `T ×_S B` determined by `z : Z ⟶ T` and `x : Z ⟶ B.X` in `Over S`.
  `pairOver_left`, `pairOver_fst` and `pairOver_snd` describe it. The lemmas
  `pairOver_shear`, `pairOver_relativeFst` and `pairOver_relativeProjection`
  compute the composites of `((z, x), y)` with the three maps above: they give
  `(z, x * y)`, `(z, y)` and `(z, x)`.
* `nonempty_pullback_pairOver_mul_iso preservation classification stability globalFunctions B hB L hL z x y`:
  for points `z : Z ⟶ T` and `x y : Z ⟶ B.X`, there is an isomorphism of line
  bundles on `Z`

  `(z, x * y)^* L ≅ (z, x)^* L ⊗ (z, y)^* L`.

## Proof

For the first theorem, `exists_shearBundle_iso` (module `ShearClassification`)
gives `φ` with `shearBundle B L ≅ P_φ ⊗ pr^* L`, and
`eq_relativeFst_unitPoint_comp` gives `φ = relativeFst ≫ unitPoint ≫ φ`.
Hence `P_φ` is the pullback along `q` of `P_{unitPoint ≫ φ}`
(`poincarePullbackComp`), and that bundle is `L` by `unitPointIso`.

The second theorem pulls the first back along `((z, x), y)`. It uses
`LineBundle.pullbackTensorObjIso`, the three `pairOver` composites and the
symmetry `LineBundle.tensorCommIso`.

## Provenance

The module name follows the classical theorem of the square. The content
proved here is the Picard-zero form `m^* L ≅ p_1^* L ⊗ p_2^* L`, stated for a
family over `T` rigidified along the unit section, with no inverse bundles. The
Lean proof is the classification-and-rigidity argument
described above, not the theorem-of-the-cube proof in the literature. The
point form is a rigidified, arbitrary-base analogue of Edixhoven, van der Geer
and Moonen, *Abelian Varieties* (registered
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed page = PDF
page − 4), Lemma (7.16)(i), printed p.104 (PDF p.108). Over a field, for `L`
on `X_T` with `ϕ_L = 0`, that lemma states `[(f + g)^* L] = [f^* L ⊗ g^* L]`
in `Pic_{Y/T}(T)`.
