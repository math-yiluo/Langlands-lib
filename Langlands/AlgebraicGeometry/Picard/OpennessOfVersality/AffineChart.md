# Affine charts through finite-type field points

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.AffineChart`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction; no literature
statement is formalized.

## Algebra

`exists_surjective_away`: let `χ : A →+* K` be a ring map to a field which is of finite
type (`RingHom.FiniteType`) and surjective on stalks (`RingHom.SurjectiveOnStalks`). Then
there is `b : A` with `χ b ≠ 0` such that every `t : K` satisfies `χ x = t * χ b ^ n` for
some `x : A` and `n : ℕ` (so `A[1/b] → K` is surjective). Proof: surjectivity on the
stalk at the zero ideal writes every generator `s` of `K` over `A` as `χ x_s / χ r_s`; let
`b` be the product of the denominators; the elements `t` of the stated form form an
`A`-subalgebra containing the generators.

## Charts

- `exists_affineOpen_chart`: for `T : Over (Spec R)` and an affine open `W` of `T.left`,
  there are an `R`-algebra structure on `Γ(T.left, W)` and a chart
  `ι : affineBase R Γ(T.left, W) ⟶ T` with `ι.left = hW.fromSpec` (the algebra structure
  is `Spec.preimage (hW.fromSpec ≫ T.hom)`).
- `exists_affineChart`: let `T : Over (Spec R)` be locally of finite type and
  `p : residueBase R K ⟶ T` a field point whose underlying morphism is surjective on
  stalks and locally of finite type. Then there are an `R`-algebra `A` of finite type, a
  chart `ι : affineBase R A ⟶ T` whose underlying morphism is an open immersion, and a
  surjective `χ : A →ₐ[R] K` with `affineBaseMap χ ≫ ι = p`.

  Proof: take an affine open `W` containing the image point, the chart of
  `exists_affineOpen_chart`, and write the lifted point (`pointLift`, Library
  `FiniteTypePointSmoothChartReduction`) as `affineBaseMap χ₁` (`exists_affineBaseMap_eq`).
  `Spec.map χ₁` is surjective on stalks and locally of finite type (cancellation from
  `p`), hence so is `χ₁` (`HasRingHomProperty.Spec_iff`). Choose `b` by
  `exists_surjective_away` and replace the chart by `A = Localization.Away b`, whose
  spectrum is an open immersion into `Spec Γ(W)`; the lift `χ : A → K`
  (`IsLocalization.liftAlgHom`) is surjective, and `A` is of finite type over `R`.
