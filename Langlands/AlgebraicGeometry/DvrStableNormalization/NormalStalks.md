# Normal stalks of flat DVR schemes with smooth generic fibre and reduced special fibre

Worker 6.

- `genericFibre Z`: the generic fibre scheme `pullback Z.hom (Spec.algebraMap R (FractionRing R))`.
- `stalk_normal_of_generic`: if the generic fibre is smooth over `FractionRing R`, the stalks of `Z`
  at its points are integrally closed domains: they are regular local
  (`AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`), hence domains and UFDs
  (`IsRegularLocalRing.isDomain`, `Langlands.CommutativeAlgebra.regularLocalFactorial`).
- `hasNormalStalks_of_reduced_quotient`: if `P` is flat and locally of finite type with smooth
  generic fibre, and `Γ(U) ⧸ π Γ(U)` is reduced for every affine open `U`, then `P` has normal
  stalks (criterion E2 of `FlatDvrNormality` on affine opens).
- `isReduced_quotient_of_isPushout`: a ring-level lemma: if `D` is a reduced pushout of `C ← A → K`
  in which `π = a(s)` maps to zero in `K`, and the quotient `C → C ⧸ π C` extends to a cocone, then
  `C ⧸ π C` is reduced.
- `isReduced_quotient_of_geometricallyReduced`: if `P → Spec R` is geometrically reduced, then
  `Γ(U) ⧸ π Γ(U)` is reduced for affine `U`; the sections of the special fibre over `U` form the
  pushout (`isIso_pushoutSection_of_isAffineOpen`).
- `hasNormalStalks_of_flat_of_geometricallyReduced`: flat, locally of finite type, geometrically
  reduced, smooth generic fibre ⇒ normal stalks.

This is the normality criterion recalled in Conrad's Remark A.3 (p.28): a flat finite-type scheme
over a DVR with normal generic fibre and reduced special fibre is normal.
