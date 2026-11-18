# Ring-level hypotheses for affine schemes over a DVR

Worker 6.

- `globalAlgebraMap Z`: the ring map `R → Γ(Z, ⊤)` induced by `Z.hom` (through `ΓSpecIso`).
- `flat_globalAlgebraMap`, `finiteType_globalAlgebraMap`: for affine `Z`, flatness and local finite
  type of `Z.hom` give flatness and finite type of `globalAlgebraMap Z`.
- `smooth_globalAlgebraMap`: for affine `Z` with smooth generic fibre,
  `FractionRing R ⊗[R] Γ(Z, ⊤)` is smooth over `FractionRing R`. Both this tensor product and the
  sections of the generic fibre are localizations of `Γ(Z, ⊤)` away from the uniformizer
  (`IsLocalization.Away.tensorRight`, `isLocalization_genericι_app`). The resulting isomorphism is
  `FractionRing R`-linear because ring maps out of the fraction field are determined on `R`.

These are exactly the three hypotheses of `DvrAffineReducedFibreStatement` for `A = Γ(Z, ⊤)`.
