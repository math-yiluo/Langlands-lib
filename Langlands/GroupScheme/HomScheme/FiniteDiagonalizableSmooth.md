# Smoothness of homomorphisms out of a finite power of roots of unity

Module `Langlands.GroupScheme.HomScheme.FiniteDiagonalizableSmooth`, namespaces
`Langlands.GroupScheme.HomScheme` and `Langlands.GroupScheme.HomScheme.FiniteDiagonalizable`.

## Statement and provenance

Let `G` be a smooth affine group scheme over `Spec R`, `I` a finite type and `m > 0`. The main
theorem `smooth_of_isUniversal_muPower` concerns any universal family
`i : RelativeHom (μ_m^I) G Y` in the sense of `IsUniversal` (`Langlands.GroupScheme.HomScheme`,
module `Universal`), where `μ_m^I` is `pi fun _ : I => (mu (Spec R) m).toGrp`. For such a family,
`Y.hom : Y.left → Spec R` is smooth. Such a family exists by `exists_isUniversal_muPower`.

This is the smoothness part of SGA 3, Exp. XI, Cor. 4.2 (`Hom_{S-gr}(H, G)` is representable,
smooth and separated over `S` for `G` smooth affine and `H` of multiplicative type and of finite
type), in the case `H = μ_m^I` and `S = Spec R`. SGA 3 obtains formal smoothness from Exp. XI,
Prop. 2.1. Here the algebraic input is `Langlands.Algebra.DiagonalizableHomSmooth`, which proves
it by a fixed-point argument internal to this project. The geometric transfer in this file is also
internal. The file is infrastructure for the torus case of SGA 3, Exp. XI, 4.1, which is the task
"Prove smooth moduli of actual closed torus subgroups".

## Uniqueness of universal families (`section Uniqueness`)

- `IsUniversal.iso hi hj : M ≅ N` takes two universal families `i : RelativeHom H G M` and
  `j : RelativeHom H G N`, for arbitrary group schemes `H`, `G` over a scheme `S`. The forward map
  is the unique `a : M ⟶ N` with `evaluate a j = i`, and the inverse is the unique `b` with
  `evaluate b i = j`. Both composites are identities by `evaluate_comp`, `evaluate_id` and
  injectivity of evaluation of a universal family.
- `IsUniversal.smooth_hom hi hj`: if `N.hom` is smooth, then `M.hom` is smooth, since
  `M.hom = (hi.iso hj).hom.left ≫ N.hom` and isomorphisms are smooth.

## Coordinates (`section Coordinates`)

- `smooth_hopfAlgebra G`: if `G` is affine and `G.X.hom` is smooth, then the coordinate Hopf
  algebra `AffineCoordinates.hopfAlgebra G` is a smooth `R`-algebra. The proof transports
  smoothness along `coordinateIso G : hopfGroup R (hopfAlgebra G) ≅ G` and translates it with
  `HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap`. It follows the pattern of
  `finitePresentation_hopfAlgebra`.
- An instance derives `Algebra.FormallySmooth R (AffineCoordinates.hopfAlgebra G)` from this.

## The universal family (`section Universal`)

Here `I` is a `Fintype`, `m` is nonzero and `G` is affine with `G.X.hom` smooth.

- `smooth_homAlgebra`: `homAlgebra R I m G`, which is
  `HomAlgebra R (hopfAlgebra G) R[I → ZMod m]`, is a smooth `R`-algebra. Instance search finds this
  from `Langlands.FiniteBialgebraHom.smooth_homAlgebra` and the instance above.
- `smooth_specOver_homAlgebra`: the structure morphism of `specOver R (homAlgebra R I m G)`, the
  base of `universalHom R I m G`, is smooth (`HasRingHomProperty.Spec_iff`).

## Main theorem

- `smooth_of_isUniversal_muPower R I hm G hi`. The hypotheses are `[Finite I]`, `0 < m`,
  `[IsAffineHom G.X.hom]`, `[Smooth G.X.hom]` and a universal family `i` over `Y` with
  `hi : IsUniversal i`. The conclusion is `Smooth Y.hom`. The proof compares `i` with the universal
  family `universalHom R I m G` (`isUniversal_universalHom`) by `IsUniversal.smooth_hom`.
