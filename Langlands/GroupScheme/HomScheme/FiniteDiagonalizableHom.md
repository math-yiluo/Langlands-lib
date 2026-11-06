# Homomorphisms out of a finite power of roots of unity

Module `Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom`, namespace
`Langlands.GroupScheme.HomScheme.FiniteDiagonalizable`.

## Main result

`exists_isUniversal_muPower R I hm G` has the following hypotheses:

- `R : Type u` is a commutative ring and `I : Type u` is a finite type;
- `m : ℕ` with `hm : 0 < m`;
- `G` is a group scheme over `Spec R` with `IsAffineHom G.X.hom` and
  `LocallyOfFinitePresentation G.X.hom`.

It concludes that there exist `Y : Over (Spec R)` and
`i : RelativeHom (pi fun _ : I => (mu (Spec R) m).toGrp) G Y` with three properties:

- `IsUniversal i`: for every scheme `T` over `Spec R`, maps `T ⟶ Y` correspond, by evaluating `i`,
  to actual group-scheme homomorphisms `(μ_m^I)_T ⟶ G_T`;
- `IsAffine Y.left`;
- `LocallyOfFinitePresentation Y.hom`.

So the functor of homomorphisms `μ_m^I → G` is represented by an affine scheme locally of finite
presentation over `Spec R`. The source is the actual finite product, over `I`, of the Library group
schemes `mu (Spec R) m` of `m`-th roots of unity.

## Provenance

The theorem is a special case of SGA 3, Exp. XI, Proposition 3.12(b) (Expo11.pdf, one-based PDF
pp.17-19, printed pp.101-103, original pp.153-156). That proposition takes an affine group `G`
over a scheme `S` and a finite group `H` of multiplicative type over `S`. It says that
`Hom_{S-gr}(H, G)` is representable and affine over `S`, and of finite presentation over `S` if
`G` is. Here `S = Spec R`, `H = μ_m^I` and `G` is affine and locally of finite presentation over
`Spec R`, so `G` is of finite presentation. The conclusion is that `Y` is affine and locally of
finite presentation over `Spec R`, so `Y` is of finite presentation over `Spec R`. This module
does not treat the other cases of 3.12: general `S`, other finite `H` of multiplicative type, or
`G` only of finite type.

SGA cuts `Hom_{S-gr}(H, G)` out of `Hom_S(H, G)` by a finite limit, and represents `Hom_S(H, G)`
by polynomial equations in the coordinates of a basis of the coordinate ring of `H`. The Lean proof
follows the same idea in a different form. `HomAlgebra` of `Langlands.Algebra.FiniteBialgebraHom`
imposes the Hopf compatibility equations, in coordinates, on the Library Weil restriction. It is
used here for the task "Prove smooth moduli of actual closed torus subgroups" (SGA 3, Exp. XI,
4.1, torus case), whose proof approximates subtori by their finite torsion subgroups.

## Characters of `(ℤ/m)^I` (`section Characters`)

Here `M` is any commutative monoid.

- `apply_single_pow`: a character `χ : Multiplicative (I → ZMod m) →* Mˣ` sends each basis
  vector `Pi.single i 1` to an `m`-th root of unity.
- `rootHom ζ : ZMod m →+ Additive Mˣ` sends `k` to `ζ^k`, for `ζ ∈ rootsOfUnity m M`. It is
  defined with `ZMod.lift`, and `rootHom_intCast` evaluates it on integers.
- `charOfRoots t` is the character `x ↦ ∏ i, (t i)^(x i)`. `charOfRoots_single` evaluates it on
  `Pi.single i a`.
- `ofAdd_single_intCast`: `Pi.single i (k : ZMod m)` is the `k`-th power of `Pi.single i 1`.
- `rootsCharEquiv I m M : (Multiplicative (I → ZMod m) →* Mˣ) ≃* (I → rootsOfUnity m M)`
  evaluates a character on the basis vectors. Its inverse is `charOfRoots`. Both inverse laws are
  proved: each `x` is the product of its coordinate vectors, and each coordinate lifts to an
  integer. `rootsCharEquiv_apply_coe` records the forward formula.

## Identifying `μ_m^I` with a Hopf spectrum (`section Points`)

- `muPower R I m` abbreviates `pi fun _ : I => (mu (Spec (CommRingCat.of R)) m).toGrp`.
- `rootsRestrict R I m a` restricts families of `m`-th roots of unity along the global sections
  of `a : T' ⟶ T`.
- `diagonalizablePointsEquiv R I m T` identifies the `T`-points of the Library diagonalizable
  group scheme `Diagonalizable.groupScheme (CommRingCat.of R) (I → ZMod m)` with
  `I → rootsOfUnity m Γ(T, ⊤)`. It composes `Corepresented.pointsEquiv` (points are characters
  with values in `Γ(T, ⊤)ˣ`) with `rootsCharEquiv`. `diagonalizablePointsEquiv_naturality` proves
  naturality in `T`.
- `muPowerPointsEquiv R I m T` makes the same identification for `muPower R I m`, using
  `piPointsEquiv` and `mu.pointsEquiv`. `muPowerPointsEquiv_naturality` proves naturality.
- `diagonalizableIso R I m` is the isomorphism of group schemes from the diagonalizable group
  scheme of `(ℤ/m)^I` to `muPower R I m`. It is built by the Library `isoOfPointModels` from the
  two natural identifications.
- `muPowerHopfIso R I m : hopfGroup R (AddMonoidAlgebra R (I → ZMod m)) ≅ muPower R I m` composes
  the Library `Diagonalizable.hopfSpecIso` with `diagonalizableIso`. Here `hopfGroup` is the
  Hopf spectrum of `HomScheme.FiniteSourceHom`.

## The target as a Hopf spectrum (`section Coordinates`)

Here `G` is a group scheme over `Spec R` with `IsAffine G.X.left`.

- `coordinateIso G : hopfGroup R (AffineCoordinates.hopfAlgebra G) ≅ G` is the Library
  `AffineCoordinates.hopfSpecIso G`, after identifying the bundled Hopf algebra with the bundling
  of its carrier (`CommHopfAlgCat.ofIsoSelf`).
- `finitePresentation_hopfAlgebra G`: if `G.X.hom` is locally of finite presentation, then the
  coordinate Hopf algebra is a finitely presented `R`-algebra. Through `coordinateIso`, the
  structure map of `Spec` of the coordinate algebra is isomorphic over `Spec R` to `G.X.hom`. So it
  is locally of finite presentation, and Mathlib's `HasRingHomProperty.Spec_iff` together with
  `RingHom.finitePresentation_algebraMap` gives the algebraic statement.

## The universal family (`section Universal`)

Here `I` has `Fintype` and `DecidableEq` instances and `[NeZero m]` holds. These make
`AddMonoidAlgebra R (I → ZMod m)` finite free over `R`. Also `G` is affine and locally of finite
presentation.

- The instance `Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)` is
  `finitePresentation_hopfAlgebra G`.
- `homAlgebra R I m G` is
  `HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R (I → ZMod m))`, from
  `Langlands.Algebra.FiniteBialgebraHom`.
- `universalHom R I m G : RelativeHom (muPower R I m) G (specOver R (homAlgebra R I m G))` is the
  universal family `FiniteSource.universalFamily`, transported along `muPowerHopfIso` and
  `coordinateIso` by `HomScheme.transport`.
- `isUniversal_universalHom`: this family is universal, by `isUniversal_universalFamily` and
  `IsUniversal.transport`.

The proof of `exists_isUniversal_muPower` takes `Y := specOver R (homAlgebra R I m G)` and
`i := universalHom R I m G`. `IsAffine` holds because `Y.left` is a spectrum. `IsAffineHom` gives
`IsAffine G.X.left`, since the base `Spec R` is affine. Local finite presentation of `Y.hom` is
`HasRingHomProperty.Spec_iff` applied to the finite-presentation instance of `HomAlgebra`.
