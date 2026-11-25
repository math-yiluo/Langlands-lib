/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Mul
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist


/-!
# The twisting sheaves `𝒪(m)` on `Proj` of a graded ring

This module only re-exports its parts, which live in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist`; it was split to keep the compilation
of each part cheap.

Let `𝒜 : ℕ → σ` be a graded ring with underlying ring `A`, and let `m : ℤ`. We construct the
twisting sheaf `𝒪(m)` on `Proj 𝒜` as a sheaf of modules over the structure sheaf.

The construction mirrors the one of the structure sheaf in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`. The fibre at a point `x` is
the degree-`m` part `HomogeneousLocalization.degreePart 𝒜 x m` of the localization `A_x`: the
fractions `a / b` with `a ∈ 𝒜 i`, `b ∈ 𝒜 j`, `b ∉ x` and `i = j + m`. A section of `𝒪(m)` over
an open set `U` is a dependent function `x ↦ s x` into these fibres which is locally a fixed
fraction `a / b` of this kind. This is Hartshorne's `(S(m))~`. Sections of the structure sheaf
are dependent functions into the degree-`0` parts `(A_x)₀`, and they act on sections of `𝒪(m)`
by pointwise multiplication.

The fibre is the submodule `degreePart 𝒜 x m` rather than all of `A_x`, so that the
`HomogeneousLocalization`-module structure of the fibres can be used directly: `𝒪(0) ≅ 𝒪` is
`HomogeneousLocalization.degreePart.zeroEquiv` applied pointwise, and multiplication by a
homogeneous element is `HomogeneousLocalization.mul_mem_degreePart` applied pointwise.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpectrum.Twist.isLocallyFraction`: the local predicate cutting
  out the sections of `𝒪(m)`.
- `AlgebraicGeometry.Proj.twist`: the twisting sheaf `𝒪(m)` on `Proj 𝒜`.
- `AlgebraicGeometry.Proj.twistMul`: multiplication by a homogeneous element `f` of degree `d`,
  as a morphism `𝒪(m) ⟶ 𝒪(m + d)`.
- `AlgebraicGeometry.Proj.twistPowSection`: the section `fᵐ` of `𝒪(m)` over `D₊(f)`, for `f`
  homogeneous of degree `1`; it is a free generator.

## Main results

- `AlgebraicGeometry.Proj.unitIsoTwistZero`: `𝒪(0)` is the structure sheaf.
- `AlgebraicGeometry.Proj.twistRestrictIso`: on the basic open set `D₊(f)`, multiplication by
  `f` is an isomorphism `𝒪(m) ≅ 𝒪(m + d)`. Together with `unitIsoTwistZero`, this says that
  `𝒪(k * d)` is trivial on `D₊(f)`.
- `AlgebraicGeometry.Proj.nonempty_restrict_twist_iso_unit`: `𝒪(m)` is trivial on `D₊(f)` for
  every `m` when `f` has degree `1`.
- `AlgebraicGeometry.Proj.isInvertible_twist`: `𝒪(m)` is invertible when the `D₊(f)` with `f`
  of degree `1` cover `Proj 𝒜`.
- `AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` under the same
  hypothesis, by gluing the free generators `fᵃ ⊗ fᵇ` and `fᵃ⁺ᵇ` on the `D₊(f)`.
- `AlgebraicGeometry.Proj.unitToTwist`: the global section `f` of `𝒪(d)`, for `f` homogeneous of
  degree `d`, as a morphism `𝒪 ⟶ 𝒪(d)`; it is an isomorphism on `D₊(f)`.
- `AlgebraicGeometry.Proj.map_unitToTwist_eq_smul`: the transition rule `f = (f / g) • g` on
  `D₊(g)` between the global sections `f` and `g` of `𝒪(d)`.

## TODO

- Construct `M~` for an arbitrary graded `A`-module `M` and recover `𝒪(m)` as `(A(m))~`. All
  the proofs in this module go through with `a ∈ 𝒜 i` replaced by `a ∈ M i`.
- Construct the multiplication `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)` canonically, without the hypothesis that
  the `D₊(f)` with `f` of degree `1` cover `Proj 𝒜`; its existence under that hypothesis is
  `AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso`.
- The global sections `𝒜 m → Γ(𝒪(m))` of homogeneous elements; for a polynomial ring, they are
  all the global sections.
- Relate `Proj.twist` to `Proj.twistingSheaf` on the `Abelian-variety` branch, whose fibres are
  all of `A_x`.
-/
