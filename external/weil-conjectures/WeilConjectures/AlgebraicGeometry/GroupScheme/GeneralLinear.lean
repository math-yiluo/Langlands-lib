/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup

/-!
# The general linear group scheme

The general linear group `GL_n` over a commutative ring `k` is the affine group scheme
`Spec k[x_ij, det⁻¹]` over `Spec k`, the spectrum of the Hopf algebra
`Matrix.GeneralLinearGroup.CoordinateRing n k`. Mathlib's `instGrpObjSpecAsOverSpec`
makes it a
group object in `Over (Spec k)`. Its points with values in a `k`-algebra `R` are the invertible
`n × n` matrices over `R`, as groups.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup`, notation `𝔾𝕃(n; k)`: `GL_n` as an affine group scheme
  of finite type over `k`.
- `AlgebraicGeometry.GeneralLinearGroup.homMulEquiv`: the `R`-points of the group scheme
  `𝔾𝕃(n; k)` are the group `GL n R`.

## Blueprint

- `det-d-geometry`: the ambient group `GL(V)` of the algebraic groups block, as a group scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry WithConv
open scoped MonObj
open Matrix.GeneralLinearGroup (CoordinateRing algHomMulEquiv map_algHomMulEquiv)

namespace AlgebraicGeometry

variable (n : Type u) [Fintype n] [DecidableEq n] (k : Type u) [CommRing k]

/-- The general linear group scheme `𝔾𝕃(n; k)` over a commutative ring `k`: the affine group
scheme `Spec k[x_ij, det⁻¹]` over `Spec k`, the spectrum of the Hopf algebra
`Matrix.GeneralLinearGroup.CoordinateRing n k`. (blueprint: `det-d-geometry`) -/
noncomputable def GeneralLinearGroup : Over (Spec (.of k)) :=
  (Spec (.of (CoordinateRing n k))).asOver (Spec (.of k))

@[inherit_doc] scoped notation "𝔾𝕃(" n "; " k ")" => GeneralLinearGroup n k

namespace GeneralLinearGroup

/-- `𝔾𝕃(n; k)` is a group object in `Over (Spec k)`, by the Hopf algebra structure of its
coordinate ring (`instGrpObjSpecAsOverSpec`). -/
noncomputable instance : GrpObj 𝔾𝕃(n; k) :=
  inferInstanceAs (GrpObj ((Spec (.of (CoordinateRing n k))).asOver (Spec (.of k))))

instance : IsAffine (𝔾𝕃(n; k)).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing n k))))

instance : LocallyOfFiniteType (𝔾𝕃(n; k)).hom :=
  locallyOfFiniteType_specOverSpec

/-- The `R`-points of the group scheme `𝔾𝕃(n; k)` are the invertible `n × n` matrices over `R`,
as groups. (blueprint: `det-d-geometry`) -/
noncomputable def homMulEquiv (R : Type u) [CommRing R] [Algebra k R] :
    ((Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) ≃* GL n R :=
  Spec.mapMulEquiv.symm.trans (algHomMulEquiv n k R)

variable {n k} {R S : Type u} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

/-- The point of `𝔾𝕃(n; k)` corresponding to an algebra homomorphism `ψ : k[GL_n] → R` is the
matrix `ψ(x_ij)`. -/
@[simp]
theorem homMulEquiv_mapMulEquiv (ψ : WithConv (CoordinateRing n k →ₐ[k] R)) :
    homMulEquiv n k R (Spec.mapMulEquiv ψ) = algHomMulEquiv n k R ψ := by
  change algHomMulEquiv n k R (Spec.mapMulEquiv.symm (Spec.mapMulEquiv ψ)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The identification `homMulEquiv` of the points of `𝔾𝕃(n; k)` with invertible matrices is
natural in the algebra of values: precomposing with `Spec S ⟶ Spec R` maps the entries along
`R → S`. -/
theorem homMulEquiv_specMap_comp (φ : R →ₐ[k] S)
    (f : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    homMulEquiv n k S ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of k)) ≫ f) =
      Matrix.GeneralLinearGroup.map φ.toRingHom (homMulEquiv n k R f) := by
  unfold GeneralLinearGroup at f
  delta homMulEquiv GeneralLinearGroup
  obtain ⟨χ, rfl⟩ := Spec.mapMulEquiv.surjective f
  simp only [Spec.map_asOver_comp_mapMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [← toConv_ofConv χ, map_algHomMulEquiv, ofConv_toConv]

end GeneralLinearGroup

end AlgebraicGeometry
