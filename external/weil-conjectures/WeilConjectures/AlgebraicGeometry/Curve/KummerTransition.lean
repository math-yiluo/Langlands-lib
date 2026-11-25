/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop

/-!
# The transition maps of the Kummer identifications

For integers `m` and `d` the `d`-th power map `z ↦ z ^ d` maps `μ_{m d}` to `μ_m`; for a prime
`l` the maps `μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}`, `z ↦ z ^ l`, form the inverse system defining `ℤ_l(1)`. On a
proper scheme over an algebraically closed field, the Kummer identifications
`H¹(X, μ_m) ≅ Pic(X)[m]` (`AlgebraicGeometry.Scheme.kummerTorsionEquiv`) carry the map induced
by the `d`-th power map to multiplication by `d` on the torsion of the Picard group.

## Main definitions

- `AlgebraicGeometry.Scheme.rootsOfUnityPowMap`: the power map `μ_{m d} ⟶ μ_m`.

## Main statements

- `AlgebraicGeometry.Scheme.coe_kummerTorsionEquiv_map_rootsOfUnityPowMap`: the Kummer
  identification intertwines the power map with multiplication by `d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable (X) in
/-- The `d`-th power map `μ_{m'} ⟶ μ_m`, `z ↦ z ^ d`, of étale sheaves of roots of unity, for
`m' = m d`: the restriction of the `d`-th power map `d • 𝟙` of `𝔾ₘ`. For a prime `l` the maps
`μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}` (`AlgebraicGeometry.Scheme.rootsOfUnityPowMap l (pow_succ l n).symm`) are the
transition maps of the system `(μ_{lⁿ}, z ↦ z ^ l)` defining `ℤ_l(1)`
(blueprint: `proposition-kummer-duality-integral-tate-module`). -/
noncomputable def rootsOfUnityPowMap {m m' : ℕ} (d : ℕ) (h : m * d = m') :
    X.rootsOfUnitySheaf m' ⟶ X.rootsOfUnitySheaf m :=
  kernel.lift _ (kernel.ι (m' • 𝟙 X.gmSheaf) ≫ (d • 𝟙 X.gmSheaf)) (by
    have h' : (d • 𝟙 X.gmSheaf) ≫ (m • 𝟙 X.gmSheaf) = m' • 𝟙 X.gmSheaf := by
      rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, mul_comm, h]
    rw [Category.assoc, h', kernel.condition])

@[reassoc (attr := simp)]
lemma rootsOfUnityPowMap_ι {m m' : ℕ} (d : ℕ) (h : m * d = m') :
    X.rootsOfUnityPowMap d h ≫ kernel.ι (m • 𝟙 X.gmSheaf) =
      kernel.ι (m' • 𝟙 X.gmSheaf) ≫ (d • 𝟙 X.gmSheaf) :=
  kernel.lift_ι _ _ _

variable {k : Type u} [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- Blueprint `proposition-h-1-curve-tate-module--1` (transition maps): the Kummer
identifications `H¹(X, μ_m) ≅ Pic(X)[m]` carry the map induced by the `d`-th power map
`μ_{m d} ⟶ μ_m` to multiplication by `d` on line bundles. -/
lemma coe_kummerTorsionEquiv_map_rootsOfUnityPowMap {m m' : ℕ} (d : ℕ) (h : m * d = m')
    (hm : (m : k) ≠ 0) (hm' : (m' : k) ≠ 0) (x : Sheaf.H (X.rootsOfUnitySheaf m') 1) :
    (kummerTorsionEquiv m hm (Sheaf.H.map (X.rootsOfUnityPowMap d h) 1 x) : Additive X.Pic) =
      d • (kummerTorsionEquiv m' hm' x : Additive X.Pic) := by
  have e := congrArg (fun f ↦ Sheaf.H.map f 1 x) (rootsOfUnityPowMap_ι (X := X) d h)
  simp only [Sheaf.H.map_comp_apply] at e
  rw [Sheaf.H.map_nsmul_apply] at e
  rw [Sheaf.H.map_id_apply] at e
  rw [coe_kummerTorsionEquiv_apply, coe_kummerTorsionEquiv_apply, ← map_nsmul]
  exact congrArg _ e

end AlgebraicGeometry.Scheme
