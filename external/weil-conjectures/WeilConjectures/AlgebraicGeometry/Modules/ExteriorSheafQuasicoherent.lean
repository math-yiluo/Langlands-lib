/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit
import WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Quasi-coherence of exterior sheaves on affine schemes

## References

* Stacks Project, Section 26.7, Lemmas 26.7.1 and 26.7.2(2), Tag 01I6
* Stacks Project, Section 26.7, Lemmas 26.7.1, 26.7.2(2), and 26.7.4, Tag 01I6
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Exterior powers of a quasi-coherent module on an affine scheme are quasi-coherent. -/
theorem isQuasicoherent_exteriorSheaf_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (exteriorPower M n).IsQuasicoherent := open CategoryTheory Opposite in by
  let E := exteriorPower M n
  let P := (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  let η := ((PresheafOfModules.sheafificationAdjunction.{u}
    (CategoryTheory.CategoryStruct.id X.ringCatSheaf.obj)).unit.app P)
  have hloc (W : X.Opens) (hW : IsAffineOpen W) (f : Γ(X, W)) :
      letI : Module Γ(X, W) (P.obj (op (X.basicOpen f))) :=
        Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
      IsLocalizedModule.Away f (P.map (homOfLE (X.basicOpen_le f)).op).hom := by
    let : Module Γ(X, W) Γ(M, X.basicOpen f) :=
      Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
    let : Module Γ(X, W) (P.obj (op (X.basicOpen f))) :=
      Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
    have : IsScalarTower Γ(X, W) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
      ⟨fun a b m => mul_smul _ _ _⟩
    have := hW.isLocalization_basicOpen f
    have : IsLocalizedModule (.powers f)
        (M.val.map (homOfLE (X.basicOpen_le f)).op).hom :=
      isLocalizedModule_basicOpen M hW f
    refine exteriorPower.isLocalizedModule_of_pure_wedge
      (R := Γ(X, W)) (A := Γ(X, X.basicOpen f))
      (M := Γ(M, W)) (N := Γ(M, X.basicOpen f))
      (.powers f) (M.val.map (homOfLE (X.basicOpen_le f)).op).hom n _ ?_
    intro a
    exact (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n
      (homOfLE (X.basicOpen_le f)).op) a
  apply isQuasicoherent_of_forall_isAffineOpen E
  · intro W hW f s
    obtain ⟨s', hs'⟩ := (exteriorSheaf_affine_unit_bijective M n
      ⟨X.basicOpen f, hW.basicOpen f⟩).2 s
    let : Module Γ(X, W) (P.obj (op (X.basicOpen f))) :=
      Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
    have := hloc W hW f
    obtain ⟨⟨t, _, k, rfl⟩, ht⟩ := IsLocalizedModule.surj (.powers f)
      (P.map (homOfLE (X.basicOpen_le f)).op).hom s'
    refine ⟨k, η.app (op W) t, ?_⟩
    have hn := PresheafOfModules.naturality_apply η
      (homOfLE (X.basicOpen_le f)).op t
    change E.val.map _ (η.app (op W) t) = _
    erw [← hn]
    change η.app (op (X.basicOpen f)) (_ ) = _
    erw [← ht]
    change η.app (op (X.basicOpen f))
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k)) • s') = _
    rw [map_pow, (η.app (op (X.basicOpen f))).hom.map_smul, hs']
  · intro W hW f t ht
    obtain ⟨t', ht'⟩ := (exteriorSheaf_affine_unit_bijective M n ⟨W, hW⟩).2 t
    let : Module Γ(X, W) (P.obj (op (X.basicOpen f))) :=
      Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen f))
    have := hloc W hW f
    have hz : (P.map (homOfLE (X.basicOpen_le f)).op).hom t' = 0 := by
      apply (exteriorSheaf_affine_unit_bijective M n
        ⟨X.basicOpen f, hW.basicOpen f⟩).1
      rw [map_zero]
      erw [PresheafOfModules.naturality_apply η
        (homOfLE (X.basicOpen_le f)).op t']
      exact ht' ▸ ht
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalizedModule.eq_zero_iff (.powers f)
        (P.map (homOfLE (X.basicOpen_le f)).op).hom).mp hz
    refine ⟨k, ?_⟩
    rw [← ht', ← (η.app (op W)).hom.map_smul]
    exact (congrArg (η.app (op W)) hk).trans (map_zero _)

end AlgebraicGeometry.Scheme.Modules
