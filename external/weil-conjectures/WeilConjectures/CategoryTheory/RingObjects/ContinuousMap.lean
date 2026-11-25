/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Limits

/-!

# The sheaf of continuous maps into a topological ring

Let `X` be a scheme and `T` a topological ring. The presheaf `U ↦ C(U, T)` of continuous maps
on the small pro-étale site of `X` is a sheaf (it is even an fpqc sheaf,
`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`), and it is a presheaf of rings
for the pointwise operations. This file defines it as a sheaf of rings on `X_proét`,
`AlgebraicGeometry.ProEtale.continuousMapRingSheaf X T`. Its underlying abelian sheaf
`(sheafCompose _ (forget₂ RingCat Ab)).obj (continuousMapRingSheaf X T)` is a ring object of
the category of abelian sheaves on `X_proét`
(`CategoryTheory.Sheaf.monObj_sheafCompose_obj`), commutative when `T` is. For `T = ℤ_ℓ` this
is the `ℓ`-adic sheaf `AlgebraicGeometry.Scheme.ellAdicSheaf` of mathlib, see
`WeilConjectures.CategoryTheory.RingObjects.EllAdic`.

## Main definitions

* `AlgebraicGeometry.ProEtale.continuousMapRingPresheaf`: the presheaf of rings `U ↦ C(U, T)`
  on `X_proét`.
* `AlgebraicGeometry.ProEtale.continuousMapRingSheaf`: the sheaf of rings `U ↦ C(U, T)`.
* `AlgebraicGeometry.ProEtale.continuousMapRingSheafMap`: the morphism of sheaves of rings
  induced by a continuous ring homomorphism `T →+* T'`.

## Universes

The small pro-étale site of `X : Scheme.{u}` has `Hom`-types in `Type u`, so sheaves on it
take values in `RingCat.{u + 1}` and `Ab.{u + 1}`, following the convention of the
`SixFunctors` folder. The sections `C(U, T)`, which live in `Type (max u w)` for `T : Type w`,
are therefore lifted by `ULift.{u + 1}`, so that the sheaf takes values in
`RingCat.{max (u + 1) w}`. This is `RingCat.{u + 1}` both for `T : Type` (for instance
`T = ℤ_ℓ`) and for `T : Type (u + 1)` (for instance a discrete quotient of a coefficient ring
`Λ : Type (u + 1)`).

-/

@[expose] public section

universe w u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u})

section Ring

variable (T : Type w) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The presheaf of rings `U ↦ C(U, T)` of continuous maps into the topological ring `T` on
the small pro-étale site of `X`, lifted by `ULift.{u + 1}`. -/
noncomputable def continuousMapRingPresheaf : X.ProEtᵒᵖ ⥤ RingCat.{max (u + 1) w} where
  obj U := RingCat.of (ULift.{u + 1} C(U.unop.left, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma continuousMapRingPresheaf_obj (U : X.ProEtᵒᵖ) :
    (continuousMapRingPresheaf X T).obj U = RingCat.of (ULift.{u + 1} C(U.unop.left, T)) :=
  rfl

lemma continuousMapRingPresheaf_map_apply {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (g : ULift.{u + 1} C(U.unop.left, T)) :
    (continuousMapRingPresheaf X T).map f g = ULift.up (g.down.comp f.unop.left.base.hom) :=
  rfl

/-- The presheaf of types underlying `continuousMapRingPresheaf X T` is the restriction to the
small pro-étale site of mathlib's presheaf `U ↦ C(U, T)` on all schemes, lifted by one
universe. -/
noncomputable def continuousMapRingPresheafForgetIso :
    continuousMapRingPresheaf X T ⋙ forget RingCat.{max (u + 1) w} ≅
      (ProEt.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf T ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf `U ↦ C(U, T)` is a sheaf for the pro-étale topology, being the restriction of
an fpqc sheaf. -/
lemma isSheaf_continuousMapRingPresheaf :
    Presheaf.IsSheaf (ProEt.topology X) (continuousMapRingPresheaf X T) := by
  have : ReflectsLimitsOfSize.{max (u + 1) w, max (u + 1) w} (forget RingCat.{max (u + 1) w}) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : ReflectsLimitsOfSize.{u, u + 1} (forget RingCat.{max (u + 1) w}) :=
    reflectsLimitsOfSize_shrink.{u + 1, max (u + 1) w, u, max (u + 1) w} _
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget RingCat.{max (u + 1) w}) ?_
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapRingPresheafForgetIso X T)]
  refine Functor.op_comp_isSheaf_of_isSheaf (F := ProEt.forget X ⋙ Over.forget X)
    (J := ProEt.topology X) (K := proetaleTopology) _ ?_
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    ← isSheaf_iff_isSheaf_of_type]
  exact (isSheaf_fpqcTopology_continuousMapPresheaf T).of_le proetaleTopology_le_fpqcTopology

/-- The sheaf of rings `U ↦ C(U, T)` of continuous maps into the topological ring `T` on the
small pro-étale site of `X`. Its underlying abelian sheaf
`(sheafCompose _ (forget₂ RingCat Ab)).obj (continuousMapRingSheaf X T)` is a ring object
with the pointwise multiplication. -/
noncomputable def continuousMapRingSheaf : Sheaf (ProEt.topology X) RingCat.{max (u + 1) w} :=
  ⟨continuousMapRingPresheaf X T, isSheaf_continuousMapRingPresheaf X T⟩

lemma continuousMapRingSheaf_obj :
    (continuousMapRingSheaf X T).obj = continuousMapRingPresheaf X T :=
  rfl

variable {T} {T' : Type w} [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
presheaves of rings `C(-, T) ⟶ C(-, T')`. -/
noncomputable def continuousMapRingPresheafMap :
    continuousMapRingPresheaf X T ⟶ continuousMapRingPresheaf X T' where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

lemma continuousMapRingPresheafMap_app_apply (U : X.ProEtᵒᵖ)
    (g : ULift.{u + 1} C(U.unop.left, T)) :
    (continuousMapRingPresheafMap X φ hφ).app U g = ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp g.down) :=
  rfl

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
sheaves of rings `C(-, T) ⟶ C(-, T')` on `X_proét`. -/
noncomputable def continuousMapRingSheafMap :
    continuousMapRingSheaf X T ⟶ continuousMapRingSheaf X T' :=
  ⟨continuousMapRingPresheafMap X φ hφ⟩

lemma continuousMapRingSheafMap_hom :
    (continuousMapRingSheafMap X φ hφ).hom = continuousMapRingPresheafMap X φ hφ :=
  rfl

end Ring

section CommRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The sheaf of continuous maps into a commutative topological ring is a commutative ring
object. This is stated for `T : Type`: the monoidal structure on abelian sheaves on `X_proét`
is only found by instance search for coefficients in `Ab.{u + 1}`. -/
instance isCommMonObj_continuousMapRingSheaf :
    IsCommMonObj ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X T)) :=
  Sheaf.isCommMonObj_sheafCompose_obj (ProEt.topology X) (continuousMapRingSheaf X T)
    fun U (a b : ULift.{u + 1} C(U.unop.left, T)) ↦ mul_comm a b

end CommRing

end AlgebraicGeometry.ProEtale
