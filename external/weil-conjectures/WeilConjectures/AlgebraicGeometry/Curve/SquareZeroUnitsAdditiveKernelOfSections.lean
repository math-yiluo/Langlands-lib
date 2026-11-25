/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf

/-! # Comparing unit and additive kernels from square-zero section kernels

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-units-additive-kernel-sections)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- If the section kernels of restriction have square zero, its unit and additive sheaf
kernels are isomorphic. No closed-immersion or ideal-sheaf hypothesis is needed.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-square-zero-relative-units-additive-kernel-sections)

Proof: On every etale object V, the unit kernel consists of units u restricting to 1.
Send u to u-1, which restricts to zero. For u,v in the kernel, square-zero gives
(u-1)(v-1)=0 and therefore uv-1=(u-1)+(v-1). Conversely send an additive kernel
section a to the unit 1+a, with inverse 1-a, since a*a=0. Products correspond to
sums since a*b=0. Ring restriction maps commute with both formulas, including
the coefficient universe lift. These maps therefore give sheaf morphisms into
the ambient coefficient sheaves, and the zero-composition identities factor them
through the two categorical kernels. Their composites are identity maps after
composition with the kernel inclusions, by the formulas (1+a)-1=a and 1+(u-1)=u.
The inclusions are monomorphisms, so the factorizations are mutually inverse.
Empty objects have the zero ring; the same formulas still give the unique maps. -/
theorem nonempty_unitsAdditiveKernelIso_of_sections {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hsq : ∀ (V : Y.Etaleᵒᵖ) (a b : Y.etaleStructurePresheaf.obj V),
      (etaleStructurePresheafToPullback g).app V a = 0 →
      (etaleStructurePresheafToPullback g).app V b = 0 → a * b = 0) :
    Nonempty (kernel (gmSheafToLowerStarGmSheaf g) ≅
      kernel (etaleAdditiveSheafToLowerStar g)) := by
  let q := gmSheafToLowerStarGmSheaf g
  let r := etaleAdditiveSheafToLowerStar g
  let ku := kernel.ι q
  let ka := kernel.ι r
  let uv (V : Y.Etaleᵒᵖ) (x : (kernel q).obj.obj V) :
      (Y.etaleStructurePresheaf.obj V)ˣ := (ku.hom.app V x).down.toMul
  let av (V : Y.Etaleᵒᵖ) (x : (kernel r).obj.obj V) :
      Y.etaleStructurePresheaf.obj V := (ka.hom.app V x).down
  have hu (V) (x : (kernel q).obj.obj V) :
      (etaleStructurePresheafToPullback g).app V (uv V x : Y.etaleStructurePresheaf.obj V) = 1 := by
    have h := congrArg (fun t ↦ (t.hom.app V x).down.toMul.val) (kernel.condition q)
    exact h
  have ha (V) (x : (kernel r).obj.obj V) :
      (etaleStructurePresheafToPullback g).app V (av V x) = 0 := by
    have h := congrArg (fun t ↦ (t.hom.app V x).down) (kernel.condition r)
    exact h
  have hu' (V) (x : (kernel q).obj.obj V) :
      (etaleStructurePresheafToPullback g).app V
        ((uv V x : Y.etaleStructurePresheaf.obj V) - 1) = 0 := by
    change ((etaleStructurePresheafToPullback g).app V).hom _ = 0
    rw [map_sub, map_one, hu]
    exact sub_self _
  let f : kernel q ⟶ Y.etaleAdditiveSheaf := ⟨{
    app := fun V ↦ AddCommGrpCat.ofHom {
      toFun := fun x ↦ ULift.up (show Y.etaleStructurePresheaf.obj V from
        (uv V x : Y.etaleStructurePresheaf.obj V) - 1)
      map_zero' := by
        apply ULift.ext
        change (uv V 0 : Y.etaleStructurePresheaf.obj V) - 1 = 0
        have huv : uv V 0 = 1 :=
          congrArg (fun z ↦ z.down.toMul) (map_zero (ku.hom.app V).hom)
        rw [huv, Units.val_one, sub_self]
      map_add' := by
        intro x y
        apply ULift.ext
        have h := hsq V ((uv V x : Y.etaleStructurePresheaf.obj V) - 1)
          ((uv V y : Y.etaleStructurePresheaf.obj V) - 1) (hu' V x) (hu' V y)
        change ((uv V (x + y) : Y.etaleStructurePresheaf.obj V) - 1) =
          ((uv V x : Y.etaleStructurePresheaf.obj V) - 1) +
          ((uv V y : Y.etaleStructurePresheaf.obj V) - 1)
        have huv : uv V (x + y) = uv V x * uv V y := by
          exact congrArg (fun z ↦ z.down.toMul) (map_add (ku.hom.app V).hom x y)
        rw [huv, Units.val_mul]
        linear_combination h
    }
    naturality := by
      intro V W t
      ext x
      apply ULift.ext
      have h := congrArg (fun z ↦ (z x).down.toMul.val) (ku.hom.naturality t)
      change (uv W ((kernel q).obj.map t x) : _) - 1 =
        Y.etaleStructurePresheaf.map t ((uv V x : Y.etaleStructurePresheaf.obj V) - 1)
      change _ = (Y.etaleStructurePresheaf.map t).hom _
      rw [map_sub, map_one]
      simp only [AddCommGrpCat.comp_apply] at h
      change (uv W ((kernel q).obj.map t x) : Y.etaleStructurePresheaf.obj W) =
        (Y.etaleStructurePresheaf.map t).hom (uv V x : Y.etaleStructurePresheaf.obj V) at h
      exact congrArg (fun z ↦ z - 1) h
  }⟩
  have hf : f ≫ r = 0 := by
    ext V x
    apply ULift.ext
    change (etaleStructurePresheafToPullback g).app V _ = 0
    exact hu' V x
  let au (V : Y.Etaleᵒᵖ) (x : (kernel r).obj.obj V) :
      (Y.etaleStructurePresheaf.obj V)ˣ := {
    val := 1 + av V x
    inv := 1 - av V x
    val_inv := by
      have h := hsq V (av V x) (av V x) (ha V x) (ha V x)
      linear_combination -h
    inv_val := by
      have h := hsq V (av V x) (av V x) (ha V x) (ha V x)
      linear_combination -h
  }
  let j : kernel r ⟶ Y.gmSheaf := ⟨{
    app := fun V ↦ AddCommGrpCat.ofHom {
      toFun := fun x ↦ ULift.up (Additive.ofMul (au V x))
      map_zero' := by
        apply ULift.ext
        apply Additive.toMul.injective
        apply Units.ext
        change (1 : Y.etaleStructurePresheaf.obj V) + (ka.hom.app V 0).down = 1
        simp
      map_add' := by
        intro x y
        apply ULift.ext
        apply Additive.toMul.injective
        apply Units.ext
        have h := hsq V (av V x) (av V y) (ha V x) (ha V y)
        change 1 + av V (x + y) = (1 + av V x) * (1 + av V y)
        have hav : av V (x + y) = av V x + av V y := by
          exact congrArg ULift.down (map_add (ka.hom.app V).hom x y)
        rw [hav]
        linear_combination -h
    }
    naturality := by
      intro V W t
      ext x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      have h := congrArg (fun z ↦ (z x).down) (ka.hom.naturality t)
      change 1 + av W ((kernel r).obj.map t x) =
        Y.etaleStructurePresheaf.map t (1 + av V x)
      change _ = (Y.etaleStructurePresheaf.map t).hom _
      rw [map_add, map_one]
      simp only [AddCommGrpCat.comp_apply] at h
      change av W ((kernel r).obj.map t x) =
        (Y.etaleStructurePresheaf.map t).hom (av V x) at h
      exact congrArg (fun z ↦ 1 + z) h
  }⟩
  have hj : j ≫ q = 0 := by
    ext V x
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    change (etaleStructurePresheafToPullback g).app V (1 + av V x) = 1
    change ((etaleStructurePresheafToPullback g).app V).hom _ = 1
    rw [map_add, map_one, ha, add_zero]
  let F := kernel.lift r f hf
  let G := kernel.lift q j hj
  refine ⟨⟨F, G, ?_, ?_⟩⟩
  · apply (cancel_mono ku).mp
    simp only [Category.assoc, G, ku, kernel.lift_ι, Category.id_comp]
    ext V x
    apply ULift.ext
    apply Additive.toMul.injective
    apply Units.ext
    have h := congrArg (fun t ↦ (t.hom.app V x).down) (kernel.lift_ι r f hf)
    change 1 + av V (F.hom.app V x) = (uv V x : Y.etaleStructurePresheaf.obj V)
    change av V (F.hom.app V x) = (uv V x : Y.etaleStructurePresheaf.obj V) - 1 at h
    rw [h]
    ring
  · apply (cancel_mono ka).mp
    simp only [Category.assoc, F, ka, kernel.lift_ι, Category.id_comp]
    ext V x
    apply ULift.ext
    have h := congrArg (fun t ↦ (t.hom.app V x).down.toMul.val) (kernel.lift_ι q j hj)
    change (uv V (G.hom.app V x) : Y.etaleStructurePresheaf.obj V) - 1 = av V x
    change (uv V (G.hom.app V x) : Y.etaleStructurePresheaf.obj V) = 1 + av V x at h
    rw [h]
    ring

end AlgebraicGeometry.Scheme
