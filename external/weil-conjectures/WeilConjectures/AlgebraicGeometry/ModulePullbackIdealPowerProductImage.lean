/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealProductImage
import all WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealPowerImage
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Pullback images of products by recursive ideal powers

Source: Stacks Project, Tag 0887, the quotient computation in the proof.
(blueprint: lem-weil-pbc-module-pullback-ideal-power-product-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every recursive power inclusion is monic, by induction and monicity of image inclusions. -/
private theorem power_mono {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ) :
    Mono (Scheme.idealSheafPower J.toModulesι n).2 := by
  induction n using Nat.twoStepInduction with
  | zero => change Mono (𝟙 _); infer_instance
  | one => change Mono J.toModulesι; infer_instance
  | more n ih₁ ih₂ =>
    change Mono (Scheme.idealModuleProductι J.toModulesι _ ≫ _)
    have : Mono (Scheme.idealModuleProductι J.toModulesι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).1) := by
      dsimp [Scheme.idealModuleProductι]
      infer_instance
    exact mono_comp _ _

/-- Recursive powers and ideal-data powers agree as subobjects of the structure sheaf.
The affine section ranges agree, including at zero; the affine basis detects equality. -/
private theorem power_subobject_eq {X : Scheme.{u}} (J : X.IdealSheafData) (n : ℕ) :
    let j := (Scheme.idealSheafPower J.toModulesι n).2
    let k := (J ^ n).toModulesι
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ k = j := by
  classical
  dsimp only
  have := power_mono J n
  have hr (U : X.affineOpens) :
      Set.range ((Scheme.idealSheafPower J.toModulesι n).2.app U.1) =
        Set.range ((J ^ n).toModulesι.app U.1) := by
    rw [Scheme.IdealSheafData.range_toModulesι_app]
    cases n with
    | zero => simp [Scheme.idealSheafPower]
    | succ n =>
      have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
        @SheafOfModules.isQuasicoherent_unit _ _ _ _ X.ringCatSheaf _ _ _ _
      exact ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
        (SheafOfModules.unit X.ringCatSheaf)).2.2.2.1 U).2.2.2 (n + 1) (by omega)
  have h : Subobject.mk (Scheme.idealSheafPower J.toModulesι n).2 =
      Subobject.mk (J ^ n).toModulesι :=
    le_antisymm
      (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
      (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
  exact ⟨Subobject.isoOfMkEqMk _ _ h, by simp⟩

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism over the structure sheaf induces an isomorphism of product inclusions. -/
private theorem product_iso {X : Scheme.{u}} {P Q : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (κ : Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    (e : P ≅ Q) (he : e.hom ≫ κ = ι) (F : X.Modules) :
    ∃ a : Scheme.idealModuleProduct ι F ≅ Scheme.idealModuleProduct κ F,
      a.hom ≫ Scheme.idealModuleProductι κ F = Scheme.idealModuleProductι ι F := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have hi : Mono (Scheme.idealModuleProductι ι F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have hk : Mono (Scheme.idealModuleProductι κ F) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  have h : Subobject.mk (Scheme.idealModuleProductι ι F) =
      Subobject.mk (Scheme.idealModuleProductι κ F) := by
    change imageSubobject (ι ▷ F ≫ (λ_ F).hom) =
      imageSubobject (κ ▷ F ≫ (λ_ F).hom)
    have hm : ι ▷ F ≫ (λ_ F).hom = (e.hom ▷ F) ≫ (κ ▷ F ≫ (λ_ F).hom) := by
      rw [← he, comp_whiskerRight, Category.assoc]
    calc
      _ = imageSubobject ((e.hom ▷ F) ≫ (κ ▷ F ≫ (λ_ F).hom)) :=
        congrArg (fun m : P ⊗ F ⟶ F ↦ imageSubobject m) hm
      _ = _ := imageSubobject_iso_comp (e.hom ▷ F) _
  exact ⟨Subobject.isoOfMkEqMk _ _ h, by simp⟩


/-- The image of the pulled-back inclusion of `J^n G` is `(J O_X)^n f^*G`, using
module-subobject powers on both sides.
Source: Stacks Project, Tag 0887, the displayed computation in its proof.
(blueprint: lem-weil-pbc-module-pullback-ideal-power-product-image).

Proof: on affine opens V in Y and U in X contained in the inverse image of V, put
A = O_Y(V), B = O_X(U), a = J(V), and M = G(V). Induction on the recursive ideal
power identifies its sections and inclusion with a^n inside A; the ideal-product
formula then identifies J^n G with a^n M. The affine pullback comparison identifies
the pulled-back inclusion with B tensor_A a^n M -> B tensor_A M. Its image is the
submodule generated by b tensor c m for c in a^n, which equals (a B)^n times
B tensor_A M: extension of ideals commutes with powers, and both submodules are
generated by these tensors. The same affine formulas identify this with the image
of the product inclusion on X. These modules and images are quasi-coherent, by
quasi-coherence of positive powers, ideal products, pullback, and images. Equality
of their subobjects on this affine basis therefore implies equality of the sheaf
subobjects: local membership and gluing give each inclusion. For n = 0 both power
inclusions are the structure-sheaf identity, and the product is the whole module.
Zero ideals, unit ideals, zero modules, and empty opens satisfy the same formulas.
This is the ideal-power image calculation behind the quotient computation of 0887. -/
theorem modulePullbackIdealPowerProductImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) (n : ℕ) :
    imageSubobject ((Scheme.Modules.tensorPullback f).map
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 G)) =
      imageSubobject (Scheme.idealModuleProductι
        (Scheme.idealSheafPower (J.comap f).toModulesι n).2
        ((Scheme.Modules.tensorPullback f).obj G)) := by
  classical
  let T := Scheme.Modules.tensorPullback f
  obtain ⟨eY, heY⟩ := power_subobject_eq J n
  obtain ⟨eX, heX⟩ := power_subobject_eq (J.comap f) n
  obtain ⟨aY, haY⟩ := product_iso _ _ eY heY G
  obtain ⟨aX, haX⟩ := product_iso _ _ eX heX (T.obj G)
  have hpow : (J ^ n).comap f = (J.comap f) ^ n := by
    exact Scheme.IdealSheafData.comap_pow f J n
  calc
    _ = imageSubobject (T.map (Scheme.idealModuleProductι (J ^ n).toModulesι G)) := by
      rw [← haY, T.map_comp]
      exact imageSubobject_iso_comp (T.map aY.hom) _
    _ = imageSubobject (Scheme.idealModuleProductι ((J ^ n).comap f).toModulesι
        (T.obj G)) := modulePullbackIdealProductImage f (J ^ n) G hG
    _ = imageSubobject (Scheme.idealModuleProductι ((J.comap f) ^ n).toModulesι
        (T.obj G)) := by rw [hpow]
    _ = _ := by
      rw [← haX]
      exact (imageSubobject_iso_comp aX.hom _).symm

end AlgebraicGeometry
