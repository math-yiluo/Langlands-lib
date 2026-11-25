/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Finiteness from formal quotients and a bounded torsion kernel

Source: Stacks Project, Tag 0889(1), finiteness paragraph, and Tag 05EU.
(blueprint: lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Modules

private theorem exists_fg_lift {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (K : Submodule R Q) (hK : K.FG) (hle : K ≤ f.range) :
    ∃ L : Submodule R P, L.FG ∧ L.map f = K := by
  classical
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hmem (i : Fin n) : v i ∈ K := by
    rw [← hv]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose w hw using fun i ↦ hle (hmem i)
  refine ⟨Submodule.span R (Set.range w), Submodule.fg_span (Set.finite_range w), ?_⟩
  rw [Submodule.map_span]
  convert hv using 2
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hw i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨w i, ⟨i, rfl⟩, hw i⟩

private theorem finite_of_quotient_and_torsion_kernel
    {R P H : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H] [Module.Finite R H]
    (I : Ideal R) (a : P →ₗ[R] H)
    [Module.Finite R (P ⧸ (I • (⊤ : Submodule R P)))]
    (hk : ∀ r ∈ I, ∀ x : P, a x = 0 → r • x = 0) : Module.Finite R P := by
  classical
  let K := I • (⊤ : Submodule R P)
  obtain ⟨L₁, hL₁, hmap₁⟩ := exists_fg_lift a a.range (IsNoetherian.noetherian _) le_rfl
  obtain ⟨L₂, hL₂, hmap₂⟩ := exists_fg_lift K.mkQ ⊤ Module.Finite.fg_top
    (by rw [Submodule.range_mkQ])
  let L := L₁ ⊔ L₂
  have hIL : K ≤ L := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ (fun x y hx hy ↦ L.add_mem hx hy)
    intro r hr x _
    have hx : a x ∈ L₁.map a := by rw [hmap₁]; exact ⟨x, rfl⟩
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
    have hxy : a (x - y) = 0 := by simp [map_sub, heq]
    have hz := hk r hr (x - y) hxy
    have he : r • x = r • y := by simpa only [smul_sub, sub_eq_zero] using hz
    rw [he]
    exact (show L₁ ≤ L from le_sup_left) (L₁.smul_mem r hy)
  have htop : L = ⊤ := by
    have h := (Submodule.map_mkQ_eq_top K L₂).mp hmap₂
    apply top_unique
    rw [← h]
    exact sup_le hIL le_sup_right
  apply Module.Finite.of_fg_top
  rw [← htop]
  exact hL₁.sup hL₂

set_option backward.isDefEq.respectTransparency false in
/-- A fixed quasi-coherent candidate is coherent if its quotient by a positive ideal
power is coherent and that same power annihilates the kernel of a map to a coherent module.

Source: Stacks Project, Tag 0889(1), finiteness paragraph, and Tag 05EU.
(blueprint: lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel).

Proof: on X = Spec A let P and M be the sections of F and H, and let I be the
sections of J. Exactness of affine sections identifies the kernel of a with
ker(P -> M), killed by I^s. The formal quotient at level s has finite sections,
namely P/I^s P. The image in the finite module M is finite since A is Noetherian.
Choose a finite submodule L of P containing lifts of generators of both this image
and P/I^s P. Surjectivity onto the image gives P = L + ker a, so I^s P is contained
in L because I^s ker a = 0. Surjectivity onto the quotient gives P = L + I^s P.
Thus P=L is finite. The affine finite-type criterion and the Noetherian coherence
criterion give coherence. This works also for I=0, I=A, and the empty spectrum. -/
theorem coherent_of_formalQuotients_and_torsionKernel
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (H : CoherentModules X) (a : F ⟶ H.obj)
    (s : ℕ) (hs : 1 ≤ s)
    (hquot : RingedSpace.IsCoherent X.toRingedSpace
      (((formalCompletionFunctor J).obj F).obj (op (s - 1))))
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
      (kernel a))) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hH := (isCoherent_iff_isQuasicoherent_and_isFiniteType X H.obj).mp H.property
  have : H.obj.IsQuasicoherent := hH.1
  have : H.obj.IsFiniteType := hH.2
  have : (kernel a).IsQuasicoherent := isQuasicoherent_kernel a
  have hK := (idealPowerProduct_isZero_iff_affine_cover X (kernel a) J {U}
    (fun x ↦ ⟨U, Set.mem_singleton U, trivial⟩) s).mp hker U (Set.mem_singleton U)
  let I : Ideal Γ(X, U.1) := J.ideal U ^ s
  let φ := idealModuleProductι (idealSheafPower J.toModulesι s).2 F
  have hpower : (idealSheafPower J.toModulesι s).1.IsQuasicoherent :=
    (ideal_times_quasiCoherent_affine_sections J F).2.2.1 s (by omega)
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : (idealSheafPower J.toModulesι s).1.IsQuasicoherent := hpower
  have htensor := (quasiCoherent_tensor_product_affine_sections
    (idealSheafPower J.toModulesι s).1 F).1
  have : (MonoidalCategory.tensorObj (idealSheafPower J.toModulesι s).1 F).IsQuasicoherent :=
    htensor
  have hab := (quasiCoherent_cokernel_image
    (MonoidalCategoryStruct.whiskerRight (idealSheafPower J.toModulesι s).2 F ≫
      (MonoidalCategoryStruct.leftUnitor F).hom)).2.2.2.2.2.2.2.1
  have : (idealModuleProduct (idealSheafPower J.toModulesι s).2 F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage _) hab
  have hprod : LinearMap.range (φ.val.app (op U.1)).hom =
      I • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) := by
    have hp := Scheme.Modules.multiplication_range (idealSheafPower J.toModulesι s).2 F U
    have hi : LinearMap.range ((idealSheafPower J.toModulesι s).2.val.app (op U.1)).hom =
        I := by
      ext r
      exact Set.ext_iff.mp
        (((ideal_times_quasiCoherent_affine_sections J F).2.2.2.1 U).2.2.2 s
          (by omega)) r
    ext x
    have he : Set.range (φ.app U.1) = {x | x ∈ I •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))} := by
      simpa only [φ, hi] using hp
    exact Set.ext_iff.mp he x
  have hq := (quasiCoherent_cokernel_image φ).2.2.2.2.2.2.2.2 U
  have hquot' : RingedSpace.IsCoherent X.toRingedSpace (cokernel φ) := by
    have h := hquot
    change RingedSpace.IsCoherent X.toRingedSpace
      (cokernel (idealModuleProductι (idealSheafPower J.toModulesι (s - 1 + 1)).2 F)) at h
    have he : s - 1 + 1 = s := by omega
    rw [he] at h
    exact h
  have hqcoh := (isCoherent_iff_isQuasicoherent_and_isFiniteType X (cokernel φ)).mp hquot'
  have : (cokernel φ).IsQuasicoherent := hqcoh.1
  have : (cokernel φ).IsFiniteType := hqcoh.2
  have : Module.Finite Γ(X, U.1) Γ(cokernel φ, U.1) :=
    coherent_affine_sections_finite X (cokernel φ) hquot' U.1 U.2
  obtain ⟨e, _⟩ := hq.2.2.2
  have : Module.Finite Γ(X, U.1)
      (Γ(F, U.1) ⧸ I • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) := by
    rw [← hprod]
    exact Module.Finite.equiv e.symm
  have : Module.Finite Γ(X, U.1) Γ(H.obj, U.1) :=
    coherent_affine_sections_finite X H.obj H.property U.1 U.2
  have hfinite : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    finite_of_quotient_and_torsion_kernel (P := Γ(F, U.1)) (H := Γ(H.obj, U.1))
      I (a.val.app (op U.1)).hom (by
      intro r hr x hx
      have hx' : x ∈ Set.range ((kernel.ι a).app U.1) :=
        (Set.ext_iff.mp (range_map_kernelι U.1 a) x).mpr hx
      obtain ⟨k, rfl⟩ := hx'
      have hz : r • k = 0 := Module.mem_annihilator.mp (hK hr) k
      change r • ((kernel.ι a).val.app (op U.1)).hom k = 0
      exact (_root_.map_smul ((kernel.ι a).val.app (op U.1)).hom r k).symm.trans
        ((congrArg ((kernel.ι a).val.app (op U.1)).hom hz).trans
          (map_zero ((kernel.ι a).val.app (op U.1)).hom)))
  have hFT := (quasicoherent_finite_type_affine.{u, 0} X).2 F inferInstance
  have : F.IsFiniteType := (hFT.2.1 PUnit.{1} (fun _ ↦ U.1)
    (by simp [U]) (fun _ ↦ U.2) (fun _ ↦ hfinite)).1
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mpr ⟨inferInstance, this⟩

end AlgebraicGeometry
