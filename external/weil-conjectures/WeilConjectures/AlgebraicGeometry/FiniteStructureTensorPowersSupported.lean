/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Properly supported coherent tensor powers

Source: Stacks Project, Tags 0CYS, 01I8 and 01XZ, applied in Tag 09ZT.
(blueprint: lem-weil-pbc-finite-structure-tensor-powers-supported).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_coherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M N : X.Modules) (hM : RingedSpace.IsCoherent X.toRingedSpace M)
    (hN : RingedSpace.IsCoherent X.toRingedSpace N) :
    RingedSpace.IsCoherent X.toRingedSpace (tensorObj (C := X.Modules) M N) := by
  have : M.IsQuasicoherent :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X M).mp hM |>.1
  have : N.IsQuasicoherent :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X N).mp hN |>.1
  have hq : (M ⊗ N).IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections M N).1
  have hf (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(M ⊗ N, U.1) := by
    have : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
      coherent_affine_sections_finite X M hM U.1 U.2
    have : Module.Finite Γ(X, U.1) Γ(N, U.1) :=
      coherent_affine_sections_finite X N hN U.1 U.2
    exact Module.Finite.of_surjective (tensorSectionsMap M N U.1)
      ((quasiCoherent_tensor_product_affine_sections M N).2 U.1 U.2).2
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X (M ⊗ N)).mpr
    ⟨hq, (((quasicoherent_finite_type_affine.{u, u} X).2 (M ⊗ N) hq).2.1
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X) (fun U ↦ U.2) hf).1⟩

private theorem tensor_annihilated {X : Scheme.{u}} (J : X.IdealSheafData)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ J.idealOfOpens U →
      ∀ x : Γ(M, U), a • x = 0) :
    ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ J.idealOfOpens U →
      ∀ x : Γ(M ⊗ N, U), a • x = 0 := by
  intro U a ha x
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨(M ⊗ N).presheaf, (M ⊗ N).isSheaf⟩
  let V : {V : X.affineOpens // V.1 ≤ U} → X.Opens := fun V ↦ V.1.1
  refine F.eq_of_locally_eq' V U (fun V ↦ homOfLE V.2) ?_ _ _ ?_
  · intro p hp
    obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hpW⟩
  · intro W
    rw [Scheme.Modules.map_smul, map_zero]
    have haW : X.presheaf.map (homOfLE W.2).op a ∈ J.idealOfOpens W.1.1 := by
      change a ∈ (J.idealOfOpens U : Set Γ(X, U)) at ha
      change X.presheaf.map (homOfLE W.2).op a ∈
        (J.idealOfOpens W.1.1 : Set Γ(X, W.1.1))
      rw [← J.range_toModulesι_app_eq_idealOfOpens] at ha ⊢
      obtain ⟨b, rfl⟩ := ha
      refine ⟨J.toModules.presheaf.map (homOfLE W.2).op b, ?_⟩
      exact ConcreteCategory.congr_hom
        (J.toModulesι.mapPresheaf.naturality (homOfLE W.2).op) b
    obtain ⟨t, ht⟩ :=
      ((quasiCoherent_tensor_product_affine_sections M N).2 W.1.1 W.1.2).2
        ((M ⊗ N).presheaf.map (homOfLE W.2).op x)
    rw [← ht]
    clear ht
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
      rw [tensorSectionsMap_tmul, ← smul_tmulSection, hM _ _ haW, zero_tmulSection]
    | add t s ht hs => simp only [map_add, smul_add, ht, hs, add_zero]

private theorem supported_of_annihilated {X S Z : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsProper (i ≫ f)]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hkill : ∀ (U : X.Opens) (a : Γ(X, U)), a ∈ i.ker.idealOfOpens U →
      ∀ x : Γ(F, U), a • x = 0) : HasSupportProperOver f F := by
  obtain ⟨hq, he, hf⟩ := (closedImmersion_pushforward_annihilated i).2 F hkill
  have : ((tensorPullback i).obj F).IsQuasicoherent := hq
  have : ((tensorPullback i).obj F).IsFiniteType := hf inferInstance
  have := he
  apply (module_support_proper_over_base f F).2.1.mpr
  exact ⟨Z, i, inferInstance, inferInstance, hkill, (tensorPullback i).obj F,
    inferInstance, inferInstance,
    ⟨asIso ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F)⟩⟩

/-- The tensor square and cube are in the proper-support coherent category.
Source: Stacks Project, Tags 0CYS, 01I8 and 01XZ, for the multiplication argument of 09ZT.

Proof: Since X is locally of finite type over the Noetherian ring A, it is locally
Noetherian. A coherent G is quasi-coherent of finite type (01XZ). Choose a proper closed
subscheme whose ideal annihilates G using 0CYS. Tensoring sections shows this ideal also
annihilates the tensor square and cube: a(x tensor y) = (ax) tensor y, and the same formula
holds for the cube. This statement extends from elementary tensors by linearity and
sheafification, so it holds as a sheaf statement. Quasi-coherent tensor products remain
quasi-coherent; on every affine open their sections are the tensor products of the
sections of their factors (01I8). Tensor products of finite modules are finite, so the
square and cube are of finite type by the affine criterion. Hence both are coherent by
01XZ. The annihilating proper closed subscheme and 0CYS then show that both supports are
proper over the base. No completion, multiplication, or unit is used. This includes the
zero module and empty scheme without any nonempty assumption.
(blueprint: lem-weil-pbc-finite-structure-tensor-powers-supported). -/
theorem finite_structure_tensor_powers_supported
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G) :
    RingedSpace.IsCoherent X.toRingedSpace (tensorObj (C := X.Modules) G G) ∧
    Scheme.Modules.HasSupportProperOver f (tensorObj (C := X.Modules) G G) ∧
    RingedSpace.IsCoherent X.toRingedSpace
      (tensorObj (C := X.Modules) (tensorObj (C := X.Modules) G G) G) ∧
    Scheme.Modules.HasSupportProperOver f
      (tensorObj (C := X.Modules) (tensorObj (C := X.Modules) G G) G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hq, hf⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have : G.IsQuasicoherent := hq
  have : G.IsFiniteType := hf
  obtain ⟨Z, i, hi, hp, hkill, _⟩ :=
    (module_support_proper_over_base f G).2.1.mp hproper
  have : IsClosedImmersion i := hi
  have : IsProper (i ≫ f) := hp
  have hSq := tensor_coherent G G hG hG
  have hCube := tensor_coherent (G ⊗ G) G hSq hG
  obtain ⟨hqSq, hfSq⟩ :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X (G ⊗ G)).mp hSq
  have : (G ⊗ G).IsQuasicoherent := hqSq
  have : (G ⊗ G).IsFiniteType := hfSq
  obtain ⟨hqCube, hfCube⟩ :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType X ((G ⊗ G) ⊗ G)).mp hCube
  have : ((G ⊗ G) ⊗ G).IsQuasicoherent := hqCube
  have : ((G ⊗ G) ⊗ G).IsFiniteType := hfCube
  have hkSq := tensor_annihilated i.ker G G hkill
  have hkCube := tensor_annihilated i.ker (G ⊗ G) G hkSq
  exact ⟨hSq, supported_of_annihilated f i (G ⊗ G) hkSq,
    hCube, supported_of_annihilated f i ((G ⊗ G) ⊗ G) hkCube⟩

end AlgebraicGeometry
