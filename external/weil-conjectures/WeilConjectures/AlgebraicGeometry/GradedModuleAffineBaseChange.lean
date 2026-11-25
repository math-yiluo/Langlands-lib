/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffineModuleFiniteType
import WeilConjectures.AlgebraicGeometry.GradedModuleAffineBaseChangeAlgebra

/-! # Realizing a finite graded module on the affine base change

Source: Stacks Project, Tag 0897, proof, and Tag 01SB.
(blueprint: lem-weil-pbc-graded-module-affine-base-change)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- The underlying module of a finite graded module over the pulled-back algebra is
an affine pushforward of a quasi-coherent module of finite type. No twisting module,
properness or Noetherian hypothesis is required for this realization.

Source: Stacks Project, Tag 0897, proof (the realization and finite-type paragraphs),
with Tags 01SB and 01PB.
(blueprint: lem-weil-pbc-graded-module-affine-base-change)

Proof:
1. Set b = Spec(A → B), Y = X ×_Spec(A) Spec(B), and pi = Y → X. The morphism pi
   is affine by base change of an affine morphism. On an affine open Spec(R) of X,
   its inverse image is Spec(R tensor_A B). The associated algebra and tensor pullback
   identify pi_* O_Y with the algebra f^* B~.
2. Form the underlying module M = direct sum_m G_m. Each G_m is quasi-coherent, so
   M is quasi-coherent. Internalness of the grading decomposes each element of B as
   a finite sum of homogeneous elements. Let a homogeneous b in B_k act on G_m by
   mu m k b, followed by the inclusion of G_(m+k) in M. The additive law, composition
   law and scalar law give a unital B-action commuting with the O_X-action; the unit
   law follows from the scalar law at a = 1. On affine opens this extends uniquely
   to an R tensor_A B-action. Localization compatibility glues these actions to a
   sheaf of modules over pi_* O_Y. Its underlying O_X-module is M. By clause (1) of
   affine_module_correspondence it is quasi-coherent over that algebra as well.
3. The local sections s_i in hfinite, placed in their homogeneous summands, generate
   M over pi_* O_Y. Indeed, a section of the sheaf coproduct is locally a finite sum
   of homogeneous sections. Apply hfinite to each of the finitely many summands and
   intersect the resulting neighbourhoods. Its span formula expresses each summand
   as a sum of homogeneous algebra multiples of the s_i, with O_X coefficients.
   Such coefficients belong to pi_* O_Y through the structure algebra map. Thus the
   finite free sheaf on the s_i surjects locally, proving finite type over pi_* O_Y.
4. Apply the inverse of affine_module_correspondence to this algebra module. It gives
   a quasi-coherent O_Y-module F and an algebra-linear pushforward isomorphism.
   affine_module_finite_type gives F.IsFiniteType. Restrict scalars in the isomorphism
   to obtain the stated O_X-linear isomorphism with the coproduct of the G_m. -/
theorem exists_finiteType_graded_module_affine_baseChange
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → X.Modules)
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))}) :
    let b : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
    ∃ F : (pullback f b).Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      Nonempty ((Scheme.Modules.pushforward (pullback.fst f b)).obj F ≅ ∐ G) := by
  let b : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  let pi := pullback.fst f b
  let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj (pullback f b).sheaf
  let CR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
  let rho : X.sheaf ⟶ C := ⟨pi.c⟩
  let S := SheafOfModules.restrictScalars.{u}
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map rho)
  let R := SheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map pi.base)
    (S := CR) (R := (pullback f b).ringCatSheaf) (𝟙 CR)
  have : IsAffineHom b := inferInstance
  have : IsAffineHom pi := MorphismProperty.pullback_fst _ _ ‹IsAffineHom b›
  obtain ⟨N, hN, hNfinite, ⟨e⟩⟩ := exists_finiteType_graded_algebra_module
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite
  obtain ⟨_, _, B', b', t, eps, _, _, _, P, pobj, kappa, _, _, H, hobj,
    gamma, _, _, hH, alpha, beta, _, _, _, hbeta, E, _, _⟩ :=
      Scheme.Modules.affine_module_correspondence pi
  have : IsIso (beta.app N) := hbeta N hN
  let ea : R.obj (H.obj N) ≅ N := (asIso (beta.app N)).symm
  have hF := hH N hN
  have hFfinite := (Scheme.Modules.affine_module_finite_type pi N hN (H.obj N) hF ea).mp
    hNfinite
  refine ⟨H.obj N, hF, hFfinite, ⟨?_⟩⟩
  exact S.mapIso ea ≪≫ e

end AlgebraicGeometry
