/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.SheafCoinductionAdjunction
import WeilConjectures.AlgebraicGeometry.AffineInternalHomEvaluationBijective

/-!
# Affine sheaf-Hom is right adjoint to restriction

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine
(blueprint: lem-sc-finite-sheafhom-affine).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- For an affine `f : Y ⟶ X`, internal Hom from `f_* O_Y`, with its canonical
`f_* O_Y`-action, is right adjoint to restriction of scalars. Its sections on an
affine open are the module Hom of sections, and its counit evaluates at one.

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine;
Modules, lemma-adjoint-tensor-restrict (blueprint: lem-sc-finite-sheafhom-affine).

Proof, step 1 (def-pur-sheaf-hom). For an A-module G and an O_X-module F, send
an A-linear map psi : G -> Hom(A,F) to m -> psi(m)(1). Conversely send g to
m -> (s -> g(s*m)), on every smaller open. These assignments commute with
restriction and are mutually inverse, since psi(m)(s) = psi(s*m)(1).
They are natural in G and F and give the adjunction; the identity on Hom(A,F)
gives the counit phi -> phi(1). The A-action is precomposition by multiplication.
Step 2 (lem-pc-affine-morphism-hi, lem-weil-pbc-affine-tilde-gamma-adjunction).
Since f is affine, A = f_* O_Y is quasi-coherent. On an affine open U, A|_U is
the sheaf associated to S = O_Y(f^{-1} U). The tilde/global-sections adjunction,
valid for every F, identifies Hom(A|_U,F|_U) with Hom_R(S,F(U)) by taking
components at U. Thus no quasi-coherence or finite presentation of F is needed.
Under this identification the counit is evaluation at 1 in S. -/
theorem sheafHom_affine_rightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∃ H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A,
      ∃ i : H ⋙ T ≅ K, ∃ adj : T ⊣ H,
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
          (W : Over U) (b : A.obj.obj (op W.left)),
          (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
            (((i.hom.app F).val.app (op U)).hom φ).app (op W)
              (A.obj.map W.hom.op a * b)) ∧
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (φ : (H.obj F).val.obj (op U)),
          ((adj.counit.app F).val.app (op U)).hom φ =
            ((((i.hom.app F).val.app (op U)).hom φ).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U))) ∧
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens),
          IsAffineOpen U →
          ∃ e : (SheafOfModules.homObj M F).val.obj (op U) ≃ₗ[X.presheaf.obj (op U)]
            (M.val.obj (op U) →ₗ[X.presheaf.obj (op U)] F.val.obj (op U)),
            ∀ (φ : (SheafOfModules.homObj M F).val.obj (op U))
              (s : M.val.obj (op U)),
              e φ s = (φ.app (op (Over.mk (𝟙 U)))).hom s) := by
  dsimp only
  obtain ⟨H, i, adj, haction, hcounit⟩ := sheafHom_restrictScalars_adjunction f
  refine ⟨H, i, adj, haction, hcounit, ?_⟩
  intro F U hU
  let M := (SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom).obj
    (SheafOfModules.unit
      (((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
        RingCat.{u} _ _).obj Y.ringCatSheaf))
  have hM : M.IsQuasicoherent := by
    change ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent
    have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_unit.{u, u, u}
    exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f _
  let ev : (SheafOfModules.homObj M F).val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      (M.val.obj (op U) →ₗ[X.presheaf.obj (op U)] F.val.obj (op U)) :=
    { toFun := fun φ ↦ (φ.app (op (Over.mk (𝟙 U)))).hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ by
        ext s
        rw [PresheafOfModules.smul_app (R := X.presheaf) r φ (op (Over.mk (𝟙 U)))]
        change X.presheaf.map (𝟙 U).op r •
          ((φ.app (op (Over.mk (𝟙 U)))).hom s : F.val.obj (op U)) =
          r • ((φ.app (op (Over.mk (𝟙 U)))).hom s : F.val.obj (op U))
        simp }
  exact ⟨LinearEquiv.ofBijective ev (affine_internalHom_evaluation_bijective M F U hU),
    fun _ _ ↦ rfl⟩

end AlgebraicGeometry
