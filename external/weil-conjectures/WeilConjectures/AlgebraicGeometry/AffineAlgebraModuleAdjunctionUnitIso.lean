/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorHomBijective
/-! # Canonical affine algebra module adjunction component

Source: Stacks Project, Tags 0AVW and 01SB. -/

@[expose] public section

noncomputable section
universe v
open CategoryTheory
namespace AlgebraicGeometry

private theorem adjunction_of_unit_formula
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (R : D ⥤ C)
    (β : 𝟭 C ⟶ H ⋙ R)
    (e : ∀ M K, (H.obj M ⟶ K) ≃ (M ⟶ R.obj K))
    (he : ∀ M K a, e M K a = β.app M ≫ R.map a) :
    ∃ adj : H ⊣ R, ∀ M, adj.unit.app M = β.app M := by
  let core : Adjunction.CoreHomEquiv H R :=
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro M' M K a q
        apply (e M' K).injective
        rw [Equiv.apply_symm_apply, he, R.map_comp, ← Category.assoc]
        change _ = (β.app M' ≫ (H ⋙ R).map a) ≫ _
        rw [← β.naturality a, Category.assoc]
        change _ = a ≫ (β.app M ≫ R.map ((e M K).symm q))
        rw [← he, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M K K' a q
        simp only [he, R.map_comp, Category.assoc] }
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro M
  rw [Adjunction.mkOfHomEquiv_unit_app]
  change e M (H.obj M) (𝟙 _) = _
  simp [he]

/-- The canonical affine algebra adjunction component.
Source: Stacks Project, Tags 0AVW and 01SB.
(blueprint: new-affine-algebra-module-unit-iso).

Proof: Identify the canonical left adjoint with tensor pullback for g by its Hom adjunction.
Associativity identifies this pullback with the two tensor operations in the affine module
correspondence. Its unit is beta: both are adjoint to the tensor unit s mapped to s tensor 1.
The correspondence proves beta invertible on quasi-coherent algebra modules. Transport the unit
across the unique adjunction-compatible isomorphism of left adjoints; its image under G is
invertible too. The same tensor calculation covers zero rings and modules.
-/
theorem affine_algebra_module_adjunction_unit_iso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [(RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).IsRightAdjoint] :
    ∀ M : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)),
      M.IsQuasicoherent → IsIso
        ((Adjunction.ofIsRightAdjoint
          (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).unit.app M) := by
  classical
  let A := (TopCat.Sheaf.pushforward CommRingCat.{v} f.base).obj X.sheaf
  let RA := (sheafCompose _ (forget₂ CommRingCat.{v} RingCat.{v})).obj A
  let R := SheafOfModules.pushforward.{v} (F := TopologicalSpace.Opens.map f.base)
    (S := RA) (R := X.ringCatSheaf) (𝟙 RA)
  obtain ⟨_, _, B, b, t, ε, hp, hb, ht, P, pobj, κ, hmapP, hunitP,
    H, hobj, γ, hmapH, hunitH, hqc, α, β, hα, hβ, hisoα, hisoβ, hE⟩ :=
    Scheme.Modules.affine_module_correspondence f
  have bijective := Scheme.Modules.affine_module_tensor_hom_bijective f B b t ε ht
    P pobj κ H hobj γ hunitP hunitH β hβ
  let e (M : SheafOfModules.{v} RA) (K : X.Modules) :
      (H.obj M ⟶ K) ≃ (M ⟶ R.obj K) :=
    Equiv.ofBijective (fun a ↦ β.app M ≫ R.map a) (bijective M K)
  obtain ⟨a, unit_eq⟩ := adjunction_of_unit_formula H R β e (fun _ _ _ ↦ rfl)
  intro M hM
  have : IsIso (a.unit.app M) := by
    rw [unit_eq]
    exact hisoβ M hM
  change IsIso ((Adjunction.ofIsRightAdjoint R).unit.app M)
  rw [← a.unit_leftAdjointUniq_hom_app (Adjunction.ofIsRightAdjoint R) M]
  infer_instance

end AlgebraicGeometry
