/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ConcreteCategory
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
@[expose] public section
universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The snake formula evaluated on cycles, with the cycle representatives already chosen. -/
private theorem boundaryHorseshoe_delta_apply {R : Type u} [Ring R]
    (H : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hH : H.ShortExact)
    (z : H.X₃.cycles 0) (b : H.X₂.X 0) (a : H.X₁.cycles 1)
    (hb : H.g.f 0 b = H.X₃.iCycles 0 z)
    (ha : H.f.f 1 (H.X₁.iCycles 1 a) = H.X₂.d 0 1 b) :
    hH.δ 0 1 rfl (H.X₃.homologyπ 0 z) = H.X₁.homologyπ 1 a := by
  have hzero : H.X₃.d 0 1 (H.X₃.iCycles 0 z) = 0 :=
    congrArg (fun f ↦ f z) (H.X₃.iCycles_d 0 1)
  have hsnake := hH.δ_apply 0 1 rfl (H.X₃.iCycles 0 z) hzero b hb
    (H.X₁.iCycles 1 a) ha 2 ((ComplexShape.up ℕ).next_eq' rfl)
  have hza : H.X₃.cyclesMk (H.X₃.iCycles 0 z) 1
      ((ComplexShape.up ℕ).next_eq' rfl) hzero = z := by
    apply (Preadditive.mono_iff_injective (H.X₃.iCycles 0)).1 inferInstance
    rw [HomologicalComplex.i_cyclesMk]
    rfl
  have haa : H.X₁.cyclesMk (H.X₁.iCycles 1 a) 2 ((ComplexShape.up ℕ).next_eq' rfl)
      (ShortComplex.ShortExact.d_eq_zero_of_f_eq_d_apply hH 0 1 b
        (H.X₁.iCycles 1 a) ha 2) = a := by
    apply (Preadditive.mono_iff_injective (H.X₁.iCycles 1)).1 inferInstance
    rw [HomologicalComplex.i_cyclesMk]
    rfl
  rw [hza, haa] at hsnake
  exact hsnake

-- Comparing X.Modules with module sheaves makes the isomorphism transports expensive.
set_option backward.isDefEq.respectTransparency false in
/-- The snake boundary of the global horseshoe equals the derived-triangle boundary.
Source: Stacks Project, Tags 0117, 013T and 015B.
(blueprint: stage3-boundary-identification).

Proof: Split the resolution rows using injectivity of IA in each degree and apply
additive global sections, obtaining a short exact sequence of global complexes.
The augmentation of q is a degree-zero cocycle. The two displayed equalities
are exactly the lifting equalities in the concrete snake formula; that formula
sends its homology class to the class of a. The degree-zero resolution comparison
sends toRightDerivedZero(q) to the class of its augmentation. Apply the horseshoe
comparison of rightDerived_triangle_connecting to these compatible resolutions:
its first equality identifies the snake map transported by isoRightDerivedObj,
and its second identifies the same map with the boundary of the derived image
of the canonical short-exact-sequence triangle. The latter, transported by the
single-object comparison isomorphisms, is moduleCohomologyBoundary by definition.
Compose the comparison equalities and cancel the degree-one isomorphism to obtain
the stated equality. It holds for every permitted lift: changing b changes a
by a boundary, so its homology class is unchanged. For q = 0 that class is zero,
and zero objects introduce no exception. -/
theorem boundary_horseshoe_boundary_identification (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [EnoughInjectives X.Modules]
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    (S : ShortComplex X.Modules) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    (hS : S.ShortExact) (q : S.X₃.val.obj (op ⊤))
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b) :
    (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).hom
      (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q)) =
      (RingedSpace.globalSectionsComplex IA).homologyπ 1 a := by
  let v : X.Modules ⥤
      ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : HasDerivedCategory.{wC} X.Modules :=
    inferInstanceAs (HasDerivedCategory.{wC}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : PreservesFiniteLimits v :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  obtain ⟨G, hF, hhorse, htriangle⟩ := rightDerived_triangle_connecting v
  rcases G with ⟨F, add, delta, mono, exm, exr, exl, nat⟩
  dsimp only at hF
  subst F
  dsimp only at hhorse htriangle
  obtain ⟨hH, hδ⟩ := hhorse S hS IA IB IC α β hαβ hιA hιB hrows
  have ht := htriangle S hS 0
  have hd := hδ 0
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at ht hd
  have hcompare : RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0 ≫
      (IA.isoRightDerivedObj v 1).hom =
      (IC.isoRightDerivedObj v 0).hom ≫ hH.δ 0 1 rfl := by
    apply (cancel_mono (IA.isoRightDerivedObj v 1).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    erw [← hd]
    apply (cancel_mono
      (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso S.X₁ 1).inv).1
    erw [ht]
    simp only [RingedSpace.moduleCohomologyBoundary,
      Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Category.assoc]
    dsimp only [v]
    erw [Iso.hom_inv_id, Category.comp_id]
  let H := (ShortComplex.mk α β hαβ).map
    (v.mapHomologicalComplex (ComplexShape.up ℕ))
  let z := IC.toRightDerivedZero' v q
  have hz : H.X₃.iCycles 0 z = (IC.ι.f 0).val.app (op ⊤) q := by
    change (IC.toRightDerivedZero' v ≫ H.X₃.iCycles 0) q = _
    erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rfl
  have hsnake := boundaryHorseshoe_delta_apply H hH z b a (hb.trans hz.symm) ha
  have haug : v.toRightDerivedZero.app S.X₃ ≫ (IC.isoRightDerivedObj v 0).hom =
      IC.toRightDerivedZero' v ≫ H.X₃.homologyπ 0 := by
    erw [IC.toRightDerivedZero_eq v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  change ((v.toRightDerivedZero.app S.X₃ ≫
    RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0) ≫
      (IA.isoRightDerivedObj v 1).hom) q = _
  erw [Category.assoc, hcompare, ← Category.assoc, haug]
  exact hsnake
end AlgebraicGeometry.Scheme.Modules
