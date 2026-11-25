/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.CechHorseshoeCorrectionCochain

/-! # The local correction in a horseshoe Cech double complex

Source: Stacks Project, Cohomology, Tag 01EQ (total-complex calculation),
and Tag 0B8S (local lifts).
(blueprint: lem-sc-cech-horseshoe-lift-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

local instance instHasLimitsOfShape_cechHorseshoeLiftClass
    (R : Type u) [Ring R] (J : Type*) [Small.{u} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

set_option backward.isDefEq.respectTransparency false in
/-- The images of the local difference cocycle and the global horseshoe cycle agree
in total homology. This is a calculation about alpha and beta, without a cohomology
boundary or a canonical comparison map.
Source: Stacks Project, Cohomology, Tag 01EQ, double-complex proof, and Tag 0B8S.
(blueprint: lem-sc-cech-horseshoe-lift-class).

Proof:
1. On each U_i, aug_B(x_i) minus the restriction of b maps under beta^0 to zero:
the augmentation square, the local lift equation and beta^0(b) = aug_C(q) give this.
Since alpha^0 is a kernel on sections, it lifts uniquely to t_i in IA^0(U_i).
2. On each pairwise intersection, naturality and the augmentation square for alpha
show that the Cech differential of (t_i) is the image of z under aug_A. Cancellation
of the two restrictions of b removes b. Monicity of alpha^0 verifies the equality.
3. The resolution differential of t_i equals minus a restricted to U_i. Apply alpha^1:
d(aug_B(x_i)) = 0 and d(b) = alpha^1(a); then cancel alpha^1, which is monic.
4. Regard (t_i) as the (0,0) summand of the total complex. Its total differential is
beta_A(iCycles z) minus alpha_A(iCycles a), since both signs leaving (0,0) are +1.
A total coboundary has zero homology class, so H(beta_A)[z] = H(alpha_A)[a].
Empty intersections and an empty indexing type cause no exceptions: products and
sectionwise kernel arguments still apply, and all empty products are zero modules. -/
theorem cech_horseshoe_lift_class (X : Scheme.{u})
    (S : ShortComplex X.Modules)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q)
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b)
    (z : ((cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1)
    (hz : ∀ y : Fin 2 → ι,
      S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        ((Pi.π (fun w : Fin 2 → ι ↦
          S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) :
    HomologicalComplex.homologyMap (moduleCechBeta U IA) 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        HomologicalComplex.homologyMap (moduleCechAlpha U IA) 1
          ((RingedSpace.globalSectionsComplex IA).homologyπ 1 a) := by
  obtain ⟨c, hc₁, hc₂⟩ := cech_horseshoe_correction_cochain X S IA IB IC α β hαβ hιA hιB
    hrows U q x hx b a hb ha z hz
  let D := moduleCechDouble U IA
  let T := D.total (ComplexShape.up ℕ)
  let t := D.ιTotal (ComplexShape.up ℕ) 0 0 0 (by simp) c
  have ht : T.d 0 1 t = (moduleCechBeta U IA).f 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) -
      (moduleCechAlpha U IA).f 1
        ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) := by
    have hd : D.ιTotal (ComplexShape.up ℕ) 0 0 0 (by simp) ≫ T.d 0 1 =
        ((D.d 0 1).f 0 ≫ D.ιTotal (ComplexShape.up ℕ) 1 0 1 (by simp)) +
        ((D.X 0).d 0 1 ≫ D.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp)) := by
      rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
        HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
        HomologicalComplex₂.d₁_eq _ _ (by simp : (ComplexShape.up ℕ).Rel 0 1)
          0 1 (by simp),
        HomologicalComplex₂.d₂_eq _ _ 0 (by simp : (ComplexShape.up ℕ).Rel 0 1)
          1 (by simp)]
      simp
    have hd' := ConcreteCategory.congr_hom hd c
    change T.d 0 1 t =
      D.ιTotal (ComplexShape.up ℕ) 1 0 1 (by simp) (((D.d 0 1).f 0) c) +
      D.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp) (((D.X 0).d 0 1) c) at hd'
    rw [hc₁, hc₂, map_neg] at hd'
    change T.d 0 1 t =
      D.ιTotal (ComplexShape.up ℕ) 0 1 1 (by simp)
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (IA.ι.f 0).val)).f 1
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) -
      D.ιTotal (ComplexShape.up ℕ) 1 0 1 (by simp)
        (moduleCechZero U (IA.cocomplex.X 1)
          ((RingedSpace.globalSectionsComplex IA).iCycles 1 a))
    exact hd'.trans ((add_comm _ _).trans (sub_eq_add_neg _ _).symm)
  let cz := HomologicalComplex.cyclesMap (moduleCechBeta U IA) 1 z
  let ca := HomologicalComplex.cyclesMap (moduleCechAlpha U IA) 1 a
  have hc : cz - ca = T.toCycles 0 1 t := by
    apply (ModuleCat.mono_iff_injective (T.iCycles 1)).mp inferInstance
    simp only [map_sub]
    rw [show T.iCycles 1 cz = (moduleCechBeta U IA).f 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) from
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (moduleCechBeta U IA) 1) z]
    rw [show T.iCycles 1 ca = (moduleCechAlpha U IA).f 1
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) from
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (moduleCechAlpha U IA) 1) a]
    rw [show T.iCycles 1 (T.toCycles 0 1 t) = T.d 0 1 t from
      ConcreteCategory.congr_hom (T.toCycles_i 0 1) t]
    exact ht.symm
  have hπ : T.homologyπ 1 cz = T.homologyπ 1 ca := by
    apply sub_eq_zero.mp
    rw [← map_sub, hc]
    exact ConcreteCategory.congr_hom (T.toCycles_comp_homologyπ 0 1) t
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (moduleCechBeta U IA) 1) z).trans
      (hπ.trans (ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality (moduleCechAlpha U IA) 1) a).symm)

end AlgebraicGeometry.Scheme.Modules
