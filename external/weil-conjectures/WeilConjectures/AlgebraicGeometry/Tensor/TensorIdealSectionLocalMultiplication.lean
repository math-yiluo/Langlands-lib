/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection

/-! # Local multiplication in the ideal tensor kernel

Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-tensor-ideal-section-local-multiplication).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

private theorem tensor_unit_tmul {X Z : Scheme.{u}} (j : Z ⟶ X)
    (M N : X.Modules) (U : X.Opens) (z : Γ(M, U)) (x : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
      (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app (M ⊗ N)).app U
        (tmulSection z x)) =
      tmulSection (M := (tensorPullback j).obj M) (N := (tensorPullback j).obj N)
        (U := j ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M).app U z)
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app N).app U x) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  have hn (P : X.Modules) (w : Γ(P, U)) :
      ((boundaryPullbackComparison j).app P).hom.app (j ⁻¹ᵁ U)
        ((adj.unit.app P).app U w) = pullbackUnitApp j P U w :=
    congrArg (fun q ↦ q.app U w)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction j) P)
  simp only [boundaryPullbackTensorIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rw [hn, pullback_δ_app_unit_tmulSection, tensorHom_app_tmulSection]
  rw [← hn M z, ← hn N x]
  rw [inv_app_hom_app_apply_of_iso, inv_app_hom_app_apply_of_iso]

private theorem ideal_tensor_assoc {X : Scheme.{u}} (J M N P : X.Modules)
    (i : J ⟶ 𝟙_ X.Modules) (f : M ⊗ N ⟶ P) :
    (α_ J M N).hom ≫ J ◁ f ≫ i ▷ P ≫ (λ_ P).hom =
      (i ▷ M ≫ (λ_ M).hom) ▷ N ≫ f := by
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← associator_naturality_left_assoc]
  rw [leftUnitor_tensor_hom]
  simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]

/-- The explicit ideal-tensor transport multiplies a kernel section by any local
lift of the quotient section. This is a statement about tensor modules alone;
it contains no graded algebra presentation or quotient action.

Source: Stacks Project, Tag 09MS, coherent-equation-ses, multiplication on the
ideal coefficient; Tag 08KS, the closed-immersion quotient unit.
(blueprint: lem-sc-tensor-ideal-section-local-multiplication).
Proof: Compare the tensor-pullback adjunction unit with the ordinary pullback
unit via boundaryPullbackComparison. The proved formula for the ordinary
pullback cotensorator on section tensors therefore gives the same formula for
boundaryPullbackTensorIso. Set z to the input section transported through the
inverse degree-d ideal-kernel comparison. Naturality of s identifies its value
at 1 over j inverse U with the unit applied to x, by hx. The right unitor inserts
1 and tensoring by s replaces it with this unit image. The inverse tensor
comparison sends the resulting section tensor to the unit of z tensor x.
Naturality of the unit moves the pulled-back associator and degree multiplication
past that unit. Its target inverse cancels, since the ideal tensor is annihilated
by J and its unit is invertible. The defining inclusion equation of the target
kernel comparison now leaves ordinary ideal multiplication. Naturality of the
left unitor and associator identifies this with tensoring the input kernel
inclusion with x and then multiplying degrees d and a. The source comparison's
inclusion equation gives the asserted formula. This is a direct calculation on
U, with no trivialization or choice of further lifts. Degree zero uses the same
unitors, and empty opens and zero sections use the same equations. -/
theorem tensorIdealSection_local_multiplication {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a))
    (U : X.Opens) (x : Γ(L.tensorPow a, U))
    (hx : (tensorGradedUnit j (L.tensorPow a)).app U x =
      ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
        (homOfLE le_top).op (s.app ⊤ (1 : Γ(Z, ⊤))))
    (y : Γ(kernel (tensorGradedUnit j (L.tensorPow d)), U)) :
  let m : (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d) ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow t) :=
    (ρ_ _).inv ≫ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d)) ◁ s ≫
      (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow d)
        (L.tensorPow a)).inv ≫
      (tensorPullback j).map ((α_ _ _ _).hom ≫
        j.ker.toModules ◁ (L.tensorPowAddIso d a).inv ≫
        j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h))
  let _inst := square_zero_ideal_tensor_unit_isIso j L hI t
  let v : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
      kernel (tensorGradedUnit j (L.tensorPow t)) :=
    (boundaryIdealKernelIso j (L.tensorPow d)).inv ≫
    (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow d) ≫
    (pushforward j).map m ≫
    inv ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow t)) ≫
    (boundaryIdealKernelIso j (L.tensorPow t)).hom
  (kernel.ι (tensorGradedUnit j (L.tensorPow t))).app U (v.app U y) =
    (eqToHom (congrArg L.tensorPow h)).app U
      ((L.tensorPowAddIso d a).inv.app U
        (tmulSection ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app U y) x)) := by
  extract_lets m _inst v
  let _ := _inst
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  let Jd := j.ker.toModules ⊗ L.tensorPow d
  let Jt := j.ker.toModules ⊗ L.tensorPow t
  let f : Jd ⊗ L.tensorPow a ⟶ Jt := (α_ _ _ _).hom ≫
    j.ker.toModules ◁ (L.tensorPowAddIso d a).inv ≫
    j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h)
  let z := (boundaryIdealKernelIso j (L.tensorPow d)).inv.app U y
  let q (r : ℕ) : j.ker.toModules ⊗ L.tensorPow r ⟶ L.tensorPow r :=
    j.ker.toModulesι ▷ L.tensorPow r ≫ (λ_ _).hom
  have hι (r : ℕ) : (boundaryIdealKernelIso j (L.tensorPow r)).hom ≫
      kernel.ι (tensorGradedUnit j (L.tensorPow r)) = q r :=
    Classical.choose_spec (boundaryIdealKernelIso_exists j (L.tensorPow r))
  have hv : v ≫ kernel.ι (tensorGradedUnit j (L.tensorPow t)) =
      (boundaryIdealKernelIso j (L.tensorPow d)).inv ≫ adj.unit.app Jd ≫
        (pushforward j).map m ≫ inv (adj.unit.app Jt) ≫ q t := by
    simp only [v, Category.assoc, hι]
    rfl
  have hy : (kernel.ι (tensorGradedUnit j (L.tensorPow d))).app U y = (q d).app U z := by
    have hh : (boundaryIdealKernelIso j (L.tensorPow d)).inv ≫ q d =
        kernel.ι (tensorGradedUnit j (L.tensorPow d)) := by
      rw [← hι d, Iso.inv_hom_id_assoc]
    exact (congrArg (fun k ↦ k.app U y) hh).symm
  change (adj.unit.app (L.tensorPow a)).app U x = _ at hx
  have hs : s.app (j ⁻¹ᵁ U) (unitSectionsEquiv (j ⁻¹ᵁ U) 1) =
      (adj.unit.app (L.tensorPow a)).app U x := by
    rw [hx]
    have hn := Hom.app_presheaf_map s
      ((Opens.map j.base).map (homOfLE le_top : U ⟶ ⊤))
      (unitSectionsEquiv (j ⁻¹ᵁ ⊤) 1)
    have hu : (𝟙_ Z.Modules).presheaf.map
        ((Opens.map j.base).map (homOfLE le_top : U ⟶ ⊤)).op
          (unitSectionsEquiv (j ⁻¹ᵁ ⊤) 1) = unitSectionsEquiv (j ⁻¹ᵁ U) 1 := by
      change Z.presheaf.map
        ((Opens.map j.base).map (homOfLE le_top : U ⟶ ⊤)).op 1 = 1
      exact map_one _
    rw [hu] at hn
    exact hn
  have hm : m.app (j ⁻¹ᵁ U) ((adj.unit.app Jd).app U z) =
      (adj.unit.app Jt).app U (f.app U (tmulSection z x)) := by
    have htens := tensor_unit_tmul j Jd (L.tensorPow a) U z x
    have hnat := congrArg (fun k ↦ k.app U (tmulSection z x)) (adj.unit_naturality f)
    change ((tensorPullback j).map f).app (j ⁻¹ᵁ U)
      ((adj.unit.app (Jd ⊗ L.tensorPow a)).app U (tmulSection z x)) =
        (adj.unit.app Jt).app U (f.app U (tmulSection z x)) at hnat
    dsimp only [m]
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    rw [rightUnitor_inv_app, whiskerLeft_app_tmulSection, hs,
      ← htens, inv_app_hom_app_apply_of_iso]
    exact hnat
  have hf : f ≫ q t = (q d) ▷ L.tensorPow a ≫
      (L.tensorPowAddIso d a).inv ≫ eqToHom (congrArg L.tensorPow h) := by
    simpa only [f, q, whiskerLeft_comp, Category.assoc] using
      ideal_tensor_assoc j.ker.toModules (L.tensorPow d) (L.tensorPow a) (L.tensorPow t)
        j.ker.toModulesι ((L.tensorPowAddIso d a).inv ≫ eqToHom (congrArg L.tensorPow h))
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, hv]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  change (q t).app U ((inv (adj.unit.app Jt)).app U
    (m.app (j ⁻¹ᵁ U) ((adj.unit.app Jd).app U z))) = _
  rw [hm]
  have hcancel : (inv (adj.unit.app Jt)).app U
      ((adj.unit.app Jt).app U (f.app U (tmulSection z x))) =
        f.app U (tmulSection z x) := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, IsIso.hom_inv_id, Hom.id_app]
    rfl
  rw [hcancel, ← ConcreteCategory.comp_apply, ← Hom.comp_app, hf]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [whiskerRight_app_tmulSection, hy]

end
end AlgebraicGeometry.Scheme.Modules
