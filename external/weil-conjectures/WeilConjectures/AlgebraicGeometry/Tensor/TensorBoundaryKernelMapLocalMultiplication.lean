/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorBoundaryKernelMapNaturality
import WeilConjectures.AlgebraicGeometry.BoundaryCoefficientTensorProduct
import WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorUnit

/-! # Local tensor multiplication under the canonical kernel comparisons

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its ideal coefficient.
(blueprint: lem-sc-tensor-boundary-kernel-map-local-multiplication).
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
private theorem ideal_product_inclusion {X : Scheme.{u}} (J A B C : X.Modules)
    (i : J ⟶ 𝟙_ X.Modules) (p : A ⊗ B ⟶ C) :
    (α_ A J B).inv ≫ (β_ A J).hom ▷ B ≫ (α_ J A B).hom ≫ J ◁ p ≫
        i ▷ C ≫ (λ_ C).hom =
      A ◁ (i ▷ B ≫ (λ_ B).hom) ≫ p := by
  rw [MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.leftUnitor_naturality,
    ← MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    ← BraidedCategory.braiding_naturality_right,
    MonoidalCategory.comp_whiskerRight_assoc,
    CategoryTheory.braiding_tensorUnit_right]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality_middle_assoc]
  simp only [← Category.assoc]
  congr 1
  monoidal

private theorem whiskerLeft_section {Z : Scheme.{u}} (F N : Z.Modules)
    (x : 𝟙_ Z.Modules ⟶ N) (V : Z.Opens) (s : Γ(F ⊗ 𝟙_ Z.Modules, V)) :
    (F ◁ x).app V s =
      tmulSection ((ρ_ F).hom.app V s) (x.app V (unitSectionsEquiv V 1)) := by
  have h := inv_app_hom_app_apply_of_iso (ρ_ F) s
  conv_lhs => rw [← h, rightUnitor_inv_app]
  exact whiskerLeft_app_tmulSection _ _ _

/-- In a local lift of a homogeneous quotient section, the transported
kernel map is ordinary tensor multiplication after the kernel inclusion.
There is no graded presentation, ring action or degree projection in this statement.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and the identification
of its ideal coefficient over Z; Modules, Tag 08KS, the closed-immersion quotient.
(blueprint: lem-sc-tensor-boundary-kernel-map-local-multiplication).
Proof: It suffices by sheaf separation to work on an open trivializing L, and
then on a refinement lifting the restricted quotient section. Write ell^r for
the recursively parenthesized tensor of a local generator ell in degree r;
ell^0 is the tensor unit section. The inclusion equation in
boundaryIdealKernelIso identifies a degree-n kernel section y with r ell^n
for a section r of J. Write t=a ell^(n(e+1)). The map in the conclusion has
source and target kernel comparisons made of three factors. The first factor,
the inverse ideal-kernel isomorphism, sends y to r ell^n by its inclusion
equation. The second, the annihilated-module adjunction unit, sends this to
the class of r ell^n over Z. The third, boundaryCoefficientDegreeIso at zero,
sends it to the same coefficient tensored with the degree-zero unit.
Tensoring by x changes this to the class of ar times the coefficient tensor
ell^(n(e+1)). Inverting the three target factors gives ar ell^(n(e+2)).
For the tensor identifications, induction on each exponent in
boundaryPullbackPowIso sends ell^q to the tensor of q copies of the image
of ell: the zero case is pullbackObjUnitIso, and the successor case is
boundaryPullbackTensorIso followed by the induction hypothesis. Induction
on e in tensorPowMulIso and its associators identifies blocks of n copies
with n(e+1) copies. The same inductions in boundaryCoefficientDegreeIso
leave the J factor fixed and repartition the L factors. Thus every displayed
factor sends the stated generator tensor to the stated generator tensor,
with the right and left unitors at exponent zero. This proves equality
with the tensorPowAddIso product on the right. A change of lift changes a
by an element of J; its product with r vanishes since J^2=0. The local
equalities agree on overlaps and give the asserted equality on U, including
n=0, e=0, the zero section, the zero ideal and the empty open. -/
theorem tensorBoundaryKernelMap_local_multiplication {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (U : X.Opens) (t : Γ(L.tensorPow (n * (e + 1)), U))
    (ht : (tensorGradedUnit j (L.tensorPow (n * (e + 1)))).app U t =
      ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow (n * (e + 1))))).val.map
        (homOfLE le_top).op
          ((x ≫ (boundarySectionDegreeIso j L n e).inv).app ⊤ (1 : Γ(Z, ⊤))))
    (y : Γ(kernel (tensorGradedUnit j (L.tensorPow (n * (0 + 1)))), U)) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    (kernel.ι (tensorGradedUnit j (L.tensorPow (n * ((e + 1) + 1))))).app U
        ((tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)).app U y) =
      (eqToHom (by congr 1; simp only [Nat.mul_add, Nat.mul_one, Nat.zero_add]) :
        L.tensorPow (n * (e + 1) + n * (0 + 1)) ⟶
          L.tensorPow (n * ((e + 1) + 1))).app U
        ((L.tensorPowAddIso (n * (e + 1)) (n * (0 + 1))).inv.app U
          (tmulSection t
            ((kernel.ι (tensorGradedUnit j (L.tensorPow (n * (0 + 1))))).app U y))) := by
  let J := j.ker.toModules
  let a := n * (e + 1)
  let b := n * (0 + 1)
  let c := n * ((e + 1) + 1)
  let V := j ⁻¹ᵁ U
  let F : Z.Modules := (tensorPullback j).obj (J ⊗ L.tensorPow n)
  let ks := boundaryIdealKernelIso j (L.tensorPow b)
  let kt := boundaryIdealKernelIso j (L.tensorPow c)
  let z : Γ(J ⊗ L.tensorPow b, U) := ks.inv.app U y
  let d : L.tensorPow (a + b) ⟶ L.tensorPow c :=
    eqToHom (by dsimp [a, b, c]; congr 1; simp only [Nat.mul_add, Nat.mul_one])
  let m := boundaryIdealTensorProduct J L a b ≫ J ◁ d
  let p : Γ(J ⊗ L.tensorPow c, U) := m.app U (tmulSection t z)
  let η := (Classical.choose (exists_tensorPullbackAdjunction j)).unit
  let q : Γ((tensorPullback j).obj (L.tensorPow a), V) := (η.app _).app U t
  let s : Γ((tensorPullback j).obj (J ⊗ L.tensorPow b), V) := (η.app _).app U z
  have hz : ks.hom.app U z = y := inv_app_hom_app_apply_of_iso ks.symm y
  have hs : (boundaryPullbackTensorIso j (L.tensorPow a)
      (J ⊗ L.tensorPow b)).hom.app V ((η.app _).app U (tmulSection t z)) =
      tmulSection q s := boundaryPullbackTensorIso_unit_tmul j _ _ U t z
  have hp : (η.app _).app U p = ((tensorPullback j).map m).app V
      ((boundaryPullbackTensorIso j (L.tensorPow a)
        (J ⊗ L.tensorPow b)).inv.app V (tmulSection q s)) := by
    have hn := congrArg (fun f ↦ f.app U (tmulSection t z)) (η.naturality m)
    have hh := congrArg
      ((boundaryPullbackTensorIso j (L.tensorPow a) (J ⊗ L.tensorPow b)).inv.app V) hs
    rw [inv_app_hom_app_apply_of_iso] at hh
    exact hn.trans (congrArg (((tensorPullback j).map m).app V) hh)
  have hq : (boundarySectionDegreeIso j L n e).hom.app V q =
      x.app V (unitSectionsEquiv V 1) := by
    change (boundarySectionDegreeIso j L n e).hom.app V
      ((tensorGradedUnit j (L.tensorPow a)).app U t) = _
    rw [ht]
    change (boundarySectionDegreeIso j L n e).hom.app V
      (((tensorPullback j).obj (L.tensorPow a)).presheaf.map (homOfLE le_top).op
        ((x ≫ (boundarySectionDegreeIso j L n e).inv).app ⊤ (1 : Γ(Z, ⊤)))) = _
    erw [Hom.app_presheaf_map]
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    erw [inv_app_hom_app_apply_of_iso (boundarySectionDegreeIso j L n e).symm]
    erw [← Hom.app_presheaf_map x]
    change x.app V (Z.presheaf.map (homOfLE le_top).op 1) = _
    rw [map_one]
    rfl
  have hc : (boundaryCoefficientDegreeIso j L n (e + 1)).hom.app V
      ((η.app _).app U p) =
      (F ◁ x).app V ((boundaryCoefficientDegreeIso j L n 0).hom.app V s) := by
    rw [hp]
    have h := boundaryCoefficientDegreeIso_tensor_product j L n e V q s
    change _ = _ at h
    rw [h, hq, whiskerLeft_section]
  have hk : (tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)).app U y =
      kt.hom.app U p := by
    let ts := tensorBoundaryKernelPushforwardIso j L hI n 0
    let tt := tensorBoundaryKernelPushforwardIso j L hI n (e + 1)
    have hts : ts.hom.app U y = (boundaryCoefficientDegreeIso j L n 0).hom.app V s := by
      simp only [ts, tensorBoundaryKernelPushforwardIso, Iso.trans_hom, Iso.symm_hom,
        asIso_hom, Functor.mapIso_hom, Hom.comp_app, ConcreteCategory.comp_apply]
      rfl
    have htt : tt.hom.app U (kt.hom.app U p) =
        (boundaryCoefficientDegreeIso j L n (e + 1)).hom.app V ((η.app _).app U p) := by
      simp only [tt, tensorBoundaryKernelPushforwardIso, Iso.trans_hom, Iso.symm_hom,
        asIso_hom, Functor.mapIso_hom, Hom.comp_app, ConcreteCategory.comp_apply]
      change (boundaryCoefficientDegreeIso j L n (e + 1)).hom.app V
        ((η.app _).app U (kt.inv.app U (kt.hom.app U p))) = _
      rw [inv_app_hom_app_apply_of_iso]
    have hcomm : tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x) ≫ tt.hom =
        ts.hom ≫ (pushforward j).map (F ◁ x) := by
      simp only [tt, ts, tensorBoundaryKernelMap, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    apply (bijective_app_of_iso tt U).injective
    have hh := congrArg (fun f ↦ f.app U y) hcomm
    change tt.hom.app U
      ((tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)).app U y) =
        (((pushforward j).map (F ◁ x)).app U (ts.hom.app U y)) at hh
    exact hh.trans ((congrArg (((pushforward j).map (F ◁ x)).app U) hts).trans
      (hc.symm.trans htt.symm))
  have hi : (kt.hom ≫ kernel.ι (tensorGradedUnit j (L.tensorPow c))) =
      j.ker.toModulesι ▷ L.tensorPow c ≫ (λ_ _).hom := by
    simpa only [kt, boundaryIdealKernelIso, tensorGradedUnit] using
      Classical.choose_spec (boundaryIdealKernelIso_exists j (L.tensorPow c))
  have hi₀ : (ks.hom ≫ kernel.ι (tensorGradedUnit j (L.tensorPow b))) =
      j.ker.toModulesι ▷ L.tensorPow b ≫ (λ_ _).hom := by
    simpa only [ks, boundaryIdealKernelIso, tensorGradedUnit] using
      Classical.choose_spec (boundaryIdealKernelIso_exists j (L.tensorPow b))
  change (kernel.ι (tensorGradedUnit j (L.tensorPow c))).app U
    ((tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)).app U y) = _
  rw [hk]
  change (kt.hom ≫ kernel.ι (tensorGradedUnit j (L.tensorPow c))).app U p = _
  rw [hi]
  have hm : m ≫ (j.ker.toModulesι ▷ L.tensorPow c ≫ (λ_ _).hom) =
      L.tensorPow a ◁ (j.ker.toModulesι ▷ L.tensorPow b ≫ (λ_ _).hom) ≫
        (L.tensorPowAddIso a b).inv ≫ d := by
    dsimp [m, boundaryIdealTensorProduct]
    simp only [← whiskerLeft_comp, Category.assoc]
    exact ideal_product_inclusion J _ _ _ j.ker.toModulesι _
  change (m ≫ (j.ker.toModulesι ▷ L.tensorPow c ≫ (λ_ _).hom)).app U
    (tmulSection t z) = _
  rw [hm]
  let g := j.ker.toModulesι ▷ L.tensorPow b ≫ (λ_ _).hom
  have hiy : g.app U z =
      (kernel.ι (tensorGradedUnit j (L.tensorPow b))).app U y := by
    calc
      g.app U z = (ks.hom ≫ kernel.ι (tensorGradedUnit j (L.tensorPow b))).app U z :=
        congrArg (fun f ↦ f.app U z) hi₀.symm
      _ = (kernel.ι (tensorGradedUnit j (L.tensorPow b))).app U y := by
        change (kernel.ι (tensorGradedUnit j (L.tensorPow b))).app U
          (ks.hom.app U z) = _
        rw [hz]
  change d.app U ((L.tensorPowAddIso a b).inv.app U
      ((L.tensorPow a ◁ g).app U (tmulSection t z))) =
    d.app U ((L.tensorPowAddIso a b).inv.app U
      (tmulSection t ((kernel.ι (tensorGradedUnit j (L.tensorPow b))).app U y)))
  exact congrArg (fun w : Γ(L.tensorPow a ⊗ L.tensorPow b, U) ↦
    d.app U ((L.tensorPowAddIso a b).inv.app U w))
      ((whiskerLeft_app_tmulSection g t z).trans (congrArg (tmulSection t) hiy))

end
end AlgebraicGeometry.Scheme.Modules
