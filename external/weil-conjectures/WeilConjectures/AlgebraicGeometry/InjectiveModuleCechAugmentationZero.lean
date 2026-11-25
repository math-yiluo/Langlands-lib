/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.Topology.Sheaves.CechComparison

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero part of the augmented Čech quasi-isomorphism.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EP.
(blueprint: lem-sc-injective-module-cech-augmentation-zero)

Proof: identify categorical products of opens with their finite intersections
and products of modules with families of sections. The differential from degree
zero to degree one sends a family to the difference of its restrictions on each
pairwise intersection. Its kernel therefore consists precisely of compatible
families. The sheaf gluing axiom gives a unique section on the union for every
such family. The union is X by hU, so restriction from J(X) to this kernel is
bijective and linear. There are no incoming boundaries in either degree-zero
complex. The source's zero homology is its sole term; the target's zero homology
is the kernel just described. The equality ht identifies the global-section
scalar restriction with the identity, and hb identifies the induced homology
map with restriction. Thus it is an isomorphism. This argument does not need
injectivity. If the cover is empty, hU forces X to be empty; the empty-cover
sheaf axiom gives J(X) = 0, and the target is the empty product, also zero. -/
theorem injectiveModuleCechAugmentation_quasiIsoAt_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (J : X.Modules) [Injective J]
    (ht : (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom =
      RingHom.id Γ(X, ⊤))
    (b : (CochainComplex.single₀ (ModuleCat.{u} Γ(X, ⊤))).obj
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj J) ⟶
      (CategoryTheory.cechComplexFunctor U).obj J.presheafModuleCat)
    (hb : b.f 0 =
      (ModuleCat.restrictScalarsId'App
        (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht
        (J.val.obj (op ⊤))).inv ≫
      Pi.lift fun y : Fin 1 → ι =>
        J.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l => U (y l)))).op) :
    QuasiIsoAt b 0 := by
  let P := J.presheafModuleCat
  let K := (CategoryTheory.cechComplexFunctor U).obj P
  let e := ModuleCat.restrictScalarsId'App
    (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op ⊤))).hom ht (J.val.obj (op ⊤))
  let r : P.obj (op ⊤) ⟶ K.X 0 := Pi.lift fun y : Fin 1 → ι ↦
    P.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (y l)))).op
  have hglue (c : K.X 0) (hc : K.d 0 1 c = 0) :
      ∃ s : P.obj (op ⊤), r s = c := by
    classical
    let π := TopCat.Presheaf.cechComplexFunctorπ (X := X.toTopCat) U P
    let sf (i : ι) : P.obj (op (U i)) :=
      P.map (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).op (π 0 (fun _ ↦ i) c)
    let F := (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf
      (op ⊤) isTerminalTop.op).obj J
    let G : TopCat.Sheaf (ModuleCat.{u} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, F.property⟩
    have hcompat : TopCat.Presheaf.IsCompatible G.obj U sf := by
      intro i j
      let y : Fin 2 → ι := Fin.cons i (fun _ ↦ j)
      let q : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (y l)) :=
        Pi.lift (Fin.cases (Opens.infLELeft (U i) (U j))
          (fun _ ↦ Opens.infLERight (U i) (U j)))
      have he := congrArg (fun z ↦ P.map q.op (π 1 y z)) hc
      change P.map q.op (π 1 y (((cechComplexFunctor U).obj P).d 0 1 c)) = _ at he
      rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply] at he
      change P.map q.op (∑ x : Fin 2, (-1 : ℤ) ^ x.val •
        P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (x.succAbove l)).op
          (π 0 (y ∘ x.succAbove) c)) = P.map q.op (π 1 y 0) at he
      simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul,
        Fin.val_one, pow_one, neg_smul, map_add, map_neg, map_zero] at he
      have ht0 : y ∘ (0 : Fin 2).succAbove = (fun _ ↦ j) := by
        funext k
        fin_cases k
        rfl
      have ht1 : y ∘ (1 : Fin 2).succAbove = (fun _ ↦ i) := by
        funext k
        fin_cases k
        rfl
      have transport {a b : Fin 1 → ι} (hab : a = b)
          (f : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (a l)))
          (g : U i ⊓ U j ⟶ ∏ᶜ (fun l ↦ U (b l))) :
          P.map f.op (π 0 a c) = P.map g.op (π 0 b c) := by
        subst b
        rw [Subsingleton.elim f g]
      have face0 : P.map q.op
          (P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l))
            ((0 : Fin 2).succAbove l)).op (π 0 (y ∘ (0 : Fin 2).succAbove) c)) =
          P.map (Opens.infLERight (U i) (U j)).op (sf j) := by
        let f : (∏ᶜ fun l ↦ U (y l)) ⟶
            ∏ᶜ (fun l ↦ U ((y ∘ (0 : Fin 2).succAbove) l)) :=
          Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) ((0 : Fin 2).succAbove l)
        let g : U i ⊓ U j ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U j) :=
          Opens.infLERight (U i) (U j) ≫ Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U j))
        exact (TopCat.Presheaf.map_map_apply P f.op q.op (q ≫ f).op
          (π 0 (y ∘ (0 : Fin 2).succAbove) c)).trans
            ((transport ht0 (q ≫ f) g).trans
              (TopCat.Presheaf.map_map_apply P
                (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U j))).op
                (Opens.infLERight (U i) (U j)).op g.op (π 0 (fun _ ↦ j) c)).symm)
      have face1 : P.map q.op
          (P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l))
            ((1 : Fin 2).succAbove l)).op (π 0 (y ∘ (1 : Fin 2).succAbove) c)) =
          P.map (Opens.infLELeft (U i) (U j)).op (sf i) := by
        let f : (∏ᶜ fun l ↦ U (y l)) ⟶
            ∏ᶜ (fun l ↦ U ((y ∘ (1 : Fin 2).succAbove) l)) :=
          Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) ((1 : Fin 2).succAbove l)
        let g : U i ⊓ U j ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) :=
          Opens.infLELeft (U i) (U j) ≫ Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))
        exact (TopCat.Presheaf.map_map_apply P f.op q.op (q ≫ f).op
          (π 0 (y ∘ (1 : Fin 2).succAbove) c)).trans
            ((transport ht1 (q ≫ f) g).trans
              (TopCat.Presheaf.map_map_apply P
                (Pi.lift (fun _ : Fin 1 ↦ 𝟙 (U i))).op
                (Opens.infLELeft (U i) (U j)).op g.op (π 0 (fun _ ↦ i) c)).symm)
      rw [face0, face1] at he
      exact (add_neg_eq_zero.mp he).symm
    obtain ⟨s, hs, _⟩ := G.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
      (by rw [hU]) sf hcompat
    refine ⟨s, ?_⟩
    apply TopCat.Presheaf.cechComplexFunctor_ext (X := X.toTopCat) U P
    intro y
    have hy : y = (fun _ ↦ y 0) := by
      funext k
      fin_cases k
      rfl
    obtain ⟨i, rfl⟩ : ∃ i, y = (fun _ ↦ i) := ⟨y 0, hy⟩
    have h := congrArg (fun z ↦ P.map (Pi.π (fun _ : Fin 1 ↦ U i) 0).op z) (hs i)
    change P.map (Pi.π (fun _ : Fin 1 ↦ U i) 0).op
      (P.map (homOfLE le_top).op s) = _ at h
    dsimp only [sf] at h
    rw [TopCat.Presheaf.map_map_apply P _ _ (𝟙 _),
      P.map_id, ConcreteCategory.id_apply] at h
    rw [TopCat.Presheaf.map_map_apply P _ _ (homOfLE le_top).op] at h
    have hr : (Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) ≫
        Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i) =
        P.map (homOfLE le_top).op := Pi.lift_comp_π _ _
    change (Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))))
      (fun _ ↦ i) ((Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) s) = _
    rw [← ConcreteCategory.comp_apply]
    change ((Pi.lift (fun y : Fin 1 → ι ↦ P.map (homOfLE le_top).op)) ≫
        Pi.π (fun y : Fin 1 → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i)) s = _
    rw [hr]
    exact h
  have hmono : Mono r := by
    apply (ModuleCat.mono_iff_injective r).mpr
    intro s t hst
    let F := (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤) isTerminalTop.op).obj J
    have hF : TopCat.Presheaf.IsSheaf (X := X.toTopCat) F.obj := F.property
    let G : TopCat.Sheaf (ModuleCat.{u} Γ(X, ⊤)) X.toTopCat := ⟨F.obj, hF⟩
    apply G.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU]) s t
    intro i
    have hi := congrArg
      (fun z ↦ (Pi.π (fun y : Fin 1 → ι ↦
        P.obj (op (∏ᶜ fun l ↦ U (y l))))) (fun _ ↦ i) z) hst
    have hi' : P.map (homOfLE (le_top (a := ∏ᶜ fun _ : Fin 1 ↦ U i))).op s =
        P.map (homOfLE (le_top (a := ∏ᶜ fun _ : Fin 1 ↦ U i))).op t := by
      have hr : r ≫ Pi.π (fun y : Fin 1 → ι ↦
          P.obj (op (∏ᶜ fun l ↦ U (y l)))) (fun _ ↦ i) =
          P.map (homOfLE le_top).op := Pi.lift_comp_π _ _
      exact (ConcreteCategory.congr_hom hr s).symm.trans
        (hi.trans (ConcreteCategory.congr_hom hr t))
    have hq : U i ⟶ ∏ᶜ (fun _ : Fin 1 ↦ U i) := Pi.lift fun _ ↦ 𝟙 _
    have he := congrArg (fun z ↦ P.map hq.op z) hi'
    change P.map (homOfLE le_top).op s = P.map (homOfLE le_top).op t
    simpa only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
      Subsingleton.elim (hq ≫ homOfLE le_top) (homOfLE le_top)] using he
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ rfl rfl (K.shape _ _ (by simp))]
  constructor
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    obtain ⟨s, hs⟩ := hglue c hc
    refine ⟨e.hom s, ?_⟩
    change b.f 0 (e.hom s) = c
    rw [hb]
    change (e.inv ≫ r) (e.hom s) = c
    rw [← ConcreteCategory.comp_apply, e.hom_inv_id_assoc]
    exact hs
  · change Mono (b.f 0)
    rw [hb]
    change Mono (e.inv ≫ r)
    infer_instance

end AlgebraicGeometry.Scheme.Modules
