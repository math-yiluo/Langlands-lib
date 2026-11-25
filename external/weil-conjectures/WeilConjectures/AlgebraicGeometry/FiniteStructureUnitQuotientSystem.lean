/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions

import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import WeilConjectures.AlgebraicGeometry.FiniteStructureProperSupport
import WeilConjectures.AlgebraicGeometry.FiniteStructureSupportedUnitKernel

/-! # Factor reduced units through a proper supporting quotient

Source: Stacks Project, Tag 09ZT
(blueprint: lem-weil-pbc-finite-structure-unit-quotient-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

private theorem finiteStructure_unit_composition
    {X S T : Scheme.{u}} (g : T ⟶ S) (h : S ⟶ X) (k : T ⟶ X)
    (w : g ≫ h = k) :
    (tensorPullback g).map (tensorPullbackObjUnitToUnit h) ≫
        tensorPullbackObjUnitToUnit g =
      (tensorPullbackCompositionIso g h k w).inv.app
        (SheafOfModules.unit X.ringCatSheaf) ≫ tensorPullbackObjUnitToUnit k := by
  classical
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let K : T.Modules := SheafOfModules.unit T.ringCatSheaf
  let ah := Classical.choose (exists_tensorPullbackAdjunction h)
  let ag := Classical.choose (exists_tensorPullbackAdjunction g)
  let ak := Classical.choose (exists_tensorPullbackAdjunction k)
  let e := tensorPullbackCompositionIso g h k w
  let q := pushforwardComp g h ≪≫ pushforwardCongr w
  have hu := unit_conjugateEquiv_symm (ah.comp ag) ak q.hom F
  have hu' : (ah.comp ag).unit.app F ≫ q.hom.app _ =
      ak.unit.app F ≫ (pushforward k).map (e.hom.app F) := by
    simpa only [tensorPullbackCompositionIso, conjugateIsoEquiv_symm_apply_hom,
      ah, ag, ak, q, e] using hu
  apply (ah.comp ag).homEquiv F K |>.injective
  apply (cancel_mono (q.hom.app K)).mp
  have hl : (ah.comp ag).homEquiv F K
      ((tensorPullback g).map (tensorPullbackObjUnitToUnit h) ≫
        tensorPullbackObjUnitToUnit g) =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (pushforward h).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) := by
    rw [Adjunction.comp_homEquiv]
    change ah.homEquiv F _ (ag.homEquiv _ _
      ((tensorPullback g).map (tensorPullbackObjUnitToUnit h) ≫
        tensorPullbackObjUnitToUnit g)) = _
    rw [Adjunction.homEquiv_naturality_left]
    have hg : ag.homEquiv _ _ (tensorPullbackObjUnitToUnit g) =
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
      exact (ag.homEquiv _ _).apply_symm_apply _
    rw [hg, Adjunction.homEquiv_naturality_right]
    have hh : ah.homEquiv _ _ (tensorPullbackObjUnitToUnit h) =
        SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
      exact (ah.homEquiv _ _).apply_symm_apply _
    rw [hh]
  have hr : (ah.comp ag).homEquiv F K (e.inv.app F ≫ tensorPullbackObjUnitToUnit k) ≫
      q.hom.app K = SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom := by
    rw [Adjunction.homEquiv_unit]
    calc
      _ = ((ah.comp ag).unit.app F ≫ q.hom.app _) ≫
          (pushforward k).map (e.inv.app F ≫ tensorPullbackObjUnitToUnit k) := by
        simpa only [Category.assoc] using congrArg
          (fun t ↦ (ah.comp ag).unit.app F ≫ t)
          (q.hom.naturality (e.inv.app F ≫ tensorPullbackObjUnitToUnit k))
      _ = ak.unit.app F ≫ (pushforward k).map (tensorPullbackObjUnitToUnit k) := by
        rw [hu']
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
      _ = _ := (tensorPullbackObjUnitToUnit_isIso k).2
  rw [hr, hl]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change T.presheaf.map (eqToHom
    (congrArg (fun l : T ⟶ X ↦ l ⁻¹ᵁ U.unop) w.symm)).op
    (g.app (h ⁻¹ᵁ U.unop) (h.app U.unop r)) = k.app U.unop r
  cases w
  simp only [eqToHom_refl, op_id]
  rw [T.presheaf.map_id]
  rfl


private theorem supporting_quotient_epi {X Z : Scheme.{u}} (k : Z ⟶ X)
    [IsClosedImmersion k] :
    Epi (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) := by
  classical
  let F := SheafOfModules.unit X.ringCatSheaf
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction k)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction k)
  obtain ⟨_, hη, _⟩ := closedImmersion_unit_quotient k
  have : Epi (adj.unit.app F) := (hη F).1
  have : Epi (adj'.unit.app F) := by
    rw [← Adjunction.unit_leftAdjointUniq_hom_app adj adj' F]
    infer_instance
  have : IsIso (tensorPullbackObjUnitToUnit k) :=
    (tensorPullbackObjUnitToUnit_isIso k).1
  rw [← (tensorPullbackObjUnitToUnit_isIso k).2]
  infer_instance

private theorem factored_unit_scalar {X S Y : Scheme.{u}} (j : S ⟶ X) (p : Y ⟶ S)
    (Q : X.Modules) (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q)
    (a : (tensorPullback j).obj Q ⟶
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (ha : (tensorPullback j).map q ≫ a = tensorPullbackObjUnitToUnit j ≫
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)
    (U : X.Opens) (r : Γ(X, U)) :
    (finiteStructureAdjoint j p Q a).app U ((q.val.app (op U)).hom r) =
      (p ≫ j).app U r := by
  have h : q ≫ finiteStructureAdjoint j p Q a =
      finiteStructureAdjoint j p (SheafOfModules.unit X.ringCatSheaf)
        (tensorPullbackObjUnitToUnit j ≫
          SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) := by
    unfold finiteStructureAdjoint
    simp only [Functor.map_comp, Category.assoc]
    have hn : q ≫ (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app Q =
        (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward j).map ((tensorPullback j).map q) := by
      simpa only [Functor.id_map, Functor.comp_map] using
        (Classical.choose (exists_tensorPullbackAdjunction j)).unit.naturality q
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ha, Functor.map_comp]
    simp only [Category.assoc]
  have he := congrArg (fun z ↦ (z.val.app (op U)).hom r) h
  change (finiteStructureAdjoint j p Q a).app U ((q.val.app (op U)).hom r) =
    (finiteStructureAdjoint j p (SheafOfModules.unit X.ringCatSheaf)
      (tensorPullbackObjUnitToUnit j ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)).app U r at he
  rw [he]
  have hs : finiteStructureAdjoint j p (SheafOfModules.unit X.ringCatSheaf)
      (tensorPullbackObjUnitToUnit j ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit (p ≫ j).toRingCatSheafHom := by
    calc
      _ = ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward j).map (tensorPullbackObjUnitToUnit j)) ≫
          (pushforward j).map
            (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) ≫
          (pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
        simp only [finiteStructureAdjoint, Functor.map_comp, Category.assoc]
      _ = SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom ≫
          (pushforward j).map
            (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) ≫
          (pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
        rw [(tensorPullbackObjUnitToUnit_isIso j).2]
      _ = _ := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        rfl
  rw [hs]
  rfl

private theorem pullback_quotient_factor {X S : Scheme.{u}} (j : S ⟶ X)
    {F Q : X.Modules} (q : F ⟶ Q) [Epi q] {B : S.Modules}
    (a : (tensorPullback j).obj F ⟶ B)
    (ha : (tensorPullback j).map (kernel.ι q) ≫ a = 0) :
    ∃ b : (tensorPullback j).obj Q ⟶ B, (tensorPullback j).map q ≫ b = a := by
  classical
  let adj := Classical.choose (exists_tensorPullbackAdjunction j)
  let : (tensorPullback j).IsLeftAdjoint := adj.isLeftAdjoint
  let : (tensorPullback j).Additive := adj.left_adjoint_additive
  let c := CokernelCofork.ofπ q (kernel.condition q)
  have hc : IsColimit c := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι q) (kernel.condition q)) (kernelIsKernel q)
  obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc'
    (c.mapIsColimit hc (tensorPullback j)) a ha
  exact ⟨b, hb⟩

private theorem factored_units_compatible
    {X S T Y Y' : Scheme.{u}} (j : S ⟶ X) (j' : T ⟶ X) (i : S ⟶ T)
    (p : Y ⟶ S) (p' : Y' ⟶ T) (g : Y ⟶ Y')
    (wj : i ≫ j' = j) (wp : g ≫ p' = p ≫ i)
    (c : tensorPullback j' ⋙ tensorPullback i ≅ tensorPullback j)
    (hc : c = (tensorPullbackCompositionIso i j' j wj).symm)
    (Q G : X.Modules) (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi q]
    (v : (tensorPullback j).obj Q ⟶ (tensorPullback j).obj G)
    (v' : (tensorPullback j').obj Q ⟶ (tensorPullback j').obj G)
    (ψ : (tensorPullback j).obj G ≅
      (pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (ψ' : (tensorPullback j').obj G ≅
      (pushforward p').obj (SheafOfModules.unit Y'.ringCatSheaf))
    (hψ : (tensorPullback i).map ψ'.hom ≫
      (moduleBaseChangeMap p' p i g wp (SheafOfModules.unit Y'.ringCatSheaf) ≫
        (pushforward p).map (tensorPullbackObjUnitToUnit g)) = c.hom.app G ≫ ψ.hom)
    (hv : (tensorPullback j).map q ≫ v ≫ ψ.hom = tensorPullbackObjUnitToUnit j ≫
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)
    (hv' : (tensorPullback j').map q ≫ v' ≫ ψ'.hom = tensorPullbackObjUnitToUnit j' ≫
      SheafOfModules.unitToPushforwardObjUnit p'.toRingCatSheafHom) :
    c.hom.app Q ≫ v = (tensorPullback i).map v' ≫ c.hom.app G := by
  classical
  let : (tensorPullback j').PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Classical.choose (exists_tensorPullbackAdjunction j'))
  let : (tensorPullback i).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Classical.choose (exists_tensorPullbackAdjunction i))
  have : Epi ((tensorPullback i).map ((tensorPullback j').map q)) := inferInstance
  apply (cancel_mono ψ.hom).mp
  apply (cancel_epi ((tensorPullback i).map ((tensorPullback j').map q))).mp
  have hnat := c.hom.naturality q
  have hu : c.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      tensorPullbackObjUnitToUnit j =
      (tensorPullback i).map (tensorPullbackObjUnitToUnit j') ≫
        tensorPullbackObjUnitToUnit i := by
    simpa only [hc, Iso.symm_hom] using
      (finiteStructure_unit_composition i j' j wj).symm
  obtain ⟨_, _, _, _, _, _, hbunit⟩ := moduleBaseChangeMap_algebra p' p i g wp
  let beta := moduleBaseChangeMap p' p i g wp (SheafOfModules.unit Y'.ringCatSheaf) ≫
    (pushforward p).map (tensorPullbackObjUnitToUnit g)
  calc
    _ = c.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (tensorPullback j).map q ≫ v ≫ ψ.hom := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun t ↦ t ≫ v ≫ ψ.hom) hnat
    _ = c.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        tensorPullbackObjUnitToUnit j ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ c.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫ t) hv
    _ = (tensorPullback i).map (tensorPullbackObjUnitToUnit j') ≫
        tensorPullbackObjUnitToUnit i ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) hu
    _ = (tensorPullback i).map (tensorPullbackObjUnitToUnit j') ≫
        (tensorPullback i).map
          (SheafOfModules.unitToPushforwardObjUnit p'.toRingCatSheafHom) ≫ beta := by
      simpa only [beta, Category.assoc] using congrArg
        (fun t ↦ (tensorPullback i).map (tensorPullbackObjUnitToUnit j') ≫ t) hbunit.symm
    _ = (tensorPullback i).map ((tensorPullback j').map q) ≫
        (tensorPullback i).map v' ≫ (tensorPullback i).map ψ'.hom ≫ beta := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun t ↦ (tensorPullback i).map t ≫ beta) hv'.symm
    _ = (tensorPullback i).map ((tensorPullback j').map q) ≫
        (tensorPullback i).map v' ≫ c.hom.app G ≫ ψ.hom := by
      simpa only [beta, Category.assoc] using congrArg
        (fun t ↦ (tensorPullback i).map ((tensorPullback j').map q) ≫
          (tensorPullback i).map v' ≫ t) hψ

/-- The reduced structure maps factor compatibly through one proper supporting quotient.
Source: Stacks Project, Tag 09ZT, algebra structure paragraph, expanded using 0CYS,
01XZ, 01Y6, 0096 and affine base change.

Proof: X is Noetherian since it is finite type over the Noetherian affine base.
Use the scheme-theoretic support Z of G, defined by its annihilator ideal J.
Tag 0CYS makes Z proper over A. Let Q be the direct image of O_Z, equivalently
O_X/J, and q the quotient map. Q is quasi-coherent of finite type, hence coherent
by 01XZ, and has proper support. Pullback is right exact, so j_n^*Q is the quotient
of O_Xn by the image of J. That image annihilates j_n^*G and therefore the algebra
p_n,*O_Yn identified with it by psi_n. Acting on 1 shows that its structure map
kills J. The quotient universal property gives a unique map to p_n,*O_Yn;
compose with psi_n inverse to get v_n. Naturality of the quotient, base change's
preservation of 1, hpsi, and the pinned composition comparison show compatibility:
both sides agree after the epimorphic pullback of q. The section formula follows
by the canonical adjunction unit, which sends r to 1 tensor r, and pushforward
composition. No completion, multiplication on G, or lifted map is used here.
For G=0 the scheme-theoretic support and Q are zero; for I=0 the same quotient
factorization applies unchanged; on an empty scheme the equations are unique.
(blueprint: lem-weil-pbc-finite-structure-unit-quotient-system). -/
theorem finite_structure_unit_quotient_system
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ Q : X.Modules, RingedSpace.IsCoherent X.toRingedSpace Q ∧
      Scheme.Modules.HasSupportProperOver f Q ∧
      ∃ (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q)
        (v : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj Q ⟶
          (Scheme.Modules.tensorPullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G),
        (∀ n : ℕ, (c n).hom.app Q ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app G) ∧
        (∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
          (Scheme.Modules.finiteStructureAdjoint
            (pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) Q (v n ≫ (ψ n).hom)).app U
            ((q.val.app (op U)).hom r) =
            (fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))).app U r) := by
  classical
  have _ := hp
  have _ := hw
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hqc, hft⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  let : G.IsQuasicoherent := hqc
  let : G.IsFiniteType := hft
  obtain ⟨Z, k, hk, _hann, _hrange, hkill, _hpush, hkproper⟩ :=
    (module_support_proper_over_base f G).2.2
  let : IsClosedImmersion k := hk
  let : IsProper (k ≫ f) := hkproper.mp hproper
  let Q := (pushforward k).obj (SheafOfModules.unit Z.ringCatSheaf)
  let q : SheafOfModules.unit X.ringCatSheaf ⟶ Q :=
    SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  have hQ : RingedSpace.IsCoherent X.toRingedSpace Q :=
    (isCoherent_pushforward_of_isFinite k _
      (isCoherent_unit_of_finite_to_locallyNoetherian k)).1
  have hpQ : HasSupportProperOver f Q := finite_structure_proper_support k f
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  have hfac : ∀ n : ℕ, ∃ v : (tensorPullback (j n)).obj Q ⟶
      (tensorPullback (j n)).obj G,
      (tensorPullback (j n)).map q ≫ v ≫ (ψ n).hom =
        tensorPullbackObjUnitToUnit (j n) ≫
          SheafOfModules.unitToPushforwardObjUnit (fnY n).toRingCatSheafHom := by
    intro n
    have : Epi q := supporting_quotient_epi k
    obtain ⟨b, hb⟩ := pullback_quotient_factor (j n) q
      (tensorPullbackObjUnitToUnit (j n) ≫
        SheafOfModules.unitToPushforwardObjUnit (fnY n).toRingCatSheafHom)
      (finiteStructure_supported_unit_kernel_zero k (j n) (fnY n) G hkill (ψ n))
    refine ⟨b ≫ (ψ n).inv, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hb
  choose v hv using hfac
  have hqepi : Epi q := supporting_quotient_epi k
  have hcompat : ∀ n : ℕ, (c n).hom.app Q ≫ v n =
      (tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app G := by
    intro n
    exact factored_units_compatible (j n) (j (n + 1)) (i n) (fnY n) (fnY (n + 1))
      (gn n) (hi n) (hcart n).flip.w (c n) (hc n) Q G q (v n) (v (n + 1))
      (ψ n) (ψ (n + 1)) (hψ n) (hv n) (hv (n + 1))
  refine ⟨Q, hQ, hpQ, q, v, hcompat, ?_⟩
  intro n U r
  exact factored_unit_scalar (j n) (fnY n) Q q (v n ≫ (ψ n).hom) (hv n) U r

end AlgebraicGeometry
