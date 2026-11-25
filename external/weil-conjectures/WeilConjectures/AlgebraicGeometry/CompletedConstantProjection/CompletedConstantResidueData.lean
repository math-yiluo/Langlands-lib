/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
/-! # Residue data and local tensor generators

Source: Stacks Project, Modules on Sites, Tags 03EK and 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
/-- The finite residue module with its quotient-ring action.
Source: Stacks Tags 093J--093M
(blueprint: def-weil-pbc-completed-constant-residue-data). -/
abbrev completedConstantResidueModule (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :=
  (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).obj
    (ModuleCat.of (A ⧸ I ^ (n + 1))
      (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))))

/-- Multiplication on a constant quotient module by a quotient-ring section.
The abelian sheaf is the same sheafification whether its scalar ring is A or A/I^k.
Source: Stacks Tag 03EK
(blueprint: def-weil-pbc-completed-constant-residue-data). -/
def completedConstantResidueMul (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (s : (adicLisseConstantRing X (A ⧸ I ^ (n + 1))).obj.obj U)
    (y : ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj
      (op n)).val.obj U) :
    ((adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)).obj
      (op n)).val.obj U :=
  s • (show (completedConstantResidueModule X I N n).val.obj U from y)

namespace CompletedConstantProjection

abbrev raw (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))

theorem generator_smul (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (N : ModuleCat.{u + 1} B) (U : X.ProEtᵒᵖ) (b : B) (x : N) :
    completedConstantGenerator X B N U (b • x) =
      (adicLisseConstantUnit X B).app U b • completedConstantGenerator X B N U x := by
  exact (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (adicLisseConstantUnit X B)).unit.app ((raw X B).obj N)).app U).hom.map_smul b x

def constantMap (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
    (hp : a ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f))
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (q : M →ₛₗ[f] N) :
    (adicLisseConstantModules X B).obj M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
        ((SheafOfModules.restrictScalars ((adicLisseForget X).map p)).obj
          ((adicLisseConstantModules X D).obj N)) := by
  let T := (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
    ((SheafOfModules.restrictScalars ((adicLisseForget X).map p)).obj
      ((adicLisseConstantModules X D).obj N))
  refine (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit X B) (P := (raw X B).obj M) (F := T)).symm ?_
  refine
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars
          (adicLisseConstantUnit X B)).obj T.val).obj U)
        { toFun := fun x ↦ completedConstantGenerator X D N U (q x)
          map_add' := fun x y ↦ by simp [completedConstantGenerator, map_add]
          map_smul' := by
            intro b x
            change B at b
            change M at x
            change completedConstantGenerator X D N U (q (b • x)) =
              p.hom.app U (a.hom.app U ((adicLisseConstantUnit X B).app U b)) •
                completedConstantGenerator X D N U (q x)
            rw [q.map_smulₛₗ, generator_smul]
            congr 1
            have h : p.hom.app U (a.hom.app U
                ((adicLisseConstantUnit X B).app U b)) =
                ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
                  (CommRingCat.ofHom f)).hom.app U ((adicLisseConstantUnit X B).app U b) :=
              congrArg (fun k ↦ k.hom.app U ((adicLisseConstantUnit X B).app U b)) hp
            have hn := toSheafify_naturality (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom f))
            have hn' : (adicLisseConstantUnit X D).app U (f b) =
                ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
                  (CommRingCat.ofHom f)).hom.app U ((adicLisseConstantUnit X B).app U b) :=
              ConcreteCategory.congr_hom (NatTrans.congr_app hn U) b
            exact hn'.trans h.symm }
      naturality := ?_ }
  · intro U V i
    ext x
    exact NatTrans.naturality_apply
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of N))) i (q x)

theorem constantMap_generator (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
    (hp : a ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f))
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (q : M →ₛₗ[f] N)
    (U : X.ProEtᵒᵖ) (x : M) :
    (constantMap X f a p hp M N q).val.app U (completedConstantGenerator X B M U x) =
      completedConstantGenerator X D N U (q x) := by
  let T := (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
    ((SheafOfModules.restrictScalars ((adicLisseForget X).map p)).obj
      ((adicLisseConstantModules X D).obj N))
  unfold constantMap
  exact congrArg (fun k : (raw X B).obj M ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit X B)).obj T.val ↦
        k.app U x)
    ((PresheafOfModules.sheafificationHomEquiv.{u + 1}
      (adicLisseConstantUnit X B) (P := (raw X B).obj M) (F := T)).apply_symm_apply _)

theorem residue_smul {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ)
    (c : AdicCompletion I A) (a : A)
    (h : AdicCompletion.evalₐ I n c = Ideal.Quotient.mk (I ^ n) a) (x : N) :
    (I ^ n • ⊤ : Submodule A (completedConstantUnderlyingModule I N)).mkQ (c • x) =
      a • (I ^ n • ⊤ : Submodule A (completedConstantUnderlyingModule I N)).mkQ x := by
  let M := completedConstantUnderlyingModule I N
  let : Module A N := M.isModule
  let : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let f : AdicCompletion I A →ₗ[A] M :=
    { toFun := fun t ↦ t • x
      map_add' := fun s t ↦ add_smul s t x
      map_smul' := fun a t ↦ smul_assoc a t x }
  have hc : c - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
    change AdicCompletion.eval I A n (c - algebraMap A (AdicCompletion I A) a) = 0
    have hz : AdicCompletion.evalₐ I n
        (c - algebraMap A (AdicCompletion I A) a) = 0 := by
      rw [map_sub, (AdicCompletion.evalₐ I n).commutes, h]
      simp only [Ideal.Quotient.algebraMap_eq, sub_self]
    exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq A (by simp)).injective).mp hz
  apply sub_eq_zero.mp
  rw [← map_smul, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hm := Submodule.smul_top_le_comap_smul_top (I ^ n) f hc
  change f (c - algebraMap A (AdicCompletion I A) a) ∈
    (I ^ n • ⊤ : Submodule A M) at hm
  simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, sub_smul, algebraMap_smul] using hm

theorem constantMap_underlying (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
    (hp : a ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f))
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (q : M →ₛₗ[f] N) :
    (SheafOfModules.toSheaf _).map (constantMap X f a p hp M N q) =
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom q.toAddMonoidHom) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of N)).property
  ext U x
  exact (constantMap_generator X f a p hp M N q U x).trans
    (ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U)
      (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom q.toAddMonoidHom)))) x)

theorem constantMap_isIso (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : adicLisseConstantRing X B ⟶ S) (p : S ⟶ adicLisseConstantRing X D)
    (hp : a ≫ p = (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f))
    (M : ModuleCat.{u + 1} B) (N : ModuleCat.{u + 1} D) (q : M →ₛₗ[f] N)
    (hq : Function.Bijective q) : IsIso (constantMap X f a p hp M N q) := by
  have hi : IsIso ((SheafOfModules.toSheaf _).map (constantMap X f a p hp M N q)) := by
    rw [constantMap_underlying]
    have : IsIso (AddCommGrpCat.ofHom q.toAddMonoidHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hq
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- A semilinear identity on one additive group identifies its two constant scalar actions.
Source: Stacks Tag 03EK, constant-module sheafification
(blueprint: def-weil-pbc-completed-constant-residue-data). -/
theorem constantScalar_compatibility (X : Scheme.{u})
    {B D : Type (u + 1)} [CommRing B] [CommRing D] (f : B →+* D)
    (V : Type (u + 1)) [AddCommGroup V] [Module B V] [Module D V]
    (q : V →ₛₗ[f] V) (hq : q.toAddMonoidHom = AddMonoidHom.id V)
    (U : X.ProEtᵒᵖ) (a : (adicLisseConstantRing X B).obj.obj U)
    (y : ((adicLisseConstantModules X B).obj (ModuleCat.of B V)).val.obj U) :
    (((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f)).hom.app U a) •
        (show ((adicLisseConstantModules X D).obj (ModuleCat.of D V)).val.obj U from y) =
      a • y := by
  let c := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom f)
  let g := constantMap X f c (𝟙 _) (Category.comp_id c)
    (ModuleCat.of B V) (ModuleCat.of D V) q
  have hg := constantMap_underlying X f c (𝟙 _) (Category.comp_id c)
    (ModuleCat.of B V) (ModuleCat.of D V) q
  have hid : AddCommGrpCat.ofHom q.toAddMonoidHom = 𝟙 (AddCommGrpCat.of V) :=
    congrArg AddCommGrpCat.ofHom hq
  have hg' : (SheafOfModules.toSheaf _).map g = 𝟙 _ :=
    hg.trans ((congrArg
      (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map hid).trans
        ((constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map_id _))
  have hgu (z) : g.val.app U z = z := congrArg (fun k ↦ k.hom.app U z) hg'
  have h : g.val.app U (a • y) =
      c.hom.app U a •
        (show ((adicLisseConstantModules X D).obj (ModuleCat.of D V)).val.obj U from
          g.val.app U y) := (g.val.app U).hom.map_smul a y
  exact ((hgu (a • y)).symm.trans
    (h.trans (congrArg (fun z :
      ((adicLisseConstantModules X D).obj (ModuleCat.of D V)).val.obj U ↦
        c.hom.app U a • z) (hgu y)))).symm

attribute [local irreducible] constantMap

def residueMap {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} (AdicCompletion I A)) (n : ℕ) :
    N →ₛₗ[(AdicCompletion.evalₐ I (n + 1)).toRingHom]
      (completedConstantUnderlyingModule I N ⧸
        (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N))) where
  toFun := (I ^ (n + 1) • ⊤ : Submodule A (completedConstantUnderlyingModule I N)).mkQ
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) c)
    change (I ^ (n + 1) • ⊤ : Submodule A
      (completedConstantUnderlyingModule I N)).mkQ (c • x) =
        AdicCompletion.evalₐ I (n + 1) c • _
    rw [← ha]
    exact (residue_smul I N (n + 1) c a ha.symm x).trans
      (Module.Quotient.mk_smul_mk
        (completedConstantUnderlyingModule I N) (I ^ (n + 1)) a x).symm

theorem realization_hom_ext (X : Scheme.{u})
    {B : Type (u + 1)} [CommRing B]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : adicLisseConstantRing X B ⟶ S) (a : R ⟶ S)
    (N : ModuleCat.{u + 1} B)
    (T : SheafOfModules.{u + 1} ((adicLisseForget X).obj R))
    (f g : (SheafOfModules.restrictScalars ((adicLisseForget X).map a)).obj
      ((completedAdicChange X φ).obj ((adicLisseConstantModules X B).obj N)) ⟶ T)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : N),
      f.val.app U (completedAdicChangeTensor X φ ((adicLisseConstantModules X B).obj N)
        U s (completedConstantGenerator X B N U x)) =
      g.val.app U (completedAdicChangeTensor X φ ((adicLisseConstantModules X B).obj N)
        U s (completedConstantGenerator X B N U x))) : f = g := by
  let M := (adicLisseConstantModules X B).obj N
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let e := (completedAdicChangeData X φ).choose_spec.choose M
  let j := (SheafOfModules.toSheaf _).map (eqToHom e.symm)
  let F : P.presheaf ⟶ T.val.presheaf :=
    toSheafify (ProEt.topology X) P.presheaf ≫ j.hom ≫
      ((SheafOfModules.toSheaf _).map f).hom
  let G : P.presheaf ⟶ T.val.presheaf :=
    toSheafify (ProEt.topology X) P.presheaf ≫ j.hom ≫
      ((SheafOfModules.toSheaf _).map g).hom
  have hFG : F = G := by
    ext U t
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul s m =>
      let η := toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of N))
      apply T.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem (ProEt.topology X) η m)
      rintro V i ⟨x, hx⟩
      rw [← NatTrans.naturality_apply F i.op, ← NatTrans.naturality_apply G i.op]
      change F.app (op V) (P.map i.op
        (s ⊗ₜ[(adicLisseConstantRing X B).obj.obj U, (φ.hom.app U).hom] m)) = _
      change F.app (op V) (P.map i.op
        (s ⊗ₜ[(adicLisseConstantRing X B).obj.obj U, (φ.hom.app U).hom] m)) =
          G.app (op V) (P.map i.op
            (s ⊗ₜ[(adicLisseConstantRing X B).obj.obj U, (φ.hom.app U).hom] m))
      erw [CompletedConstantReduction.tensorRestriction_tmul X]
      have hx' : completedConstantGenerator X B N (op V) x = M.val.map i.op m := hx
      erw [← hx']
      exact h (op V) (S.obj.map i.op s) x
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi j).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _ T.isSheaf
  exact hFG

theorem constant_map_generator (X : Scheme.{u})
    {B : Type (u + 1)} [CommRing B] {M N : ModuleCat.{u + 1} B}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M) :
    ((adicLisseConstantModules X B).map f).val.app U
      (completedConstantGenerator X B M U x) =
        completedConstantGenerator X B N U (f x) := by
  have h := toSheafify_naturality (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom f.hom.toAddMonoidHom))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h U) x).symm

end CompletedConstantProjection
end AlgebraicGeometry.Scheme
