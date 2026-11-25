/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
/-! # Finite-free internal Hom exactness in arbitrary universes

Source: Stacks Project, Tag 0GM8 via Tag 0GM7; the explicit proof is the
explicit calculation described below
(blueprint: lem-sc-finite-free-internal-hom-exact-sequence). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem restrictOver_preservesFiniteLimits
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) :
    PreservesFiniteLimits (PresheafOfModules.restrictOver.{w} R U) where
  preservesFiniteLimits K _ _ :=
    { preservesLimit := fun {D} ↦
        { preserves := fun {c} hc ↦ ⟨by
            apply PresheafOfModules.evaluationJointlyReflectsLimits
            intro X
            exact isLimitOfPreserves
              (PresheafOfModules.evaluation _ (Opposite.op X.unop.left)) hc⟩ } }

private theorem internalHom_preservesFiniteLimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (P : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    PreservesFiniteLimits ((SheafOfModules.homFunctor R).obj (Opposite.op P)) := by
  let F := (SheafOfModules.homFunctor R).obj (Opposite.op P)
  refine ⟨fun K _ _ ↦ ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩⟩
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro X
  apply isLimitOfReflects (forget (ModuleCat (R.obj.obj X)))
  have := restrictOver_preservesFiniteLimits R.obj X.unop
  let H := SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
    PresheafOfModules.restrictOver R.obj X.unop ⋙
    coyoneda.obj (Opposite.op ((PresheafOfModules.restrictOver R.obj X.unop).obj P.val))
  let i : (F ⋙ SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ X ⋙
      forget (ModuleCat (R.obj.obj X))) ≅ H :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      ext φ
      rfl)
  have : PreservesLimit D
      (F ⋙ SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ X ⋙
        forget (ModuleCat (R.obj.obj X))) := preservesLimit_of_natIso D i.symm
  exact isLimitOfPreserves
    (F ⋙ SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ X ⋙
      forget (ModuleCat (R.obj.obj X))) hc

open Opposite in
private noncomputable def unitLift
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (U : C)
    (n : N.val.obj (op U)) :
    (PresheafOfModules.restrictOver R.obj U).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val :=
  (PresheafOfModules.unitHomEquiv
    ((PresheafOfModules.restrictOver R.obj U).obj N.val)).symm
      (PresheafOfModules.sectionsMk (fun W ↦ N.val.map W.unop.hom.op n)
        fun {W W'} f ↦ by
          change N.val.map f.unop.left.op (N.val.map W.unop.hom.op n) =
            N.val.map W'.unop.hom.op n
          rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

open Opposite in
private theorem unitLift_app_one
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (U : C)
    (n : N.val.obj (op U)) :
    (unitLift N U n).app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) = n := by
  have h := congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((PresheafOfModules.unitHomEquiv
      ((PresheafOfModules.restrictOver R.obj U).obj N.val)).apply_symm_apply
        (PresheafOfModules.sectionsMk (fun W ↦ N.val.map W.unop.hom.op n)
          fun {W W'} f ↦ by
            change N.val.map f.unop.left.op (N.val.map W.unop.hom.op n) =
              N.val.map W'.unop.hom.op n
            rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]))
  change (unitLift N U n).app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) =
    N.val.map (𝟙 U).op n at h
  apply h.trans
  rw [op_id, N.val.map_id]
  rfl

open Opposite in
private theorem unitLift_unique
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (U : C)
    (φ : (PresheafOfModules.restrictOver R.obj U).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val) :
    φ = unitLift N U (φ.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change φ.app W (1 : R.obj.obj (op W.unop.left)) =
    (1 : R.obj.obj (op W.unop.left)) •
      PresheafOfModulesOfCommRing.map (R := R.obj) N.val W.unop.hom.op
        (φ.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)))
  rw [one_smul]
  have h := PresheafOfModules.naturality_apply φ
    (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op
    (1 : R.obj.obj (op U))
  change φ.app W ((PresheafOfModules.unit (R.obj ⋙ forget₂ _ _)).map
      W.unop.hom.op (1 : R.obj.obj (op U))) =
    N.val.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) at h
  rw [PresheafOfModules.unit_map_one] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
open Opposite in
private theorem finiteFreeHom_epi
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (P : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (r : ℕ)
    (e : P ≅ SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (ULift.{w} (Fin r)))
    {M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (f : M ⟶ N) [Epi f] :
    Epi (SheafOfModules.homObjMap (𝟙 P) f) := by
  classical
  have : HasSheafify J AddCommGrpCat.{w} := hasSheafify_addCommGrp_of_weak.{u, v, w} J
  have : HasSheafify J AddCommGrpCat.{max u v w} :=
    hasSheafify_addCommGrp_of_weak.{u, v, max u v w} J
  have hf : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map f) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w}
      ((SheafOfModules.toSheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map f)).2 inferInstance
  apply (SheafOfModules.toSheaf.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).epi_of_epi_map
  have hH : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map
        (SheafOfModules.homObjMap (𝟙 P) f)) := by
    constructor
    intro U φ
    let I := ULift.{w} (Fin r)
    let b (i : I) := SheafOfModules.ιFree (R :=
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) i ≫ e.inv
    let n (i : I) : N.val.obj (op U) :=
      φ.app (op (Over.mk (𝟙 U))) ((b i).val.app (op U) (1 : R.obj.obj (op U)))
    let s (i : I) := Presheaf.imageSieve ((SheafOfModules.toSheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map f).hom (n i)
    have hs (t : Finset I) : t.inf s ∈ J U := by
      induction t using Finset.induction_on with
      | empty => simp
      | insert i t hi ih =>
        rw [Finset.inf_insert]
        exact J.intersection_covering (Presheaf.imageSieve_mem J
          ((SheafOfModules.toSheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map f).hom (n i)) ih
    apply J.superset_covering (S := Finset.univ.inf s) _ (hs Finset.univ)
    intro V k hk
    have hki (i : I) : s i k := by
      have hle : Finset.univ.inf s ≤ s i := Finset.inf_le (Finset.mem_univ i)
      exact hle k hk
    choose m hm using hki
    let G := PresheafOfModules.restrictOver R.obj V
    have : G.Additive := ⟨by intros; rfl⟩
    let p (i : I) := e.hom ≫ SheafOfModules.freeπ (R :=
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) i
    let ψ := ∑ i : I, G.map (p i).val ≫ unitLift M V (m i)
    let θ := PresheafOfModules.restrictOverMap k φ
    have hu (i : I) : unitLift M V (m i) ≫ G.map f.val = G.map (b i).val ≫ θ := by
      rw [unitLift_unique N V (unitLift M V (m i) ≫ G.map f.val),
        unitLift_unique N V (G.map (b i).val ≫ θ)]
      apply congrArg (unitLift N V)
      change f.val.app (op V)
          ((unitLift M V (m i)).app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))) =
        θ.app (op (Over.mk (𝟙 V))) ((b i).val.app (op V) (1 : R.obj.obj (op V)))
      rw [unitLift_app_one]
      calc
        f.val.app (op V) (m i) = N.val.map k.op (n i) := hm i
        _ = φ.app (op (Over.mk k))
            (P.val.map k.op ((b i).val.app (op U) (1 : R.obj.obj (op U)))) :=
          (PresheafOfModules.naturality_apply φ
            (Over.homMk k (Category.comp_id _) : Over.mk k ⟶ Over.mk (𝟙 U)).op _).symm
        _ = φ.app (op (Over.mk k)) ((b i).val.app (op V) (1 : R.obj.obj (op V))) := by
          rw [← PresheafOfModules.naturality_apply (b i).val k.op]
          change φ.app (op (Over.mk k)) ((b i).val.app (op V)
            (R.obj.map k.op (1 : R.obj.obj (op U)))) = _
          rw [map_one]
        _ = θ.app (op (Over.mk (𝟙 V)))
            ((b i).val.app (op V) (1 : R.obj.obj (op V))) :=
          (PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp k) _).symm
    have hp : ∑ i : I, p i ≫ b i = 𝟙 P := by
      calc
        ∑ i : I, p i ≫ b i = e.hom ≫
            (∑ i : I, SheafOfModules.freeπ i ≫ SheafOfModules.ιFree i) ≫ e.inv := by
          simp only [p, b, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = 𝟙 P := by
          rw [SheafOfModules.sum_freeπ_ιFree, Category.id_comp, e.hom_inv_id]
    have hpG : ∑ i : I, G.map (p i).val ≫ G.map (b i).val = 𝟙 (G.obj P.val) := by
      have hval : (∑ i : I, p i ≫ b i).val = ∑ i : I, (p i ≫ b i).val :=
        (SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).map_sum _ _
      calc
        ∑ i : I, G.map (p i).val ≫ G.map (b i).val =
            G.map (∑ i : I, p i ≫ b i).val := by
          rw [hval, G.map_sum]
          simp only [SheafOfModules.comp_val, G.map_comp]
        _ = 𝟙 (G.obj P.val) := by rw [hp, SheafOfModules.id_val, G.map_id]
    refine ⟨ψ, ?_⟩
    change G.map (SheafOfModules.Hom.val (𝟙 P)) ≫ ψ ≫ G.map f.val = θ
    rw [SheafOfModules.id_val, G.map_id, Category.id_comp]
    dsimp only [ψ]
    rw [Preadditive.sum_comp]
    simp_rw [Category.assoc, hu, ← Category.assoc]
    rw [← Preadditive.sum_comp, hpG, Category.id_comp]
  infer_instance

/-- Internal Hom from a finite free module preserves exactness, allowing different
universes for the site and the module sections.
Source: Stacks Project, cohomology.tex, Tag 0GM8, case (2), finite free Hom calculation.
(blueprint: lem-sc-finite-free-internal-hom-exact-sequence)

Proof: choose the displayed finite free basis. On each localized site, evaluate a
linear map on its basis to identify internal Hom with a finite product of the target
module, with the necessary universe lift. Under this identification both maps become
coordinatewise maps. Finite products preserve exact sequences in module sheaves:
a cycle is a finite tuple of cycles; exactness of the original sequence supplies a
local preimage of each coordinate. Refine the finitely many coverings together and
assemble these preimages into the tuple giving a boundary. The universe lift changes
neither the underlying sections nor this local exactness criterion. For rank zero,
all three internal Homs are zero and the assertion is immediate. -/
theorem finiteFree_internalHom_exact_sequence
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (P : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (r : ℕ) (e : P ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (ULift.{w} (Fin r)))
    (S : ShortComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)))
    (hS : S.Exact) :
    ∃ hz : SheafOfModules.homObjMap (𝟙 P) S.f ≫
        SheafOfModules.homObjMap (𝟙 P) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 P) S.f)
        (SheafOfModules.homObjMap (𝟙 P) S.g) hz).Exact := by
  have : HasSheafify J AddCommGrpCat.{w} := hasSheafify_addCommGrp_of_weak.{u, v, w} J
  have : HasSheafify J AddCommGrpCat.{max u v w} :=
    hasSheafify_addCommGrp_of_weak.{u, v, max u v w} J
  let F := (SheafOfModules.homFunctor R).obj (Opposite.op P)
  have : PreservesFiniteLimits F := internalHom_preservesFiniteLimits P
  have : F.PreservesEpimorphisms := ⟨fun f _ ↦ finiteFreeHom_epi P r e f⟩
  have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact ⟨(S.map F).zero, hS.map F⟩

end CochainComplex
