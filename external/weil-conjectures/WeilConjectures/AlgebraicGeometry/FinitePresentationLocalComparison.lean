/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

/-! # Local comparison of a finite presentation and a finite free epimorphism

Source: Stacks Project, Modules, Lemma 01BP(1), first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem local_free_lifts (X : RingedSpace.{u}) (U : Opens X)
    (A₁ A₂ B : SheafOfModules.{u} ((moduleRings X).over U))
    (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) [Epi φ₁] [Epi φ₂]
    (I₁ I₂ : Type u) [Finite I₁] [Finite I₂]
    (f₁ : SheafOfModules.free I₁ ⟶ B) (f₂ : SheafOfModules.free I₂ ⟶ B)
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
      ∃ (g₁ : SheafOfModules.free I₁ ⟶ (SheafOfModules.overMap (moduleRings X) i).obj A₁)
        (g₂ : SheafOfModules.free I₂ ⟶ (SheafOfModules.overMap (moduleRings X) i).obj A₂),
        g₁ ≫ (SheafOfModules.overMap (moduleRings X) i).map φ₁ =
          (SheafOfModules.mapFreeIso (SheafOfModules.overMap (moduleRings X) i) I₁
            (SheafOfModules.overMapUnitIso i).symm).hom ≫
              (SheafOfModules.overMap (moduleRings X) i).map f₁ ∧
        g₂ ≫ (SheafOfModules.overMap (moduleRings X) i).map φ₂ =
          (SheafOfModules.mapFreeIso (SheafOfModules.overMap (moduleRings X) i) I₂
            (SheafOfModules.overMapUnitIso i).symm).hom ≫
              (SheafOfModules.overMap (moduleRings X) i).map f₂ := by
  classical
  let J := (Opens.grothendieckTopology X).over U
  let Z : Over U := Over.mk (𝟙 U)
  let T₁ := SheafOfModules.toSheaf.{u} ((moduleRings X).over U)
  have : Epi (T₁.map φ₁) := inferInstance
  have : Epi (T₁.map φ₂) := inferInstance
  have : Sheaf.IsLocallySurjective (T₁.map φ₁) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := T₁.map φ₁)).mpr inferInstance
  have : Sheaf.IsLocallySurjective (T₁.map φ₂) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := T₁.map φ₂)).mpr inferInstance
  let s₁ := B.freeHomEquiv f₁
  let s₂ := B.freeHomEquiv f₂
  let S₁ : Sieve Z := ⨅ k : I₁, Presheaf.imageSieve (T₁.map φ₁).hom ((s₁ k).val (Opposite.op Z))
  let S₂ : Sieve Z := ⨅ k : I₂, Presheaf.imageSieve (T₁.map φ₂).hom ((s₂ k).val (Opposite.op Z))
  have hS₁ : S₁ ∈ J Z := J.iInf_mem _ fun k ↦
    Presheaf.imageSieve_mem J (T₁.map φ₁).hom ((s₁ k).val (Opposite.op Z))
  have hS₂ : S₂ ∈ J Z := J.iInf_mem _ fun k ↦
    Presheaf.imageSieve_mem J (T₁.map φ₂).hom ((s₂ k).val (Opposite.op Z))
  have hS : S₁ ⊓ S₂ ∈ J Z := J.intersection_covering hS₁ hS₂
  have hS' := (GrothendieckTopology.mem_over_iff _ (S₁ ⊓ S₂)).mp hS
  obtain ⟨V, i, hi, hxV⟩ := (Opens.mem_grothendieckTopology X).mp hS' x hx
  have hi' := (Sieve.overEquiv_iff (S₁ ⊓ S₂) i).mp hi
  let W : Over U := Over.mk i
  let t : W ⟶ Z := Over.homMk i
  have hl₁ (k : I₁) : ∃ y : A₁.val.obj (Opposite.op W),
      φ₁.val.app (Opposite.op W) y = B.val.map t.op ((s₁ k).val (Opposite.op Z)) := by
    exact (iInf_le (fun k ↦ Presheaf.imageSieve (T₁.map φ₁).hom
      ((s₁ k).val (Opposite.op Z))) k) _ hi'.1
  have hl₂ (k : I₂) : ∃ y : A₂.val.obj (Opposite.op W),
      φ₂.val.app (Opposite.op W) y = B.val.map t.op ((s₂ k).val (Opposite.op Z)) := by
    exact (iInf_le (fun k ↦ Presheaf.imageSieve (T₁.map φ₂).hom
      ((s₂ k).val (Opposite.op Z))) k) _ hi'.2
  choose y₁ hy₁ using hl₁
  choose y₂ hy₂ using hl₂
  let H := SheafOfModules.overMap (moduleRings X) i
  let l₁ (k : I₁) : (H.obj A₁).sections :=
    PresheafOfModules.sectionsMk (fun Q ↦ A₁.val.map
      (Over.homMk Q.unop.hom : (Over.map i).obj Q.unop ⟶ W).op (y₁ k)) (by
        intro Q Q' f
        have hm (z) : (H.obj A₁).val.map f z =
            A₁.val.map ((Over.map i).map f.unop).op z := rfl
        rw [hm, ← PresheafOfModules.map_comp_apply]
        rfl)
  let l₂ (k : I₂) : (H.obj A₂).sections :=
    PresheafOfModules.sectionsMk (fun Q ↦ A₂.val.map
      (Over.homMk Q.unop.hom : (Over.map i).obj Q.unop ⟶ W).op (y₂ k)) (by
        intro Q Q' f
        have hm (z) : (H.obj A₂).val.map f z =
            A₂.val.map ((Over.map i).map f.unop).op z := rfl
        rw [hm, ← PresheafOfModules.map_comp_apply]
        rfl)
  refine ⟨V, i, hxV, (H.obj A₁).freeHomEquiv.symm l₁,
    (H.obj A₂).freeHomEquiv.symm l₂, ?_, ?_⟩
  · apply (H.obj B).freeHomEquiv.injective
    funext k
    rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro Q
    have ht : ((H.obj B).freeHomEquiv
        ((SheafOfModules.mapFreeIso H I₁
          (SheafOfModules.overMapUnitIso i).symm).hom ≫ H.map f₁) k).val Q =
        (s₁ k).val (Opposite.op ((Over.map i).obj Q.unop)) := by
      change ((H.obj B).unitHomEquiv
        (SheafOfModules.ιFree k ≫ _ ≫ H.map f₁)).val Q = _
      rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
        ← Functor.map_comp]
      rfl
    rw [ht]
    change (H.map φ₁).val.app Q
      (A₁.val.map (Over.homMk Q.unop.hom).op (y₁ k)) = _
    have hm (z) : (H.map φ₁).val.app Q z =
        φ₁.val.app (Opposite.op ((Over.map i).obj Q.unop)) z := rfl
    rw [hm, PresheafOfModules.naturality_apply, hy₁,
      ← PresheafOfModules.map_comp_apply]
    exact (s₁ k).property _
  · apply (H.obj B).freeHomEquiv.injective
    funext k
    rw [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro Q
    have ht : ((H.obj B).freeHomEquiv
        ((SheafOfModules.mapFreeIso H I₂
          (SheafOfModules.overMapUnitIso i).symm).hom ≫ H.map f₂) k).val Q =
        (s₂ k).val (Opposite.op ((Over.map i).obj Q.unop)) := by
      change ((H.obj B).unitHomEquiv
        (SheafOfModules.ιFree k ≫ _ ≫ H.map f₂)).val Q = _
      rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
        ← Functor.map_comp]
      rfl
    rw [ht]
    change (H.map φ₂).val.app Q
      (A₂.val.map (Over.homMk Q.unop.hom).op (y₂ k)) = _
    have hm (z) : (H.map φ₂).val.app Q z =
        φ₂.val.app (Opposite.op ((Over.map i).obj Q.unop)) z := rfl
    rw [hm, PresheafOfModules.naturality_apply, hy₂,
      ← PresheafOfModules.map_comp_apply]
    exact (s₂ k).property _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem presentation_comparison_transport (X : RingedSpace.{u}) (U V : Opens X)
    (M : SheafOfModules.{u} ((moduleRings X).over U))
    (N : SheafOfModules.{u} ((moduleRings X).over V))
    (P : M.Presentation) [P.IsFinite]
    (H : SheafOfModules.{u} ((moduleRings X).over U) ⥤
      SheafOfModules.{u} ((moduleRings X).over V)) [PreservesColimitsOfSize.{u, u} H]
    (η : SheafOfModules.unit ((moduleRings X).over V) ≅
      H.obj (SheafOfModules.unit ((moduleRings X).over U)))
    (c : H.obj M ≅ N) (I : Type u) (f : SheafOfModules.free I ⟶ M)
    (a : SheafOfModules.free I ⟶ H.obj (SheafOfModules.free P.generators.I))
    (b : SheafOfModules.free P.generators.I ⟶ H.obj (SheafOfModules.free I))
    (ha : a ≫ H.map P.generators.π = (SheafOfModules.mapFreeIso H I η).hom ≫ H.map f)
    (hb : b ≫ H.map f = (SheafOfModules.mapFreeIso H P.generators.I η).hom ≫
      H.map P.generators.π) :
    ∃ Q : N.Presentation, Q.IsFinite ∧
      ∃ (α : SheafOfModules.free I ⟶ SheafOfModules.free Q.generators.I)
        (β : SheafOfModules.free Q.generators.I ⟶ SheafOfModules.free I),
        α ≫ Q.generators.π = (SheafOfModules.mapFreeIso H I η).hom ≫ H.map f ≫ c.hom ∧
        β ≫ (SheafOfModules.mapFreeIso H I η).hom ≫ H.map f ≫ c.hom = Q.generators.π := by
  let Q := (P.map H η).ofIsIso c.hom
  let er := SheafOfModules.mapFreeIso H I η
  let eg := SheafOfModules.mapFreeIso H P.generators.I η
  have hQ := (P.map H η).generators.ofEpi_π c.hom
  have hπ := P.map_π_eq H η
  have hh : ((P.map H η).generators.ofEpi c.hom).π =
      (eg.hom ≫ H.map P.generators.π) ≫ c.hom :=
    hQ.trans (congrArg (fun f ↦ f ≫ c.hom) hπ)
  refine ⟨Q, inferInstance, a ≫ eg.inv, b ≫ er.inv, ?_, ?_⟩
  · apply (congrArg (fun f ↦ (a ≫ eg.inv) ≫ f) hh).trans
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f ↦ f ≫ c.hom) ha
  · apply Eq.trans ?_ hh.symm
    change (b ≫ er.inv) ≫ er.hom ≫ H.map f ≫ c.hom = _
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f ↦ f ≫ c.hom) hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Near any point, a finite presentation can be compared in both directions
with a given finite free epimorphism.
Source: Stacks Project, Modules, Lemma 01BP(1), first paragraph of the proof;
kernel restriction is Modules, Section 01AF.
(blueprint: lem-weil-pbc-finite-presentation-local-comparison)

Proof: Choose a finite presentation near x from the finite-presentation data.
Each of the finitely many basis images of psi lifts locally through its generator
map, since that map is epi. Each of the finitely many presentation generators
lifts locally through psi, since psi is epi. Intersect these finitely many
neighborhoods of x and restrict the presentation to the intersection. Restriction
preserves finite free modules, epis, and kernels; transport the restriction of
psi across the canonical free-module isomorphism to obtain psi'. The chosen
lifts define alpha and beta. Both equations hold because they agree on the free
basis. Evaluation computes kernels sectionwise, so restriction supplies the
isomorphism of kernels in the statement. Empty basis sets need no shrinking;
the empty space has no points to check. -/
theorem finitePresentation_local_comparison
    (X : RingedSpace.{u}) (F : SheafOfModules.{u} (moduleRings X))
    [F.IsFinitePresentation] (r : ℕ)
    (ψ : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r)) ⟶ F)
    (hψ : Epi ψ) (x : X) :
    ∃ (U : Opens X), x ∈ U ∧
      ∃ (ψ' : SheafOfModules.free (R := (moduleRings X).over U)
          (ULift.{u} (Fin r)) ⟶ F.over U)
        (P : (F.over U).Presentation), P.IsFinite ∧
        ∃ (α : SheafOfModules.free (R := (moduleRings X).over U)
            (ULift.{u} (Fin r)) ⟶ SheafOfModules.free P.generators.I)
          (β : SheafOfModules.free (R := (moduleRings X).over U) P.generators.I ⟶
            SheafOfModules.free (ULift.{u} (Fin r))),
          α ≫ P.generators.π = ψ' ∧ β ≫ ψ' = P.generators.π ∧
            Nonempty ((kernel ψ).over U ≅ kernel ψ') := by
  classical
  let R := moduleRings X
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  let := hq
  have hcover := (Opens.coversTop_iff X q.X).mp q.coversTop
  have hx : x ∈ ⨆ j, q.X j := by rw [hcover]; trivial
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hx
  let U := q.X j
  let P := q.presentation j
  let L := SheafOfModules.overFunctor R U
  let e : SheafOfModules.free (R := R.over U) (ULift.{u} (Fin r)) ≅
      L.obj (SheafOfModules.free (R := R) (ULift.{u} (Fin r))) :=
    SheafOfModules.mapFreeIso L _ (Iso.refl _)
  let ψU := e.hom ≫ L.map ψ
  let := hψ
  have : Epi ψU := by dsimp [ψU]; infer_instance
  have : Finite P.generators.I := inferInstance
  obtain ⟨V, i, hxV, a, b, ha, hb⟩ := local_free_lifts X U
    (SheafOfModules.free P.generators.I) (SheafOfModules.free (ULift.{u} (Fin r)))
    (F.over U) P.generators.π ψU (ULift.{u} (Fin r)) P.generators.I ψU
    P.generators.π x hxj
  let H := SheafOfModules.overMap R i
  let η := (SheafOfModules.overMapUnitIso (R := R) i).symm
  let c := (SheafOfModules.overFunctorMap R i).app F
  let er := SheafOfModules.mapFreeIso H (ULift.{u} (Fin r)) η
  let ψV := er.hom ≫ H.map ψU ≫ c.hom
  obtain ⟨PV, hPV, α, β, hα, hβ⟩ :=
    presentation_comparison_transport X U V (F.over U) (F.over V) P H η c
      (ULift.{u} (Fin r)) ψU a b ha hb
  refine ⟨V, hxV, ψV, PV, hPV, α, β, hα, ?_, ?_⟩
  · exact hβ
  · let T := SheafOfModules.overFunctor R V
    let eV := er ≪≫ H.mapIso e ≪≫
      (SheafOfModules.overFunctorMap R i).app
        (SheafOfModules.free (R := R) (ULift.{u} (Fin r)))
    have heq : ψV = eV.hom ≫ T.map ψ := by
      change er.hom ≫ H.map (e.hom ≫ L.map ψ) ≫ c.hom =
        (er.hom ≫ H.map e.hom ≫
          ((SheafOfModules.overFunctorMap R i).app _).hom) ≫ T.map ψ
      simp only [Functor.map_comp, Category.assoc]
      have hn := (SheafOfModules.overFunctorMap R i).hom.naturality ψ
      change H.map (L.map ψ) ≫ c.hom =
        ((SheafOfModules.overFunctorMap R i).app _).hom ≫ T.map ψ at hn
      exact congrArg (fun f ↦ er.hom ≫ H.map e.hom ≫ f) hn
    exact ⟨PreservesKernel.iso T ψ ≪≫ (kernelIsIsoComp eV.hom (T.map ψ)).symm ≪≫
      kernelIsoOfEq heq.symm⟩

end AlgebraicGeometry.RingedSpace
