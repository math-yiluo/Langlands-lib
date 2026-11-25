/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.DualMapLocalRetraction
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Dualizing finite free quotients

## References

* Stacks Project, Tag 0EKP, the dual-surjection construction in (2) to (3)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

private theorem splitMono_map_comp_three
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ D')
    [IsSplitMono (F.map a)] [IsSplitMono (F.map b)] [IsSplitMono (F.map c)] :
    IsSplitMono (F.map (a ≫ b ≫ c)) := by
  rw [F.map_comp a (b ≫ c), F.map_comp b c]
  infer_instance

private theorem finiteLocallyFree_cokernel_splitMono
    {Z : Scheme.{u}} {A B : Z.Modules} (f : A ⟶ B)
    [A.IsFiniteLocallyFree] [B.IsFiniteLocallyFree] [IsSplitMono f] :
    (cokernel f).IsFiniteLocallyFree := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree A
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree B
  have := isQuasicoherent_cokernel f
  let T := ShortComplex.cokernelSequence f
  let t := ShortComplex.Splitting.ofExactOfRetraction T
    (ShortComplex.cokernelSequence_exact f) (retraction f) (IsSplitMono.id f)
    (by dsimp [T, ShortComplex.cokernelSequence]; infer_instance)
  apply isFiniteLocallyFree_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections B hU
  let F := SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op U)
  have : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  let s := t.map F
  let q : Γ(B, U) →ₗ[Γ(Z, U)] Γ(cokernel f, U) := ((T.map F).g).hom
  let j : Γ(cokernel f, U) →ₗ[Γ(Z, U)] Γ(B, U) := s.s.hom
  have hsplit : q.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.s_g
    change q.comp j = LinearMap.id at h
    exact h
  have : Module.Finite Γ(Z, U) Γ(cokernel f, U) :=
    Module.Finite.of_surjective q (by
      intro y
      exact ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have : Module.Projective Γ(Z, U) Γ(cokernel f, U) :=
    Module.Projective.of_split j q hsplit
  exact ⟨Module.finitePresentation_of_projective _ _, inferInstance⟩

private theorem finiteLocallyFree_cokernel_locallySplitMono
    {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    [A.IsFiniteLocallyFree] [B.IsFiniteLocallyFree]
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map f)) :
    (cokernel f).IsFiniteLocallyFree := by
  classical
  choose U hx hs using h
  apply isFiniteLocallyFree_of_isOpenImmersion (cokernel f) (fun x ↦ (U x).ι)
  · simpa only [Scheme.Opens.opensRange_ι] using
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩ :
        (⨆ x, U x) = ⊤)
  · intro x
    let F := restrictFunctor (U x).ι
    have : IsSplitMono (F.map f) := hs x
    have : (F.obj A).IsFiniteLocallyFree :=
      SheafOfModules.IsFiniteLocallyFree.of_iso (R := (U x).toScheme.ringCatSheaf)
        ((restrictFunctorIsoPullback (U x).ι).symm.app A)
    have : (F.obj B).IsFiniteLocallyFree :=
      SheafOfModules.IsFiniteLocallyFree.of_iso (R := (U x).toScheme.ringCatSheaf)
        ((restrictFunctorIsoPullback (U x).ι).symm.app B)
    have : (cokernel (F.map f)).IsFiniteLocallyFree :=
      finiteLocallyFree_cokernel_splitMono (F.map f)
    exact SheafOfModules.IsFiniteLocallyFree.of_iso (R := (U x).toScheme.ringCatSheaf)
      ((PreservesCokernel.iso F f).symm ≪≫
        (restrictFunctorIsoPullback (U x).ι).app (cokernel f))

private theorem mono_pullback_of_locallySplitMono
    {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map f))
    {Y : Scheme.{u}} (g : Y ⟶ X) : Mono ((Modules.pullback g).map f) := by
  classical
  choose U hx hs using h
  let V (y : Y) := g ⁻¹ᵁ U (g y)
  apply mono_of_restrict _ V
  · exact eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx (g y)⟩
  · intro y
    let F := restrictFunctor (U (g y)).ι
    let G := Modules.pullback (g ∣_ U (g y))
    let H := restrictFunctor (V y).ι
    let e : Modules.pullback g ⋙ H ≅ F ⋙ G :=
      Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback (V y).ι) ≪≫
        pullbackComp (V y).ι g ≪≫
        pullbackCongr (morphismRestrict_ι g (U (g y))).symm ≪≫
        (pullbackComp (g ∣_ U (g y)) (U (g y)).ι).symm ≪≫
        Functor.isoWhiskerRight (restrictFunctorIsoPullback (U (g y)).ι).symm G
    have : IsSplitMono (F.map f) := hs (g y)
    have hj : (G.map (F.map f)) ≫ G.map (retraction (F.map f)) = 𝟙 _ := by
      rw [← G.map_comp, IsSplitMono.id, G.map_id]
    have : IsSplitMono (H.map ((Modules.pullback g).map f)) := IsSplitMono.mk'
      { retraction := (e.hom.app B) ≫ G.map (retraction (F.map f)) ≫ e.inv.app A
        id := by
          change (Modules.pullback g ⋙ H).map f ≫ _ = _
          rw [← Category.assoc, e.hom.naturality, Functor.comp_map, Category.assoc,
            ← Category.assoc (G.map (F.map f)), hj, Category.id_comp]
          exact e.hom_inv_id_app A }
    infer_instance

private theorem embedding_of_locallySplit
    {X : Scheme.{u}} {A B C D : X.Modules} (a : A ⟶ B) (b : B ⟶ C) (e : C ≅ D)
    [IsIso a] [A.IsFiniteLocallyFree] [D.IsFiniteLocallyFree]
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map b)) :
    Mono (a ≫ b ≫ e.hom) ∧ (cokernel (a ≫ b ≫ e.hom)).IsFiniteLocallyFree ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
        Mono ((Modules.pullback g).map (a ≫ b ≫ e.hom)) := by
  have hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (a ≫ b ≫ e.hom)) := by
    intro x
    obtain ⟨U, hx, hU⟩ := h x
    have : IsSplitMono ((restrictFunctor U.ι).map b) := hU
    exact ⟨U, hx, splitMono_map_comp_three (restrictFunctor U.ι) a b e.hom⟩
  have hm : Mono (a ≫ b ≫ e.hom) := by
    choose U hx hU using hs
    exact mono_of_restrict _ U
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
      (fun x ↦ by have := hU x; infer_instance)
  exact ⟨hm, finiteLocallyFree_cokernel_locallySplitMono _ hs,
    fun _ g ↦ mono_pullback_of_locallySplitMono _ hs g⟩

/-- The transpose of a finite free quotient of the dual of a vector bundle,
composed with biduality and the finite free dual comparison, is a universally
monic embedding with finite locally free cokernel. -/
theorem dual_free_quotient_embedding
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree]
    {r : ℕ} (β : free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ dual M) [Epi β] :
    let α := SheafOfModules.bidual (R := X.sheaf) M ≫ dualMap β ≫
      (SheafOfModules.homObjFreeUnitIso (R := X.sheaf) (ULift.{u} (Fin r))).hom
    Mono α ∧ (cokernel α).IsFiniteLocallyFree ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ X), Mono ((Modules.pullback g).map α) := by
  have hb : IsIso (SheafOfModules.bidual (R := X.sheaf) M) :=
    SheafOfModules.isIso_bidual.{u} (R := X.sheaf) M
  have hfree := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) r
  apply @embedding_of_locallySplit X M (dual (dual M))
    (dual (free (R := X.ringCatSheaf) (ULift.{u} (Fin r))))
    (free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
    (SheafOfModules.bidual (R := X.sheaf) M) (dualMap β)
    (SheafOfModules.homObjFreeUnitIso (R := X.sheaf) (ULift.{u} (Fin r)))
    hb inferInstance hfree
  exact @exists_local_retraction_dualMap_of_epi.{u}
    X _ (dual M) β inferInstance (IsFiniteLocallyFree.dual M)

end AlgebraicGeometry.Scheme.Modules
