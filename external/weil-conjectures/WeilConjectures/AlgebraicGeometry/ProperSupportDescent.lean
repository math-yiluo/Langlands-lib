/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of proper module support

Source: Stacks Project, Limits of Schemes, Lemma 32.13.5 (Tag 081G), together with
Cohomology of Schemes, Lemma 30.26.7 (Tag 0CYS)
(blueprint: lem-pc-proper-support-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proper support of a finitely presented module descends to a later Noetherian stage.
The functor `R` specifies the affine bases `S_k = Spec (R.obj k)` and their affine
transition maps. These bases are qcqs. The cone `c` with `hc` is their inverse limit,
and `IsAffine c.pt` expresses that the limit is `Spec R` for a ring `R`.
The scheme and module at the limit and at a later stage are their indicated pullbacks.

Source: Stacks Project, Tag 081G and Tag 0CYS
(blueprint: lem-pc-proper-support-descent).

Proof:
1. Finite presentation implies quasi-coherence and finite type. By
   lem-weil-pbc-scheme-theoretic-support, form the closed scheme-theoretic support
   Z_i in X_i. Its base changes to X and X_j have underlying sets equal to the
   preimages of Supp(F_i) (Stacks 01JT). These are precisely the supports of the
   pulled-back modules by lem-weil-pbc-support-pullback-finite-type(3).
   The map Z_i to S_i is locally of finite type, and both schemes are qcqs:
   S_i is affine and Z_i is closed in the finitely presented S_i-scheme X_i.
2. The limit support is proper by hypothesis. The closed base change Z of Z_i
   has this underlying support, so Z to S is proper by
   lem-weil-pbc-closed-subset-proper-over-base-properties(1), Stacks 0CYL.
3. Apply lem-weil-pbc-eventually-proper, Stacks 081F, to Z_i to S_i and the
   directed tail of the base system. Some j >= i has Z_j to S_j proper.
4. The underlying set of Z_j is the support of the pullback of F_i by step 1.
   Since X_j to S_j is locally of finite type, properness of Z_j gives proper
   support by lem-weil-pbc-closed-subset-proper-over-base-properties(1). -/
theorem exists_hasSupportProperOver_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Fi : Xi.Modules) [Fi.IsFinitePresentation]
    (hF : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj Fi)) :
    ∃ (j : I) (hij : i ≤ j),
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij))))
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj Fi) := by
  classical
  obtain ⟨J, _, hJ, _, _, _, hsupport, _⟩ := Scheme.schemeTheoreticSupport Xi Fi
  let z := J.subschemeι
  let a := z ≫ f
  have : IsClosedImmersion z := hJ
  have : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Xi := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace z
  have : QuasiSeparatedSpace J.subscheme := quasiSeparatedSpace_of_quasiSeparated z
  have comparison {T : Scheme.{u}} (t : T ⟶ Spec (R.obj i)) :
      Scheme.Modules.HasSupportProperOver (pullback.snd f t)
        ((Scheme.Modules.tensorPullback (pullback.fst f t)).obj Fi) ↔
      IsProper (pullback.snd a t) := by
    let k : pullback a t ⟶ pullback f t :=
      pullback.lift (pullback.fst a t ≫ z) (pullback.snd a t)
        (by simpa [a, Category.assoc] using (pullback.condition (f := a) (g := t)))
    have hkfst : k ≫ pullback.fst f t = pullback.fst a t ≫ z :=
      pullback.lift_fst _ _ _
    have hksnd : k ≫ pullback.snd f t = pullback.snd a t :=
      pullback.lift_snd _ _ _
    have H : IsPullback (pullback.fst a t) k z (pullback.fst f t) := by
      apply IsPullback.of_bot (v₂₁ := pullback.snd f t) (v₂₂ := f)
      · rw [hksnd]
        exact IsPullback.of_hasPullback a t
      · exact hkfst.symm
      · exact IsPullback.of_hasPullback f t
    have : IsClosedImmersion k :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) H inferInstance
    have hr : Set.range k.base =
        {x : ↥(pullback f t) | ¬ Subsingleton
          (((Scheme.Modules.tensorPullback (pullback.fst f t)).obj Fi).presheaf.stalk x)} := by
      rw [Scheme.range_snd_of_isPullback H, hsupport]
      exact ((Scheme.Modules.finiteType_module_support_pullback Fi).2.2 _ _).2.symm
    constructor
    · rintro ⟨W, hW, hp⟩
      have hp' := (Scheme.closed_subset_proper_over_base_properties
        (pullback.snd f t) W).2.1.mp hp _ k (hr.trans hW.symm)
      rwa [hksnd] at hp'
    · intro hp
      let W : TopologicalSpace.Closeds ↥(pullback f t) :=
        ⟨Set.range k.base, k.isClosedEmbedding.isClosed_range⟩
      refine ⟨W, hr, ?_⟩
      apply (Scheme.closed_subset_proper_over_base_properties (pullback.snd f t) W).1.mpr
      refine ⟨pullback a t, k, inferInstance, rfl, ?_⟩
      rwa [hksnd]
  have hp : IsProper (pullback.snd a (c.π.app (op i))) :=
    (comparison _).mp hF
  let D := R.op ⋙ Scheme.Spec
  have {j k : Iᵒᵖ} (t : j ⟶ k) : IsAffineHom (D.map t) := by
    dsimp [D]
    infer_instance
  have : CompactSpace (D.obj (op i)) := by dsimp [D]; infer_instance
  have : QuasiSeparatedSpace (D.obj (op i)) := by dsimp [D]; infer_instance
  let ψ := pullback.map a (c.π.app (op i)) (𝟙 (Spec (R.obj i)))
    (c.π.app (op i)) a (𝟙 c.pt) (𝟙 (Spec (R.obj i)))
    (Category.comp_id a) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hψ : IsProper ψ := by
    have he : ψ ≫ pullback.snd (𝟙 (Spec (R.obj i))) (c.π.app (op i)) =
        pullback.snd a (c.π.app (op i)) := by
      simp only [ψ, pullback.map, pullback.lift_snd]
      exact Category.comp_id _
    rw [← he] at hp
    exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).mp hp
  obtain ⟨j, hij, hj⟩ := exists_isProper_baseChange_of_isLimit D c hc i
    a (𝟙 (Spec (R.obj i))) a (by simp) hψ
  refine ⟨j, hij, (comparison _).mpr ?_⟩
  have he :
      (pullback.map a (D.map (homOfLE hij).op) (𝟙 (Spec (R.obj i)))
        (D.map (homOfLE hij).op) a (𝟙 (D.obj (op j))) (𝟙 (Spec (R.obj i)))
        (Category.comp_id a) (Category.comp_id _)) ≫
        pullback.snd (𝟙 (Spec (R.obj i))) (D.map (homOfLE hij).op) =
      pullback.snd a (D.map (homOfLE hij).op) := by
    simp only [pullback.map, pullback.lift_snd]
    exact Category.comp_id _
  change IsProper (pullback.snd a (D.map (homOfLE hij).op))
  rw [← he]
  have := hj
  infer_instance

end AlgebraicGeometry
