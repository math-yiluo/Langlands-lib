/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverAugmentation
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentation
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverLocalLifting
import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtaleRepresentableEpiLocalLifting
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Injective row descent on a pro-etale hypercover

## References

* Stacks Project, Hypercoverings, Tags 01GE and 01GW
* Stacks Project, Tags 01GE and 01GW, ringed-module analogue
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

private theorem singleAugmentation_quasiIso
    {A : Type*} [Ring A] (K : CochainComplex (ModuleCat.{u + 1} A) ℕ)
    (M : ModuleCat.{u + 1} A)
    (f : (CochainComplex.single₀ _).obj M ⟶ K)
    (hinj : Function.Injective (f.f 0))
    (hzero : Function.Exact (f.f 0) (K.d 0 1))
    (hpos : ∀ n : ℕ, K.ExactAt (n + 1)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
      ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hzero,
        (ModuleCat.mono_iff_injective _).mpr hinj⟩
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 1
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 0
    · exact K.shape 0 0 (by simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt f (n + 1)
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

-- Transporting the ringed site unfolds its pushforward and scalar restriction functors.
set_option backward.isDefEq.respectTransparency false in
/-- The augmented section row of an injective module sheaf on a representable
hypercover is quasi-isomorphic, independently of weak contractibility. -/
theorem hypercoverRowAugmentationComplex_quasiIso_of_injective
    (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left))
    (I : ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [Injective I] : QuasiIso (hypercoverRowAugmentationComplex X R W U I) := by
  let C' := ULiftHom.{u + 1} X.ProEt
  let up : X.ProEt ⥤ C' := ULiftHom.up
  let down : C' ⥤ X.ProEt := ULiftHom.down
  let top' := down.inducedTopology (topology X)
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsEquivalence)
  have : down.IsContinuous top' (topology X) := by dsimp [top', down]; infer_instance
  have : up.IsContinuous (topology X) top' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsContinuous
      (topology X) ((ULiftHom.equiv : X.ProEt ≌ C').inverse.inducedTopology (topology X)))
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).functor.IsContinuous top'
      (topology X) := by change down.IsContinuous top' (topology X); infer_instance
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).inverse.IsContinuous
      (topology X) top' := by change up.IsContinuous (topology X) top'; infer_instance
  let pc := (precoverage X).comap down
  have hpc : pc.toGrothendieck = top' := by
    change pc.toGrothendieck = down.inducedTopology (topology X)
    rw [← Functor.restrictedTopology_eq_inducedTopology]
    apply Precoverage.toGrothendieck_comap_eq_restrictedTopology
    intro V S hS
    convert hS using 1
    funext Y f
    apply propext
    rw [Presieve.map_iff]
    constructor
    · rintro ⟨Z, hZ, g, hg, he⟩
      subst hZ
      have he' : down.map g = f := by simpa using he
      exact he' ▸ hg
    · intro hf
      exact ⟨up.obj Y, rfl, ULift.up f, hf, rfl⟩
  have : top'.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful down top' (topology X)
  let R' := (down.sheafPushforwardContinuous CommRingCat.{u + 1}
    top' (topology X)).obj R
  let RR := (sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let RR' := (sheafCompose top'
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'
  let E : SheafOfModules.{u + 1} RR ≌ SheafOfModules.{u + 1} RR' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.ProEt) (𝟙 RR') (𝟙 RR)
      (by ext V x; change (RR.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (RR.obj.map (𝟙 _)).hom x = x; simp)
  let I' : SheafOfModules.{u + 1} RR' := E.functor.obj I
  have : Injective I' := (E.map_injective_iff I).mpr inferInstance
  have : pc.toGrothendieck.Subcanonical := by rw [hpc]; infer_instance
  have hseq' := ringedHypercover_injective_augmentation_exact.{u + 1, u + 1, u + 1} pc
  rw [hpc] at hseq'
  have hseq := hseq' R' I' (up.obj W) (U ⋙ Over.forget W ⋙ up)
    (Functor.whiskerRight (hypercoverUnderlyingAugmentation X W U) up) (by
      intro n T w p hp hcomp
      obtain ⟨S, hS, hlift⟩ := hypercover_matching_local_lifting X W U
        hzero hone hhigher n (down.obj T) (down.map w)
        (fun Δ h θ ↦ down.map (p Δ h θ))
        (fun Δ h θ ↦ congrArg down.map (hp Δ h θ))
        (fun Δ Δ' h h' α θ ↦ congrArg down.map (hcomp Δ Δ' h h' α θ))
      refine ⟨S.functorPullback down, ?_, ?_⟩
      · change _ ∈ down.inducedTopology (topology X) T
        rw [← Functor.restrictedTopology_eq_inducedTopology]
        exact Functor.IsCocontinuous.cover_lift hS
      · intro V f hf
        obtain ⟨t, ht, htp⟩ := hlift (down.obj V) (down.map f) hf
        exact ⟨ULift.up t, congrArg ULift.up ht,
          fun Δ h θ ↦ congrArg ULift.up (htp Δ h θ)⟩)
  let row := (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    ((hypercoverSections X R W U).obj I)
  let a : (CochainComplex.single₀ _).obj
      ((SheafOfModules.evaluation _ (op W)).obj I) ⟶ row :=
    (CochainComplex.fromSingle₀Equiv row _).symm
      ⟨hypercoverRestrictionZero X R W U I, by exact hypercoverRestrictionZero_d X R W U I⟩
  have hd (n : ℕ) (s : row.X n) :
      (row.d n (n + 1)) s =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).left.op s := by
    change ((AlgebraicTopology.AlternatingCofaceMapComplex.obj
      ((hypercoverSections X R W U).obj I)).d n (n + 1)) s = _
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      CochainComplex.of_d, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (((hypercoverSections X R W U).obj I).δ j)).hom s = _
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  have ha : QuasiIso a := by
    apply singleAugmentation_quasiIso row _ a
    · have h := hseq.1
      change Function.Injective (I.val.map (U _⦋0⦌).hom.op) at h
      change Function.Injective (hypercoverRestrictionZero X R W U I)
      intro x y hxy
      apply h
      simpa only [hypercoverRestrictionZero_apply] using hxy
    · have h := hseq.2.1
      change Function.Exact (I.val.map (U _⦋0⦌).hom.op)
        (fun s ↦ ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (U.δ j).left.op s) at h
      change Function.Exact (fun x ↦ hypercoverRestrictionZero X R W U I x)
        (fun x ↦ (row.d 0 1) x)
      simp only [hypercoverRestrictionZero_apply, hd]
      exact h
    · intro n
      rw [HomologicalComplex.exactAt_iff' row n (n + 1) (n + 2) (by simp) (by simp)]
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      have h := hseq.2.2 n
      change Function.Exact
        (fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).left.op s)
        (fun s ↦ ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).left.op s) at h
      change Function.Exact (fun x ↦ (row.d n (n + 1)) x)
        (fun x ↦ (row.d (n + 1) (n + 2)) x)
      simp only [hd]
      exact h
  have he : QuasiIso (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) :=
    inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((SheafOfModules.evaluation _ (op W)).obj I) 0 0 rfl) (Iso.refl _) ?_)).mp he
  apply (cancel_epi (HomologicalComplex.extendSingleIso
    ComplexShape.embeddingUpNat ((SheafOfModules.evaluation _ (op W)).obj I)
      0 0 rfl).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f]
  erw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat (i := 0) rfl]
  simp [hypercoverRowAugmentationComplex, hypercoverRowAugmentation, a]
  rfl

end AlgebraicGeometry.Scheme.ProEt
