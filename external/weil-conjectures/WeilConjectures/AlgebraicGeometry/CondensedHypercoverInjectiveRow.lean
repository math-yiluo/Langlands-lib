/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverAugmentation
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentation
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverLocalLifting
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Augmented hypercover rows for injective internal modules -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Simplicial
namespace AlgebraicGeometry.ProEtale

private lemma ab_hom_sum {P Q : AddCommGrpCat.{u + 1}} {α : Type*} [Fintype α]
    (f : α → (P ⟶ Q)) : (∑ j, f j).hom = ∑ j, (f j).hom :=
  map_sum AddCommGrpCat.homAddEquiv f Finset.univ

private theorem singleAugmentation_quasiIso
    (K : CochainComplex AddCommGrpCat.{u + 1} ℕ)
    (M : AddCommGrpCat.{u + 1})
    (f : (CochainComplex.single₀ _).obj M ⟶ K)
    (hinj : Function.Injective (f.f 0).hom)
    (hzero : Function.Exact (f.f 0).hom (K.d 0 1).hom)
    (hpos : ∀ n : ℕ, K.ExactAt (n + 1)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
      ⟨(ShortComplex.ab_exact_iff_function_exact _).mpr hzero,
        (AddCommGrpCat.mono_iff_injective _).mpr hinj⟩
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 1
    · exact HomologicalComplex.single_obj_d (.up ℕ) 0 M 0 0
    · exact K.shape 0 0 (by simp)
  | succ n =>
    exact (quasiIsoAt_iff_exactAt f (n + 1)
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

-- Transport through two module equivalences needs explicit sectionwise type comparison.
set_option backward.isDefEq.respectTransparency false in
/-- The augmented alternating section row of an injective internal module is exact.
Source: Stacks Project, Tags 09A2, 01GE and 01GW; Hemo--Richarz--Scholbach,
Lemma 5.3(1), the hypercover calculation.
(auxiliary; not a blueprint node).
Proof: reconstruct the section-ring sheaf and transport I through the proved
internal/sectionwise module equivalence. Its forward functor leaves the underlying
abelian sheaf and all restriction maps unchanged, and the equivalence preserves
injectives. Lift the site morphism universe using ULiftHom and transport the
ringed module along this site equivalence, preserving injectivity once more.
The given represented matching-map epimorphisms imply local lifting of every
finite compatible boundary. Apply the ringed hypercover injective augmentation
exactness theorem: its augmented free-module resolution is locally exact, and
Hom into the transported injective gives an injective augmentation, exactness at
simplicial degree zero, and exactness in each positive degree. These are statements
about functions on section groups. They identify definitionally with the underlying
abelian section functions; expand the alternating differential to identify them
with exactness of the abelian cochain row. The single-degree augmentation is
therefore a quasi-isomorphism. Extension by zero preserves this quasi-isomorphism,
and the canonical single-complex extension isomorphism identifies it with the
augmentation asserted here. This also covers an empty W. -/
theorem condensedHypercoverInjectiveRow
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (W : X.ProEt) (U : SimplicialObject (Over W))
    (hzero : Epi ((Scheme.ProEt.topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((Scheme.ProEt.topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((Scheme.ProEt.topology X).yoneda.map μ.left))
    (I : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X)) [Injective I] :
    QuasiIso (Scheme.ProEt.abelianHypercoverRowAugmentationComplex X W U
      ((Mod.forget (condensedRingObj Λ X)).obj I)) := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let E₀ := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let I₀ := (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj I
  have : Injective I₀ := by
    change Injective (E₀.functor.obj I)
    exact (E₀.map_injective_iff I).mpr inferInstance
  let C' := ULiftHom.{u + 1} X.ProEt
  let up : X.ProEt ⥤ C' := ULiftHom.up
  let down : C' ⥤ X.ProEt := ULiftHom.down
  let top' := down.inducedTopology (Scheme.ProEt.topology X)
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsEquivalence)
  have : down.IsContinuous top' (Scheme.ProEt.topology X) := by dsimp [top', down]; infer_instance
  have : up.IsContinuous (Scheme.ProEt.topology X) top' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.ProEt ≌ C').functor.IsContinuous
      (Scheme.ProEt.topology X)
        ((ULiftHom.equiv : X.ProEt ≌ C').inverse.inducedTopology (Scheme.ProEt.topology X)))
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).functor.IsContinuous top'
      (Scheme.ProEt.topology X) := by
    change down.IsContinuous top' (Scheme.ProEt.topology X)
    infer_instance
  have : (ULiftHom.equiv.symm : C' ≌ X.ProEt).inverse.IsContinuous
      (Scheme.ProEt.topology X) top' := by
    change up.IsContinuous (Scheme.ProEt.topology X) top'
    infer_instance
  let pc := (Scheme.ProEt.precoverage X).comap down
  have hpc : pc.toGrothendieck = top' := by
    change pc.toGrothendieck = down.inducedTopology (Scheme.ProEt.topology X)
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
    GrothendieckTopology.subcanonical_of_full_of_faithful down top' (Scheme.ProEt.topology X)
  let R' := (down.sheafPushforwardContinuous CommRingCat.{u + 1}
    top' (Scheme.ProEt.topology X)).obj R
  let RR := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let RR' := (sheafCompose top'
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'
  let E : SheafOfModules.{u + 1} RR ≌ SheafOfModules.{u + 1} RR' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.ProEt) (𝟙 RR') (𝟙 RR)
      (by ext V x; change (RR.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (RR.obj.map (𝟙 _)).hom x = x; simp)
  let I₀' : SheafOfModules.{u + 1} RR' := E.functor.obj I₀
  have : Injective I₀' := (E.map_injective_iff I₀).mpr inferInstance
  have : pc.toGrothendieck.Subcanonical := by rw [hpc]; infer_instance
  have hseq' := ringedHypercover_injective_augmentation_exact.{u + 1, u + 1, u + 1} pc
  rw [hpc] at hseq'
  have hseq := hseq' R' I₀' (up.obj W) (U ⋙ Over.forget W ⋙ up)
    (Functor.whiskerRight (Scheme.ProEt.hypercoverUnderlyingAugmentation X W U) up) (by
      intro n T w p hp hcomp
      obtain ⟨S, hS, hlift⟩ := Scheme.ProEt.hypercover_matching_local_lifting X W U
        hzero hone hhigher n (down.obj T) (down.map w)
        (fun Δ h θ ↦ down.map (p Δ h θ))
        (fun Δ h θ ↦ congrArg down.map (hp Δ h θ))
        (fun Δ Δ' h h' α θ ↦ congrArg down.map (hcomp Δ Δ' h h' α θ))
      refine ⟨S.functorPullback down, ?_, ?_⟩
      · change _ ∈ down.inducedTopology (Scheme.ProEt.topology X) T
        rw [← Functor.restrictedTopology_eq_inducedTopology]
        exact Functor.IsCocontinuous.cover_lift hS
      · intro V f hf
        obtain ⟨t, ht, htp⟩ := hlift (down.obj V) (down.map f) hf
        exact ⟨ULift.up t, congrArg ULift.up ht,
          fun Δ h θ ↦ congrArg ULift.up (htp Δ h θ)⟩)
  let row := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
    ((Scheme.ProEt.abelianHypercoverSections X W U).obj I.X)
  let a : (CochainComplex.single₀ _).obj
      (((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj
        I.X) ⟶ row :=
    (CochainComplex.fromSingle₀Equiv row _).symm
      ⟨Scheme.ProEt.abelianHypercoverRestrictionZero X W U I.X,
        Scheme.ProEt.abelianHypercoverRestrictionZero_d X W U I.X⟩
  have hd (n : ℕ) (s : row.X n) :
      (row.d n (n + 1)).hom s =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.X.obj.map (U.δ j).left.op s := by
    change ((AlgebraicTopology.AlternatingCofaceMapComplex.obj
      ((Scheme.ProEt.abelianHypercoverSections X W U).obj I.X)).d n (n + 1)).hom s = _
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      CochainComplex.of_d, AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (((Scheme.ProEt.abelianHypercoverSections X W U).obj I.X).δ j)).hom s = _
    simp only [ab_hom_sum, AddCommGrpCat.hom_zsmul,
      AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
    rfl
  have ha : QuasiIso a := by
    apply singleAugmentation_quasiIso row _ a
    · have h := hseq.1
      change Function.Injective (I₀.val.map (U _⦋0⦌).hom.op) at h
      change Function.Injective (Scheme.ProEt.abelianHypercoverRestrictionZero X W U I.X).hom
      intro x y hxy
      apply h
      simp only [Scheme.ProEt.abelianHypercoverRestrictionZero_apply] at hxy
      convert! hxy using 1
    · have h := hseq.2.1
      change Function.Exact (I₀.val.map (U _⦋0⦌).hom.op)
        (fun s ↦ ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I₀.val.map (U.δ j).left.op s) at h
      change Function.Exact
        (fun x ↦ (Scheme.ProEt.abelianHypercoverRestrictionZero X W U I.X).hom x)
        (fun x ↦ (row.d 0 1).hom x)
      simp only [Scheme.ProEt.abelianHypercoverRestrictionZero_apply, hd]
      exact h
    · intro n
      rw [HomologicalComplex.exactAt_iff' row n (n + 1) (n + 2) (by simp) (by simp)]
      apply (ShortComplex.ab_exact_iff_function_exact _).mpr
      have h := hseq.2.2 n
      change Function.Exact
        (fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I₀.val.map (U.δ j).left.op s)
        (fun s ↦ ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I₀.val.map (U.δ j).left.op s) at h
      change Function.Exact (fun x ↦ (row.d n (n + 1)).hom x)
        (fun x ↦ (row.d (n + 1) (n + 2)).hom x)
      simp only [hd]
      exact h
  have he : QuasiIso (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) :=
    inferInstance
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj I.X)
      0 0 rfl) (Iso.refl _) ?_)).mp he
  apply (cancel_epi (HomologicalComplex.extendSingleIso
    ComplexShape.embeddingUpNat
      (((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op W)).obj I.X)
      0 0 rfl).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f]
  erw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat (i := 0) rfl]
  simp [Scheme.ProEt.abelianHypercoverRowAugmentationComplex,
    Scheme.ProEt.abelianHypercoverRowAugmentation, a]
  rfl

end AlgebraicGeometry.ProEtale
