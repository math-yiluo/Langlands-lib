/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Vanishing of pro-etale shriek sections near a disjoint closed subset

## References

* Stacks Project, Tag 09AG
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

private theorem exists_closed_specialization_localization
    (T : Scheme.{u}) [IsAffine T] (C : Set T) (hC : IsClosed C) :
    ∃ (W : Scheme.{u}) (f : W ⟶ T), IsAffine W ∧ WeaklyEtale f ∧
      (∀ t : T, (∃ c ∈ C, Specializes t c) → t ∈ Set.range f) ∧
      (∀ w : W, ∃ w' : W, Specializes w w' ∧ f w' ∈ C) := by
  let A := Γ(T, ⊤)
  let e : T ≅ Spec A := T.isoSpec
  obtain ⟨I, hI⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (e.hom '' C)).mp
      (e.hom.isClosedMap C hC)
  let S : Submonoid A := (IsUnit.submonoid (A ⧸ I)).comap (Ideal.Quotient.mk I)
  obtain ⟨hwe, _hemb, hrange, _hC, hspec⟩ :=
    affineClosedSpecializationLocalization A I S (fun _ ↦ Iff.rfl)
  let W := Spec (CommRingCat.of (Localization S))
  let l : W ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A (Localization S)))
  let f : W ⟶ T := l ≫ e.inv
  have := hwe
  refine ⟨W, f, inferInstance, inferInstance, ?_, ?_⟩
  · rintro t ⟨c, hc, htc⟩
    have hcI : I ≤ (e.hom c).asIdeal := by
      have hmem : e.hom c ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
        rw [← hI]
        exact ⟨c, hc, rfl⟩
      exact hmem
    have hle : (e.hom t).asIdeal ≤ (e.hom c).asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
        ((PrimeSpectrum.le_iff_specializes _ _).mpr (htc.map e.hom.continuous))
    obtain ⟨w, hw⟩ : e.hom t ∈
        Set.range (PrimeSpectrum.comap (algebraMap A (Localization S))) := by
      rw [hrange]
      exact ⟨e.hom c, hcI, hle⟩
    refine ⟨w, ?_⟩
    change e.inv (l w) = t
    change l w = e.hom t at hw
    rw [hw]
    exact Scheme.hom_inv_apply e t
  · intro w
    obtain ⟨w', hww', hw'I⟩ := hspec w
    refine ⟨w', hww', ?_⟩
    have hmem : l w' ∈ e.hom '' C := by
      rw [hI]
      exact hw'I
    obtain ⟨c, hc, hec⟩ := hmem
    change e.inv (l w') ∈ C
    rw [← hec]
    simpa using hc

set_option backward.isDefEq.respectTransparency false in
private theorem exists_specialization_cover_refinement
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hspecializes : ∀ v : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes v ((pullback.fst V.hom i) z))
    (S : Sieve V) (hS : S ∈ topology X V) :
    ∃ (n : ℕ) (W : Fin n → X.ProEt) (f : ∀ j, W j ⟶ V),
      Presieve.ofArrows W f ∈ precoverage X V ∧
      ∀ j, S (f j) ∧ ∀ w : (W j).left, ∃ z : ↥(pullback (W j).hom i),
        Specializes w ((pullback.fst (W j).hom i) z) := by
  classical
  obtain ⟨R, hR, hle⟩ := mem_topology_iff.mp hS
  obtain ⟨κ, T, g, rfl⟩ := R.exists_eq_ofArrows
  let E : PreZeroHypercover V.left :=
    ⟨κ, fun k ↦ (T k).left, fun k ↦ (g k).left⟩
  have hE : E.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    rw [mem_precoverage_iff, Presieve.map_ofArrows] at hR
    exact hR
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE.1
  obtain ⟨n, k, O, hO, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E
      (U := ⊤) isCompact_univ
  let A : Fin n → Scheme.{u} := fun j ↦ (O j).toScheme
  let a : ∀ j, A j ⟶ V.left := fun j ↦ (O j).ι ≫ (g (k j)).left
  have ha (j : Fin n) : WeaklyEtale (a j) := by
    have hcomp : WeaklyEtale ((g (k j)).left ≫ V.hom) :=
      (MorphismProperty.Over.w (g (k j))) ▸ (T (k j)).prop
    have := WeaklyEtale.of_comp (g (k j)).left V.hom
    dsimp [a]
    infer_instance
  have hA (j : Fin n) : IsAffine (A j) := hO j
  let C : ∀ j, Set (A j) := fun j ↦ (a j ≫ V.hom) ⁻¹' Set.range i
  have hC (j : Fin n) : IsClosed (C j) :=
    i.isClosedEmbedding.isClosed_range.preimage (a j ≫ V.hom).continuous
  choose B b hB hb hreach hspec using
    fun j ↦ exists_closed_specialization_localization (A j) (C j) (hC j)
  let W : Fin n → X.ProEt := fun j ↦
    have := hb j
    have := ha j
    ProEt.mk (b j ≫ a j ≫ V.hom)
  let f : ∀ j, W j ⟶ V := fun j ↦
    MorphismProperty.Over.homMk (b j ≫ a j) (Category.assoc _ _ _)
  have hsurj : ∀ v : V.left, ∃ j, v ∈ Set.range (f j).left := by
    intro v
    obtain ⟨z, hvz⟩ := hspecializes v
    have hzcover : (pullback.fst V.hom i) z ∈
        ⋃ j, (g (k j)).left '' (O j) := by
      rw [hcover]
      trivial
    obtain ⟨j, t, ht, htz⟩ := Set.mem_iUnion.mp hzcover
    let t' : A j := ⟨t, ht⟩
    have hat : a j t' = (pullback.fst V.hom i) z := htz
    have := ha j
    obtain ⟨v', hv't, hv'v⟩ :=
      Flat.generalizingMap (a j) (hat ▸ hvz)
    have htC : t' ∈ C j := by
      refine ⟨(pullback.snd V.hom i) z, ?_⟩
      change i _ = V.hom (a j t')
      rw [hat]
      exact (congrArg (fun q : pullback V.hom i ⟶ X ↦ q z)
        (pullback.condition (f := V.hom) (g := i))).symm
    obtain ⟨w, hw⟩ := hreach j v' ⟨t', htC, hv't⟩
    refine ⟨j, w, ?_⟩
    change a j (b j w) = v
    rw [hw, hv'v]
  refine ⟨n, W, f, ?_, ?_⟩
  · rw [mem_precoverage_iff, Presieve.map_ofArrows]
    refine ⟨?_, ?_⟩
    · let E' : PreZeroHypercover V.left :=
        ⟨Fin n, fun j ↦ (W j).left, fun j ↦ (f j).left⟩
      change E'.presieve₀ ∈ Scheme.qcPrecoverage V.left
      rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      refine ⟨fun {H} hH ↦ ?_⟩
      have (j : Fin n) : IsAffine (W j).left := hB j
      exact IsCompactOpenCovered.of_finite_of_isSpectralMap
        (fun j ↦ (f j).left.isSpectralMap) (fun v _ ↦ hsurj v) H.2 hH.isCompact
    · apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
      refine ⟨hsurj, fun j ↦ ?_⟩
      have := hb j
      have := ha j
      change WeaklyEtale (b j ≫ a j)
      infer_instance
  · intro j
    constructor
    · let o : W j ⟶ T (k j) :=
        MorphismProperty.Over.homMk (b j ≫ (O j).ι) (by
          change (b j ≫ (O j).ι) ≫ (T (k j)).hom = b j ≫ a j ≫ V.hom
          simpa only [a, Category.assoc] using
            (congrArg (fun q ↦ b j ≫ (O j).ι ≫ q)
              (MorphismProperty.Over.w (g (k j)))).symm)
      have heq : o ≫ g (k j) = f j := by
        apply MorphismProperty.Over.Hom.ext
        exact Category.assoc _ _ _
      rw [← heq]
      exact S.downward_closed (hle _ _ ⟨k j⟩) o
    · intro w
      obtain ⟨w', hww', z, hz⟩ := hspec j w
      have hz' : (W j).hom w' = i z := hz.symm
      obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback w' z hz'
      exact ⟨q, hq.symm ▸ hww'⟩

private theorem empty_of_lift_of_specializes_closed
    {X Z : Scheme.{u}} (U : X.ProEt) (i : Z ⟶ X)
    (hdisjoint : IsEmpty ↥(pullback U.hom i)) (W : X.ProEt)
    (hspecializes : ∀ w : W.left, ∃ z : ↥(pullback W.hom i),
      Specializes w ((pullback.fst W.hom i) z))
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom) : IsEmpty W.left := by
  refine ⟨fun w ↦ ?_⟩
  obtain ⟨z, _hz⟩ := hspecializes w
  let b : pullback W.hom i ⟶ pullback U.hom i :=
    pullback.lift (pullback.fst W.hom i ≫ a) (pullback.snd W.hom i) (by
      rw [Category.assoc, ha, pullback.condition])
  exact hdisjoint.elim (b z)

private theorem shriek_presheaf_subsingleton_of_specializes_closed
    {X Z : Scheme.{u}} (U : X.ProEt) (i : Z ⟶ X)
    (hdisjoint : IsEmpty ↥(pullback U.hom i)) (W : X.ProEt)
    (hspecializes : ∀ w : W.left, ∃ z : ↥(pullback W.hom i),
      Specializes w ((pullback.fst W.hom i) z))
    (G : Sheaf (topology U.left) AddCommGrpCat.{u + 1}) :
    Subsingleton
      (((MorphismProperty.Over.map ⊤ U.prop).op.leftKanExtension G.obj).obj (op W)) := by
  let L := (MorphismProperty.Over.map ⊤ U.prop).op
  let P := L.leftKanExtension G.obj
  let E := Functor.LeftExtension.mk P (L.leftKanExtensionUnit G.obj)
  let hE := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    P (L.leftKanExtensionUnit G.obj) (op W)
  obtain ⟨ι, s, hs, hiso⟩ :=
    SmallSite.exists_final_discrete_costructuredArrow_overMap U.prop W
  have := hs
  have hzero : IsZero (s ⋙ CostructuredArrow.proj L (op W) ⋙ G.obj) := by
    apply Functor.isZero
    intro j
    let T := (s.obj j).left.unop
    let a := (s.obj j).hom.unop
    have hW : IsEmpty W.left := empty_of_lift_of_specializes_closed U i hdisjoint W
      hspecializes (a.left ≫ T.hom) (by
        have ha := MorphismProperty.Over.w a
        change a.left ≫ (T.hom ≫ U.hom) = W.hom at ha
        simpa only [Category.assoc] using ha)
    have := hW
    have := hiso j
    have : IsIso a := inferInstanceAs (IsIso (s.obj j).hom.unop)
    have : IsIso a.left := inferInstance
    have : IsEmpty T.left := ⟨fun t ↦ hW.elim ((inv a.left) t)⟩
    exact (isTerminalSectionsOfIsEmpty G T).isZero
  exact AddCommGrpCat.subsingleton_of_isZero
    (((Functor.Final.isColimitWhiskerEquiv s (E.coconeAt (op W))).symm hE).isZero_pt hzero)

/-- Shriek sections vanish on an affine object all of whose points specialize to the
closed fibre disjoint from the source, where `j_!` is the sheafified left Kan extension along
the localization functor (the direct-sum presheaf indexed by lifts to `U`). -/
theorem shriek_sections_subsingleton_of_specializes_closed
    {X Z : Scheme.{u}} (U : X.ProEt) (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty ↥(pullback U.hom i))
    (V : X.ProEt) [IsAffine V.left]
    (hspecializes : ∀ v : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes v ((pullback.fst V.hom i) z))
    (G : Sheaf (topology U.left) AddCommGrpCat.{u + 1}) :
    Subsingleton
      ((sheafify (topology X)
        ((MorphismProperty.Over.map ⊤ U.prop).op.leftKanExtension G.obj)).obj (op V)) := by
  let P := (MorphismProperty.Over.map ⊤ U.prop).op.leftKanExtension G.obj
  let F := sheafify (topology X) P
  let η := toSheafify (topology X) P
  have hF : Presieve.IsSheaf (topology X) (F ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp
        ((presheafToSheaf (topology X) AddCommGrpCat.{u + 1}).obj P).property)
  have hη : Presheaf.IsLocallySurjective (topology X) η := inferInstance
  refine ⟨fun s t ↦ ?_⟩
  suffices hs : ∀ s : F.obj (op V), s = 0 from (hs s).trans (hs t).symm
  intro s
  obtain ⟨n, W, f, hcover, hW⟩ := exists_specialization_cover_refinement i V
    hspecializes (Presheaf.imageSieve η s) (Presheaf.imageSieve_mem (topology X) η s)
  apply (hF.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
  rintro T f' ⟨j⟩
  obtain ⟨p, hp⟩ := (hW j).1
  have : Subsingleton (P.obj (op (W j))) :=
    shriek_presheaf_subsingleton_of_specializes_closed U i hdisjoint (W j) (hW j).2 G
  change F.map (f j).op s = F.map (f j).op 0
  rw [← hp, Subsingleton.elim p 0]
  simp

end AlgebraicGeometry.Scheme.ProEt
