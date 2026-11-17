import Langlands.AlgebraicGeometry.EtaleGenericPullback
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Generic sections of étale locally constant parameters over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Flat base change preserves dominance of the chosen generic-point map. -/
theorem isDominant_genericPullbackFst
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsDominant (pullback.fst f (Spec.algebraMap R K)) := by
  have : IsDominant (Spec.algebraMap R K) := isDominant_fractionFieldMap R K
  have : IsSchemeTheoreticallyDominant (Spec.algebraMap R K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  infer_instance

/-- On a connected étale trivialization, a generic section selects one summand
and therefore extends over the entire cover. -/
theorem exists_section_on_connected_etale_trivialization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R)))
    {U : Scheme.{u}} [ConnectedSpace U] (q : U ⟶ Spec (CommRingCat.of R)) [Etale q]
    (I : Type u)
    (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U)))
    (p : Over.mk (Spec.algebraMap R K) ⟶ C) :
    ∃ s : U ⟶ C.left, s ≫ C.hom = q ∧
      pullback.fst q (Spec.algebraMap R K) ≫ s =
        pullback.snd q (Spec.algebraMap R K) ≫ p.left := by
  let b := Spec.algebraMap R K
  let V : Scheme.{u} := pullback q b
  let j : V ⟶ U := pullback.fst q b
  let t : V ⟶ Spec (CommRingCat.of K) := pullback.snd q b
  have : ConnectedSpace V := connectedSpace_etale_genericPullback R K q
  let a : V ⟶ ((Over.pullback q).obj C).left :=
    pullback.lift (t ≫ p.left) j (by
      rw [Category.assoc, Over.w p]
      exact (pullback.condition (f := q) (g := b)).symm)
  have hehom : e.hom.left ≫ Sigma.desc (fun _ : I => 𝟙 U) =
      pullback.snd C.hom q := by simpa using Over.w e.hom
  have heinv : e.inv.left ≫ pullback.snd C.hom q =
      Sigma.desc (fun _ : I => 𝟙 U) := by simpa using Over.w e.inv
  let d : V ⟶ ∐ (fun _ : I => U) := a ≫ e.hom.left
  have hd : d ≫ Sigma.desc (fun _ : I => 𝟙 U) = j := by
    dsimp only [d]
    rw [Category.assoc, hehom]
    exact pullback.lift_snd _ _ _
  obtain ⟨i, c, hc⟩ := connectedHom_factor_coproduct (fun _ : I => U) d
  have hci : c = j := by
    simpa only [Category.assoc, Sigma.ι_comp_desc, Category.comp_id] using
      (congrArg (fun z => z ≫ Sigma.desc (fun _ : I => 𝟙 U)) hc).trans hd
  have hji : j ≫ Sigma.ι (fun _ : I => U) i = d := by rwa [hci] at hc
  let s : U ⟶ C.left :=
    Sigma.ι (fun _ : I => U) i ≫ e.inv.left ≫ pullback.fst C.hom q
  refine ⟨s, ?_, ?_⟩
  · dsimp only [s]
    rw [Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc e.inv.left, heinv, ← Category.assoc,
      Sigma.ι_comp_desc, Category.id_comp]
  · change j ≫ s = t ≫ p.left
    dsimp only [s]
    rw [← Category.assoc, hji]
    dsimp only [d]
    simp only [Category.assoc, Over.hom_left_inv_left_assoc]
    exact pullback.lift_fst _ _ _

/-- A generic section of a separated parameter with an actual connected étale
coproduct trivialization extends uniquely over a DVR. -/
theorem existsUnique_section_of_connected_etale_trivialization
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsSeparated C.hom]
    {U : Scheme.{u}} [ConnectedSpace U] (q : U ⟶ Spec (CommRingCat.of R))
    [Etale q] [Surjective q] (I : Type u)
    (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U)))
    (p : Over.mk (Spec.algebraMap R K) ⟶ C) :
    ∃! s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C,
      Over.homMk (Spec.algebraMap R K) ≫ s = p := by
  let b := Spec.algebraMap R K
  obtain ⟨sU, hbase, hgen⟩ :=
    exists_section_on_connected_etale_trivialization R K C q I e p
  have hgen' {T : Scheme.{u}} (r : T ⟶ U) (t : T ⟶ Spec (CommRingCat.of K))
      (w : r ≫ q = t ≫ b) : r ≫ sU = t ≫ p.left := by
    let l := pullback.lift r t w
    calc
      r ≫ sU = l ≫ pullback.fst q b ≫ sU := by simp only [l, pullback.lift_fst_assoc]
      _ = l ≫ pullback.snd q b ≫ p.left := by rw [hgen]
      _ = t ≫ p.left := by simp only [l, pullback.lift_snd_assoc]
  let W : Scheme.{u} := pullback q q
  let f : W ⟶ Spec (CommRingCat.of R) := pullback.fst q q ≫ q
  have : IsReduced W := SmoothReducedBase.isReduced_of_smooth_of_isReduced f
  have : IsDominant (pullback.fst f b) := isDominant_genericPullbackFst R K f
  have hagree : pullback.fst q q ≫ sU = pullback.snd q q ≫ sU := by
    apply ext_of_isDominant_of_isSeparated C.hom
      (by simp only [Category.assoc, hbase, pullback.condition]) (pullback.fst f b)
    have h₁ := hgen' (pullback.fst f b ≫ pullback.fst q q) (pullback.snd f b)
      (by simpa only [Category.assoc] using (pullback.condition (f := f) (g := b)))
    have h₂ := hgen' (pullback.fst f b ≫ pullback.snd q q) (pullback.snd f b)
      (by rw [Category.assoc, ← pullback.condition];
          simpa only [Category.assoc] using (pullback.condition (f := f) (g := b)))
    exact (by simpa only [Category.assoc] using h₁.trans h₂.symm)
  obtain ⟨s, hs⟩ := IsRegularEpi.exists_of_isKernelPair q
    (IsKernelPair.of_hasPullback q) sU hagree
  have hsbase : s ≫ C.hom = 𝟙 _ := by
    apply (cancel_epi q).mp
    rw [← Category.assoc, hs, hbase, Category.comp_id]
  have hsgen : b ≫ s = p.left := by
    apply (cancel_epi (pullback.snd q b)).mp
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hs]
    exact hgen
  let s' : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C := Over.homMk s hsbase
  have hsfac : Over.homMk (Spec.algebraMap R K) ≫ s' = p := by
    ext
    exact hsgen
  refine ⟨s', hsfac, ?_⟩
  intro t ht
  apply Over.OverMorphism.ext
  have : IsDominant b := isDominant_fractionFieldMap R K
  apply ext_of_isDominant_of_isSeparated C.hom (by simp) b
  exact (congrArg (fun a => a.left) ht).trans
    (congrArg (fun a => a.left) hsfac).symm

section ChosenSection

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Over (Spec (CommRingCat.of R))) [IsSeparated C.hom]
    {U : Scheme.{u}} [ConnectedSpace U] (q : U ⟶ Spec (CommRingCat.of R))
    [Etale q] [Surjective q] (I : Type u)
    (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U)))
    (p : Over.mk (Spec.algebraMap R K) ⟶ C)

/-- The unique integral section extending the given generic point. -/
def sectionOfConnectedEtaleTrivialization :
    Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C :=
  Classical.choose (existsUnique_section_of_connected_etale_trivialization R K C q I e p)

@[reassoc (attr := simp)]
theorem sectionOfConnectedEtaleTrivialization_generic :
    Over.homMk (Spec.algebraMap R K) ≫
      sectionOfConnectedEtaleTrivialization R K C q I e p = p :=
  (Classical.choose_spec
    (existsUnique_section_of_connected_etale_trivialization R K C q I e p)).1

end ChosenSection

end Langlands.AlgebraicGeometry
