import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingUniquenessStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusBaseChangeProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionEvaluationSections
import Langlands.AlgebraicGeometry.LinearSystem.BundleComparison
import Langlands.AlgebraicGeometry.LinearSystem.CoordinateIdentity
import Langlands.AlgebraicGeometry.LinearSystem.ScalarTwist
import Langlands.AlgebraicGeometry.Modules.OpenCartesianDirectImageBaseChange
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas

/-! # Proof of uniqueness of frame-normalized cubic embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections Langlands.SchemeModule

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option backward.isDefEq.respectTransparency false

variable {P : Prerequisites.{u}} {S T : Scheme.{u}} {g d n m : ℕ}
variable {a : Datum P S g d n} {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}

private lemma frameEvaluation_isIso (h : a.frameLocus ρ = ⊤) (k : Fin (m + 2)) :
    IsIso (a.frameEvaluation ρ k) := by
  rw [isIso_iff_forall_mem_isoLocus]
  intro x
  have hx : x ∈ a.frameLocus ρ := by rw [h]; trivial
  obtain ⟨W, hxW, hW⟩ := (mem_sSup_isIso_restrict_iff (a.frameEvaluation ρ) x).mp hx
  exact hW k x hxW

private lemma frameEvaluation_pullback_isIso (b : T ⟶ S) [IsOpenImmersion b]
    (k : Fin (m + 2)) [IsIso (a.frameEvaluation ρ k)] :
    IsIso ((a.pullback b).frameEvaluation ρ k) := by
  have : IsIso (a.rigidificationBaseChangeMap b) := by
    unfold Datum.rigidificationBaseChangeMap
    have := isIso_pushforwardBaseChange_of_isOpenImmersion b a.abelian.X.hom
      (a.pullback b).abelian.X.hom (pullback.fst a.abelian.X.hom b)
      (IsPullback.of_hasPullback a.abelian.X.hom b) a.cubicBundle.obj
    infer_instance
  have : IsIso (a.rigidificationBaseChangeMap b ≫ (a.pullback b).frameEvaluation ρ k) := by
    rw [a.rigidificationBaseChangeMap_comp_frameEvaluation]
    infer_instance
  exact IsIso.of_isIso_comp_left (a.rigidificationBaseChangeMap b) _

private lemma cubicSections_ext (k : Fin (m + 2)) [IsIso (a.frameEvaluation ρ k)]
    {s t : GlobalSections a.cubicBundle.obj}
    (h : ∀ j : Fin (m + 2), j ≠ k →
      pullbackSection (a.torsionPoint (ρ j)) a.cubicBundle.obj s =
        pullbackSection (a.torsionPoint (ρ j)) a.cubicBundle.obj t) : s = t := by
  apply sectionHom_injective a.rigidificationModule
  apply (cancel_mono (a.frameEvaluation ρ k)).mp
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, Datum.frameEvaluation, Pi.lift_comp_π]
  rw [← sectionHom_naturality, ← sectionHom_naturality,
    Datum.torsionEvaluation_app_top, Datum.torsionEvaluation_app_top, h j.1 j.2]

private lemma frameEmbedding_coordinates
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    (h : a.IsFrameEmbedding ρ ψ)
    (e : (LineBundle.pullback ψ).obj (RelativeProjectiveSpace.twistOne S m) ≅ a.cubicBundle) :
    ∃ (s : Fin (m + 1) → GlobalSections a.cubicBundle.obj)
      (hs : ∀ x, ∃ i, x ∈ nonvanishingLocus a.cubicBundle.obj (s i)),
      relativeLinearSystemMap a.abelian.X.hom hs = ψ ∧
        (∀ j i : Fin (m + 1), i ≠ j →
          VanishesAlong a.cubicBundle (a.torsionPoint (ρ j.castSucc)) (s i)) ∧
        (∀ i k : Fin (m + 1),
          pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1)))) a.cubicBundle.obj (s i) =
            pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1)))) a.cubicBundle.obj (s k)) := by
  let L := RelativeProjectiveSpace.twistOne S m
  let coords := RelativeProjectiveSpace.twistOneCoordinate S m
  let pulled : Fin (m + 1) → GlobalSections ((LineBundle.pullback ψ).obj L).obj :=
    fun i => pullbackSection ψ L.obj (coords i)
  let e₀ : ((LineBundle.pullback ψ).obj L).obj ≅ a.cubicBundle.obj :=
    (LineBundle.forget a.abelian.X.left).mapIso e
  have hp := pullbackSections_generate ψ (relativeProjectiveCoordinates_generate S m)
  refine ⟨mapIsoSections e₀ pulled, mapIsoSections_generate e₀ hp, ?_, ?_, ?_⟩
  · rw [relativeLinearSystemMap_mapIso]
    have he := relativeLinearSystemMap_pullback (RelativeProjectiveSpace.toBase S m)
      a.abelian.X.hom ψ (𝟙 S) (by simpa using h.toBase)
      (relativeProjectiveCoordinates_generate S m)
    simpa only [RelativeProjectiveSpace.map_id, Category.comp_id,
      relativeLinearSystemMap_relativeProjectiveCoordinates] using he
  · intro j i hij
    exact (vanishesAlong_mapIso_iff e₀ _ (pulled i)).mpr
      ((vanishesAlong_pullback_iff _ ψ L (coords i)).mpr (h.basis j i hij))
  · intro i k
    let p := a.torsionPoint (ρ (Fin.last (m + 1)))
    have heq : pullbackSection p ((LineBundle.pullback ψ).obj L).obj (pulled i) =
        pullbackSection p ((LineBundle.pullback ψ).obj L).obj (pulled k) :=
      (pullbackSection_pullback_eq_iff ψ p (coords i) (coords k)).mpr (h.unit i k)
    change pullbackSection p a.cubicBundle.obj (e₀.hom.app ⊤ (pulled i)) =
      pullbackSection p a.cubicBundle.obj (e₀.hom.app ⊤ (pulled k))
    rw [pullbackSection_naturality, pullbackSection_naturality, heq]

private lemma lastCoordinate_generates {X : Scheme.{u}} {L : LineBundle X}
    (p : S ⟶ X) {s : Fin (m + 1) → GlobalSections L.obj}
    (hs : ∀ x, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (hunit : ∀ i, pullbackSection p L.obj (s i) = pullbackSection p L.obj (s 0)) :
    ∀ x, p x ∈ trivializationOpen L.obj (s 0) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs (p x)
  have h := (mem_pullback_trivializationOpen_iff p (s i) x).mpr hi
  rw [hunit i] at h
  exact (mem_pullback_trivializationOpen_iff p (s 0) x).mp h

private theorem eq_of_cubic_coordinate_bundles
    {ψ ψ' : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    (hframe : ∀ k, IsIso (a.frameEvaluation ρ k))
    (h : a.IsFrameEmbedding ρ ψ) (h' : a.IsFrameEmbedding ρ ψ')
    (e : (LineBundle.pullback ψ).obj (RelativeProjectiveSpace.twistOne S m) ≅ a.cubicBundle)
    (e' : (LineBundle.pullback ψ').obj (RelativeProjectiveSpace.twistOne S m) ≅ a.cubicBundle) :
    ψ = ψ' := by
  obtain ⟨s, hs, hψ, hb, hu⟩ := frameEmbedding_coordinates h e
  obtain ⟨s', hs', hψ', hb', hu'⟩ := frameEmbedding_coordinates h' e'
  let p := a.torsionPoint (ρ (Fin.last (m + 1)))
  have hg := lastCoordinate_generates p hs (fun i => hu i 0)
  have hg' := lastCoordinate_generates p hs' (fun i => hu' i 0)
  obtain ⟨c, hc⟩ := isUnit_sectionRatio hg hg'
  have hc' : (c : Γ(S, ⊤)) • pullbackSection p a.cubicBundle.obj (s 0) =
      pullbackSection p a.cubicBundle.obj (s' 0) := by
    rw [hc, sectionRatio_smul hg]
  let ec := Langlands.Scheme.Modules.unitAut a.cubicBundle.obj
    (Units.map a.abelian.X.hom.appTop.hom.toMonoidHom c)
  have heq : mapIsoSections ec.asIso s = s' := by
    funext i
    change ec.asIso.hom.app ⊤ (s i) = s' i
    rw [Langlands.Scheme.Modules.unitAut_hom_app_top]
    change a.abelian.X.hom.appTop (c : Γ(S, ⊤)) • s i = s' i
    have := hframe i.castSucc
    apply cubicSections_ext (a := a) (ρ := ρ) i.castSucc
    intro j hj
    rw [LinearSystem.pullbackSection_smul]
    have hcj : (a.torsionPoint (ρ j)).appTop (a.abelian.X.hom.appTop (c : Γ(S, ⊤))) =
        (c : Γ(S, ⊤)) := by
      change (a.torsionPoint (ρ j) ≫ a.abelian.X.hom).appTop (c : Γ(S, ⊤)) = _
      simp
    rw [hcj]
    refine Fin.lastCases ?_ (fun k hk => ?_) j hj
    · intro _
      rw [hu i 0, hu' i 0]
      exact hc'
    · have hik : i ≠ k := fun he => hk (congrArg Fin.castSucc he.symm)
      rw [show pullbackSection _ _ (s i) = 0 from hb k i hik,
        show pullbackSection _ _ (s' i) = 0 from hb' k i hik, smul_zero]
  calc
    ψ = relativeLinearSystemMap a.abelian.X.hom hs := hψ.symm
    _ = relativeLinearSystemMap a.abelian.X.hom (mapIsoSections_generate ec.asIso hs) :=
      (relativeLinearSystemMap_mapIso _ ec.asIso hs).symm
    _ = ψ' := by
      subst s'
      exact hψ'

private def pullback_cubic_iso (b : T ⟶ S)
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
    (h : a.IsFrameEmbedding ρ ψ) {N : LineBundle S}
    (e : (LineBundle.pullback ψ).obj (RelativeProjectiveSpace.twistOne S m) ≅
      LineBundle.tensor P.preservation a.cubicBundle ((LineBundle.pullback a.abelian.X.hom).obj N))
    (eN : (LineBundle.pullback b).obj N ≅ LineBundle.trivial T) :
    (LineBundle.pullback (a.pullbackEmbedding b ψ)).obj (RelativeProjectiveSpace.twistOne T m) ≅
      (a.pullback b).cubicBundle := by
  let q := pullback.fst a.abelian.X.hom b
  let f := (a.pullback b).abelian.X.hom
  let ψT := a.pullbackEmbedding b ψ
  let L := RelativeProjectiveSpace.twistOne S m
  have w : ψT ≫ RelativeProjectiveSpace.map m b = q ≫ ψ := Datum.pullbackEmbedding_map h.toBase
  have eN' : (LineBundle.pullback q).obj ((LineBundle.pullback a.abelian.X.hom).obj N) ≅
      LineBundle.trivial (a.pullback b).abelian.X.left :=
    LineBundle.pullbackCompEqIso q a.abelian.X.hom pullback.condition N ≪≫
      ((LineBundle.pullbackComp f b).app N).symm ≪≫
      (LineBundle.pullback f).mapIso eN ≪≫ LineBundle.pullbackTrivialIso f
  exact (LineBundle.pullback ψT).mapIso (RelativeProjectiveSpace.twistOnePullbackIso m b).symm ≪≫
    LineBundle.pullbackCompEqIso ψT (RelativeProjectiveSpace.map m b) w L ≪≫
    ((LineBundle.pullbackComp q ψ).app L).symm ≪≫ (LineBundle.pullback q).mapIso e ≪≫
    LineBundle.pullbackTensorObjIso P.preservation q _ _ ≪≫
    LineBundle.tensorIso P.preservation (a.cubicBundlePullbackIso b).symm eN' ≪≫
    LineBundle.tensorTrivialIso P.preservation (a.pullback b).cubicBundle

/-- On the entire projective frame locus, two frame-normalized cubic embeddings agree. -/
theorem frameEmbeddingUniqueness : FrameEmbeddingUniquenessStatement.{u} := by
  intro P S g d n m a ρ ψ ψ' hframe h h'
  obtain ⟨N, ⟨e⟩⟩ := h.cubic
  obtain ⟨N', ⟨e'⟩⟩ := h'.cubic
  apply Scheme.hom_ext_of_forall
  intro x
  let y := a.abelian.X.hom x
  let U := N.trivializingOpen y ⊓ N'.trivializingOpen y
  have eN : (LineBundle.pullback U.ι).obj N ≅ LineBundle.trivial U.toScheme :=
    ObjectProperty.isoMk _ (pullbackTrivializationOfLE inf_le_left N.obj (N.localTrivialization y))
  have eN' : (LineBundle.pullback U.ι).obj N' ≅ LineBundle.trivial U.toScheme :=
    ObjectProperty.isoMk _ (pullbackTrivializationOfLE inf_le_right N'.obj (N'.localTrivialization y))
  have hU : ∀ k, IsIso ((a.pullback U.ι).frameEvaluation ρ k) := fun k => by
    have := frameEvaluation_isIso hframe k
    exact frameEvaluation_pullback_isIso (a := a) (ρ := ρ) U.ι k
  have heq := eq_of_cubic_coordinate_bundles hU (h.pullback (f := U.ι)) (h'.pullback (f := U.ι))
    (pullback_cubic_iso U.ι h e eN) (pullback_cubic_iso U.ι h' e' eN')
  have hp : pullback.fst a.abelian.X.hom U.ι ≫ ψ = pullback.fst a.abelian.X.hom U.ι ≫ ψ' := by
    rw [← Datum.pullbackEmbedding_map (f := U.ι) h.toBase,
      ← Datum.pullbackEmbedding_map (f := U.ι) h'.toBase, heq]
  refine ⟨a.abelian.X.hom ⁻¹ᵁ U, ⟨N.mem_trivializingOpen y, N'.mem_trivializingOpen y⟩, ?_⟩
  rw [← AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst, Category.assoc, Category.assoc, hp]

end Langlands.AbelianScheme.PolarizedFiniteLevel
