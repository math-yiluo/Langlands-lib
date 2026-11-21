import Langlands.Geometry.Analytic.AnalyticGaloisCover
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackExistence
import Langlands.Geometry.Analytic.OpenImmersionFieldPointLifting
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure

/-! # Geometric fibres detect analytic Galois coverings -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set Topology
open AffinoidAtlasPresentation BanachSpectrum PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every ordinary analytic point underlies a full point over a complete
algebraically closed value extension in the base-field universe. -/
theorem exists_algebraicallyClosed_fieldPoint
    (X : LocalizedCategory.{u, v, v} (K := K)) (x : localizedSpaceFunctor.obj X) :
    ∃ (L : Type u) (_ : NormedField L) (_ : NormedAlgebra K L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : IsAlgClosed L) (q : (localizedFieldPointFunctor L).obj X),
      ((localizedFieldPointProjection L).app X q).down = x := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨i, t, ht⟩ := A.presentation.atlas.exists_mem_range_chart x
  let H := CompletedResidueField K t
  let L := ValuedField.CompleteAlgebraicClosure H
  let : NormedAlgebra K L :=
    { toAlgebra := ((algebraMap H L).comp (algebraMap K H)).toAlgebra
      norm_smul_le := fun a b => by
        change ‖algebraMap H L (algebraMap K H a) * b‖ ≤ ‖a‖ * ‖b‖
        rw [norm_mul, norm_algebraMap' L, norm_algebraMap' H] }
  let j : H →ₐ[K] L := ⟨algebraMap H L, fun _ => rfl⟩
  let f := j.comp (completedResidueMap K t).toAlgHom
  have hf (a : A.presentation.atlas.algebra i) : ‖f a‖ = t a :=
    (norm_algebraMap' L _).trans (norm_completedResidueMap K t a)
  obtain ⟨q, ⟨hq, -⟩, -⟩ := FieldPoint.existsUnique_of_chartCharacter
    domainCompletedResidueSurjectivity x i f ⟨t, ht, hf⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q, hq⟩

namespace AnalyticGaloisCover

variable {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} {Γ : Type z} [Group Γ]

/-- A surjective analytic étale arrow whose deck action is simply transitive
on full geometric fibres has the analytic deck-graph partition. -/
def of_geometricFibres (hp : etale p) (hsurj : Function.Surjective (localizedSpaceFunctor.map p))
    (deck : Γ →* Aut Y) (hdeck : ∀ γ, (deck γ).hom ≫ p = p)
    (hact : ∀ (L : Type u) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
      [CompleteSpace L] [IsAlgClosed L] (a b : (localizedFieldPointFunctor L).obj Y),
      (localizedFieldPointFunctor L).map p a = (localizedFieldPointFunctor L).map p b →
      ∃! γ : Γ, (localizedFieldPointFunctor L).map (deck γ).hom a = b) : AnalyticGaloisCover Γ p := by
  let Q := localizedEtalePullback p p hp
  let s := Q.1.fst
  let t := Q.1.snd
  let h := IsPullback.of_isLimit Q.2
  let graph (γ : Γ) := analyticDeckGraph h (deck γ) (hdeck γ)
  have hs (γ : Γ) : graph γ ≫ s = 𝟙 Y := h.lift_fst _ _ _
  have ht (γ : Γ) : graph γ ≫ t = (deck γ).hom := h.lift_snd _ _ _
  have hsEtale : etale s := by
    have hex : LocalizedEtalePullbackStatement.{u, v} K :=
      localizedEtalePullback_of_targetLocality_and_finitePieces
        (AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent finiteAffinoidAlgebraDescent)
        AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces
    obtain ⟨_, _, _, h', hq⟩ := hex p p hp
    exact etale_snd_of_isPullback h' h.flip hq
  have hopen (γ : Γ) : openImmersion (graph γ) :=
    localizedEtaleSectionsOpen hsEtale (hs γ)
  refine ⟨hp, hsurj, deck, hdeck, Q.1.pt, s, t, h, ?_, ?_⟩
  · intro x
    obtain ⟨L, _, _, _, _, _, q, hq⟩ := exists_algebraicallyClosed_fieldPoint Q.1.pt x
    let Φ := localizedFieldPointFunctor (K := K) L
    let a := Φ.map s q
    let b := Φ.map t q
    have hab : Φ.map p a = Φ.map p b := by
      change Φ.map p (Φ.map s q) = Φ.map p (Φ.map t q)
      rw [← Φ.map_comp_apply, ← Φ.map_comp_apply, h.w]
    obtain ⟨γ, hγ, _⟩ := hact L a b hab
    have hgraph : Φ.map (graph γ) a = q := by
      apply Types.ext_of_isPullback (localizedEtaleFieldPointPullback (L := L) s t p p hp h)
      · change Φ.map s (Φ.map (graph γ) a) = a
        rw [← Φ.map_comp_apply, hs, Φ.map_id_apply]
      · change Φ.map t (Φ.map (graph γ) a) = b
        rwa [← Φ.map_comp_apply, ht]
    refine ⟨γ, ((localizedFieldPointProjection L).app Y a).down, ?_⟩
    change localizedSpaceFunctor.map (graph γ) (((localizedFieldPointProjection L).app Y a).down) = x
    rw [← localizedFieldPointProjection_map_down (graph γ)]
    have hh := congrArg (fun r => ((localizedFieldPointProjection L).app Q.1.pt r).down) hgraph
    exact hh.trans hq
  · intro γ δ hγδ
    apply Set.disjoint_left.mpr
    intro x hxγ hxδ
    obtain ⟨L, _, _, _, _, _, q, hq⟩ := exists_algebraicallyClosed_fieldPoint Q.1.pt x
    let Φ := localizedFieldPointFunctor (K := K) L
    have liftGraph (α : Γ) (hx : x ∈ range (localizedSpaceFunctor.map (graph α))) :
        ∃ a : Φ.obj Y, Φ.map (graph α) a = q :=
      openImmersionFieldPointLifting (L := L) (graph α) (hopen α) q (hq.symm ▸ hx)
    obtain ⟨a, ha⟩ := liftGraph γ hxγ
    obtain ⟨b, hb⟩ := liftGraph δ hxδ
    have hfst (α : Γ) (r : Φ.obj Y) (hr : Φ.map (graph α) r = q) : r = Φ.map s q := by
      rw [← hr, ← Φ.map_comp_apply, hs, Φ.map_id_apply]
    have heq : a = b := (hfst γ a ha).trans (hfst δ b hb).symm
    subst b
    have hsnd (α : Γ) (hr : Φ.map (graph α) a = q) :
        Φ.map (deck α).hom a = Φ.map t q := by
      rw [← hr, ← Φ.map_comp_apply, ht]
    have hsame : Φ.map p a = Φ.map p (Φ.map t q) := by
      rw [← hsnd γ ha, ← Φ.map_comp_apply, hdeck]
    obtain ⟨α, _, hα⟩ := hact L a (Φ.map t q) hsame
    exact hγδ ((hα γ (hsnd γ ha)).trans (hα δ (hsnd δ hb)).symm)

end AnalyticGaloisCover
end Langlands.Analytic.SaturatedAtlasPresentation
