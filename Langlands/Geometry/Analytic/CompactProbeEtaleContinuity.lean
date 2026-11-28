import Langlands.Geometry.Analytic.QuasiEtaleToEtaleReduction
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.EtalePointwiseLifting.LocalizedStability
import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology
import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement

/-! # Étale continuity for the compact-probe quasi-étale topology -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

universe u v

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The inclusion of the small étale site is continuous for the quasi-étale
topology tested by compact Hausdorff probes. -/
def CompactProbeEtaleContinuityStatement : Prop :=
  ∀ X : LocalizedCategory.{u, v, v} (K := K),
    (EtaleSite.toQuasiEtaleSite X).IsContinuous (etaleTopology X)
      (compactProbeQuasiEtaleTopology X)

variable {X : LocalizedCategory.{u, v, v} (K := K)}
  {U : EtaleSite X} {R : Presieve U}

private theorem exists_compact_chart_image_neighborhood
    (hcomp : QuasiEtaleCompStatement.{u, v} K) (hR : R ∈ etalePrecoverage X U)
    {C : QuasiEtaleSite X} (g : C ⟶ (EtaleSite.toQuasiEtaleSite X).obj U)
    (x : localizedSpaceFunctor.obj C.left) :
    ∃ σ : Set (Set (localizedSpaceFunctor.obj C.left)), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 x ∧
      ∀ W ∈ σ, ∃ (A : QuasiEtaleSite X) (a : A ⟶ C),
        IsCompactSpace A.left ∧
        (Sieve.generate R).functorPushforward (EtaleSite.toQuasiEtaleSite X) (a ≫ g) ∧
        W = range (localizedSpaceFunctor.map a.left) := by
  let F := EtaleSite.toQuasiEtaleSite X
  obtain ⟨V, f, hf, y, hy⟩ :=
    mem_etalePrecoverage_iff.mp hR (localizedSpaceFunctor.map g.left x)
  obtain ⟨_, hcancel⟩ := localizedEtaleStability (K := K)
  have he : etale f.left := by
    apply hcancel.of_postcomp f.left U.hom U.prop
    rw [MorphismProperty.Over.w f]
    exact V.prop
  obtain ⟨P, p, q, hP, hq⟩ := localizedEtalePullbackBaseChange f.left g.left he
  obtain ⟨z, _, hz⟩ := exists_point_of_isPullback_of_etale hP he y x hy
  obtain ⟨σ, hσ, hn, hW⟩ := QuasiEtaleToEtale.exists_chartImages q hq z
  refine ⟨σ, hσ, hz ▸ hn, fun W hW' => ?_⟩
  obtain ⟨i, rfl⟩ := hW W hW'
  let D := (presentationOf P).chartDomain i
  let j := domainι P D
  let A : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ ((j ≫ q) ≫ C.hom)
    (hcomp.comp_mem _ _ (quasiEtale_domainι_comp_of_etale D q hq) C.prop)
  let a : A ⟶ C := MorphismProperty.Over.homMk (j ≫ q)
  let b : A ⟶ F.obj V := MorphismProperty.Over.homMk (j ≫ p) (by
    change (j ≫ p) ≫ V.hom = (j ≫ q) ≫ C.hom
    have hfU : f.left ≫ U.hom = V.hom := MorphismProperty.Over.w f
    have hgU : g.left ≫ U.hom = C.hom := MorphismProperty.Over.w g
    calc
      _ = j ≫ (p ≫ f.left) ≫ U.hom := by simp only [Category.assoc, hfU]
      _ = j ≫ (q ≫ g.left) ≫ U.hom := by rw [hP.w]
      _ = _ := by simp only [Category.assoc, hgU])
  have hab : a ≫ g = b ≫ F.map f := by
    apply MorphismProperty.Over.Hom.ext
    change (j ≫ q) ≫ g.left = (j ≫ p) ≫ f.left
    simpa only [Category.assoc] using congrArg (j ≫ ·) hP.w.symm
  have hf' : (Sieve.generate R).functorPushforward F (F.map f) := by
    rw [← Sieve.generate_map_eq_functorPushforward]
    exact Sieve.le_generate _ _ _ (Presieve.map.of hf)
  refine ⟨A, a, isCompactSpace_chartDomainObj _ i, hab ▸ ?_, ?_⟩
  · exact (Sieve.generate R |>.functorPushforward F).downward_closed hf' b
  · change localizedSpaceFunctor.map q '' D.carrier =
      range (localizedSpaceFunctor.map (j ≫ q))
    rw [Functor.map_comp]
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, by rw [TopCat.comp_app, domainι_apply]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, t.property, by rw [TopCat.comp_app, domainι_apply]⟩

/-- Pull back an étale covering family to each compact probe, then use
étale openness to extract finitely many compact chart images. -/
theorem compactProbeEtaleContinuity_of_comp
    (hcomp : QuasiEtaleCompStatement.{u, v} K) :
    CompactProbeEtaleContinuityStatement.{u, v} (K := K) := by
  intro X
  let F := EtaleSite.toQuasiEtaleSite X
  let : RepresentablyFlat F :=
    QuasiEtaleToEtale.representablyFlat_toQuasiEtaleSite
      localizedEtalePullbackBaseChange localizedEtaleStability X
  apply QuasiEtaleToEtale.isContinuous_of_flat F (etalePrecoverage X)
  intro U R hR C g hC
  classical
  let : CompactSpace (localizedSpaceFunctor.obj C.left) := hC.1
  choose σ hσ hn hchart using exists_compact_chart_image_neighborhood hcomp hR g
  obtain ⟨s, _, hcover⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => ⋃₀ σ x) (fun x _ => hn x)
  let T := ⋃ x ∈ s, σ x
  have hT : T.Finite := s.finite_toSet.biUnion (fun x _ => hσ x)
  let : Fintype T := hT.fintype
  let e := Fintype.equivFin T
  have hsource (W : T) :=
    let ⟨x, _, hx⟩ := mem_iUnion₂.mp W.property
    hchart x W.val hx
  choose A a hA ha haim using hsource
  refine ⟨_, fun i => A (e.symm i), fun i => a (e.symm i),
    fun i => hA (e.symm i), fun i => ha (e.symm i), ?_⟩
  intro x
  obtain ⟨y, hy, W, hW, hx⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  let w : T := ⟨W, mem_iUnion₂.mpr ⟨y, hy, hW⟩⟩
  refine ⟨e w, ?_⟩
  change x ∈ range (localizedSpaceFunctor.map (a (e.symm (e w))).left)
  rw [e.symm_apply_apply, ← haim w]
  exact hx

end Langlands.Analytic.SaturatedAtlasPresentation
