import Langlands.Geometry.Analytic.EquivariantEtalePretopology
import Langlands.Geometry.Analytic.InducedQuasiEtaleProof
import Langlands.Geometry.Analytic.InducedSiteEquivalenceProof
import Langlands.Geometry.Analytic.InducedSpaceContinuityProof
import Langlands.Geometry.Analytic.LocalizedSigmaComponents
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Induction on equivariant étale sites -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hH : IsOpen (H : Set G)) (X : GSpace.{u, max z v, max z v} K H)

/-- Induction of an étale object and its over-morphisms along an open subgroup. -/
def etaleSiteInduction :
    EquivariantEtaleSite X ⥤ EquivariantEtaleSite ((gSpaceInduction hH (continuityStatement.{u, v, z})).obj X) :=
  MorphismProperty.Comma.lift
    (MorphismProperty.Over.forget _ _ X ⋙ Over.post (gSpaceInduction hH (continuityStatement.{u, v, z})))
    (fun U => etale_inductionFunctor_map H ((ObjectProperty.ι _).map U.hom) U.prop)
    (fun _ => trivial) (fun _ => trivial)

private theorem etale_of_etale_induction {U V : GSpace.{u, max z v, max z v} K H} (f : U ⟶ V)
    (hf : GSpace.etale ((gSpaceInduction hH (continuityStatement.{u, v, z})).map f)) : GSpace.etale f := by
  let c := baseCoset H
  have hU : etale (copy H U.obj c) :=
    etale_localizedSigmaCofan_inj (fun _ : G ⧸ H => U.obj.V) c
  have hV : etale (copy H V.obj c) :=
    etale_localizedSigmaCofan_inj (fun _ : G ⧸ H => V.obj.V) c
  have hs : copy H U.obj c ≫ GSpace.forget.map ((gSpaceInduction hH (continuityStatement.{u, v, z})).map f) =
      GSpace.forget.map f ≫ copy H V.obj c :=
    copy_inductionFunctor_map H ((ObjectProperty.ι _).map f) c
  let := (localizedEtaleStability (K := K)).2
  exact (etale (K := K)).of_postcomp _ _ hV (hs ▸ etale_comp hU hf)

instance etaleSiteInduction_isEquivalence : (etaleSiteInduction hH X).IsEquivalence := by
  let Q := quasiEtaleSiteInduction hH (continuityStatement.{u, v, z})
    (inductionFunctor_map_quasiEtale_etale.{u, v, z}) X
  let I := gSpaceInduction (K := K) hH (continuityStatement.{u, v, z})
  let : Q.IsEquivalence := (quasiEtaleSiteEquivalenceStatement.{u, v, z}
    K G H hH continuityStatement inductionFunctor_map_quasiEtale_etale X).1
  let F := etaleSiteInduction hH X
  let J := EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X
  let J' := EquivariantQuasiEtaleSite.ofEquivariantEtaleSite (I.obj X)
  have h : F ⋙ J' = J ⋙ Q := rfl
  have : (F ⋙ J').Faithful := h ▸ inferInstanceAs (J ⋙ Q).Faithful
  have : (F ⋙ J').Full := h ▸ inferInstanceAs (J ⋙ Q).Full
  refine ⟨⟨fun {_ _} f g he => (F ⋙ J').map_injective (congrArg J'.map he)⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro U V f
    obtain ⟨g, hg⟩ := (F ⋙ J').map_surjective (J'.map f)
    exact ⟨g, J'.map_injective hg⟩
  · intro V
    obtain ⟨U, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q (J'.obj V)
    let A := MorphismProperty.Over.forget (GSpace.quasiEtale (K := K) (G := G)) ⊤ (I.obj X) ⋙
      Over.forget (I.obj X)
    have hU' : GSpace.etale (I.map U.hom) := by
      change etale (GSpace.forget.map (Q.obj U).hom)
      rw [← MorphismProperty.Over.w e.hom, _root_.CategoryTheory.Functor.map_comp]
      exact etale_comp (show etale ((A ⋙ GSpace.forget).map e.hom) from etale_of_isIso _) V.prop
    let U' : EquivariantEtaleSite X :=
      MorphismProperty.Over.mk ⊤ U.hom (etale_of_etale_induction hH U.hom hU')
    have he : (A.mapIso e).hom ≫ V.hom = (F.obj U').hom := MorphismProperty.Over.w e.hom
    exact ⟨U', ⟨MorphismProperty.Over.isoMk (A.mapIso e) he⟩⟩

/-- A family of étale over-morphisms is jointly surjective precisely when its
induction is jointly surjective on every coset copy. -/
theorem map_etaleSiteInduction_mem_iff {U : EquivariantEtaleSite X} (R : Presieve U) :
    R.map (etaleSiteInduction hH X) ∈ equivariantEtalePrecoverage ((gSpaceInduction hH (continuityStatement.{u, v, z})).obj X)
        ((etaleSiteInduction hH X).obj U) ↔
      R ∈ equivariantEtalePrecoverage X U := by
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, ofArrows_mem_equivariantEtalePrecoverage_iff,
    ofArrows_mem_equivariantEtalePrecoverage_iff]
  let Y := localizedSpaceFunctor.obj (GSpace.forget.obj U.left)
  constructor
  · intro h x
    obtain ⟨i, ⟨c, y⟩, he⟩ := h (⟨baseCoset H, x⟩ : (_ : G ⧸ H) × Y)
    have hpt := localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply
      hH continuityStatement (f i).left c y
    exact ⟨i, y, eq_of_heq (Sigma.mk.inj_iff.mp (hpt.symm.trans he)).2⟩
  · rintro h ⟨c, x⟩
    obtain ⟨i, y, hy⟩ := h x
    refine ⟨i, ⟨c, y⟩, ?_⟩
    exact (localizedSpaceFunctor_map_forget_map_gSpaceInduction_map_apply
      hH continuityStatement (f i).left c y).trans (congrArg (Sigma.mk c) hy)

private theorem mem_equivariantEtaleTopology_iff_arrows
    {G₀ : Type z} [Group G₀] [TopologicalSpace G₀]
    {B : GSpace.{u, max z v, max z v} K G₀} {U : EquivariantEtaleSite B} (S : Sieve U) :
    S ∈ equivariantEtaleTopology B U ↔ S.arrows ∈ equivariantEtalePrecoverage B U := by
  rw [equivariantEtaleTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  constructor
  · rintro ⟨R, hR, hRS⟩
    rw [mem_equivariantEtalePrecoverage_iff] at hR ⊢
    intro x
    obtain ⟨V, f, hf, hx⟩ := hR x
    exact ⟨V, f, hRS _ _ hf, hx⟩
  · exact fun h => ⟨S.arrows, h, le_rfl⟩

/-- Induction transports the generated equivariant étale topologies. -/
instance etaleSiteInduction_isDenseSubsite :
    (etaleSiteInduction hH X).IsDenseSubsite (equivariantEtaleTopology X)
      (equivariantEtaleTopology ((gSpaceInduction hH (continuityStatement.{u, v, z})).obj X)) where
  functorPushforward_mem_iff {U S} := by
    let F := etaleSiteInduction hH X
    let points := EquivariantEtaleSite.points ((gSpaceInduction hH (continuityStatement.{u, v, z})).obj X)
    rw [mem_equivariantEtaleTopology_iff_arrows, mem_equivariantEtaleTopology_iff_arrows,
      ← map_etaleSiteInduction_mem_iff hH X S.arrows]
    simp only [mem_equivariantEtalePrecoverage_iff]
    constructor
    · intro h x
      obtain ⟨V, a, ⟨W, f, k, hf, rfl⟩, y, hy⟩ := h x
      refine ⟨F.obj W, F.map f, Presieve.map_map (F := F) hf, points.map k y, ?_⟩
      exact (_root_.CategoryTheory.Functor.map_comp_apply points k (F.map f) y).symm.trans hy
    · intro h x
      obtain ⟨V, f, hf, hx⟩ := h x
      exact ⟨V, f, Presieve.map_le_functorPushforward F S.arrows _ _ hf, hx⟩

/-- The equivalence of equivariant étale over-categories induced by the open subgroup. -/
def etaleSiteInductionEquivalence :
    EquivariantEtaleSite X ≌ EquivariantEtaleSite ((gSpaceInduction hH (continuityStatement.{u, v, z})).obj X) :=
  (etaleSiteInduction hH X).asEquivalence

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
