import Langlands.Geometry.Analytic.AnalyticGaloisCover
import Langlands.Geometry.Analytic.FieldPointValueChange
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure

/-! # Freeness of analytic Galois deck actions -/

noncomputable section

universe u v uL z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits AffinoidAtlasPresentation Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

private def fieldPointValueChange {M : Type uL} [NormedField M] [NormedAlgebra K M]
    (i : L →ₐ[K] M) (hi : ∀ a, ‖i a‖ = ‖a‖) :
    fieldPointFunctor.{u, v, v} (K := K) L ⟶ fieldPointFunctor (K := K) M where
  app _ := TypeCat.ofHom fun q => q.mapValue i hi
  naturality _ _ _ := by
    ext q
    exact FieldPoint.ext' rfl (fun _ _ _ => rfl)

/-- Isometric extension of the value field commutes with localized analytic arrows. -/
def localizedFieldPointValueChange {M : Type uL} [NormedField M] [NormedAlgebra K M]
    (i : L →ₐ[K] M) (hi : ∀ a, ‖i a‖ = ‖a‖) :
    localizedFieldPointFunctor.{u, v, v} (K := K) L ⟶ localizedFieldPointFunctor (K := K) M :=
  Localization.Construction.natTransExtension
    (eqToHom (localizationFunctor_localizedFieldPointFunctor L) ≫ fieldPointValueChange i hi ≫
      eqToHom (localizationFunctor_localizedFieldPointFunctor M).symm)

namespace AnalyticGaloisCover

variable {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
  {Γ : Type z} [Group Γ] (c : AnalyticGaloisCover Γ p)

private theorem eq_one_of_graph_points_eq {γ : Γ} {x : localizedSpaceFunctor.obj Y}
    (h : localizedSpaceFunctor.map (c.graph γ) x = localizedSpaceFunctor.map (c.graph 1) x) :
    γ = 1 := by
  by_contra hγ
  exact (Set.disjoint_left.mp (c.disjoint_graphs hγ)) ⟨x, rfl⟩ ⟨x, h.symm⟩

/-- If postcomposition by a deck element fixes an arrow from a space with a
specified point, the deck element is the identity. -/
theorem eq_one_of_comp_deck_eq {T : LocalizedCategory.{u, v, v} (K := K)}
    (f : T ⟶ Y) (x : localizedSpaceFunctor.obj T) {γ : Γ}
    (h : f ≫ (c.deck γ).hom = f) : γ = 1 := by
  have hone : (c.deck 1).hom = 𝟙 Y := by rw [map_one]; rfl
  have hgraph : f ≫ c.graph γ = f ≫ c.graph 1 := by
    apply c.isPullback.hom_ext
    · rw [Category.assoc, c.graph_fst, Category.assoc, c.graph_fst]
    · rw [Category.assoc, c.graph_snd, h, Category.assoc, c.graph_snd, hone, Category.comp_id]
  apply c.eq_one_of_graph_points_eq (x := localizedSpaceFunctor.map f x)
  simpa only [Functor.map_comp, TopCat.comp_app] using
    congrArg (fun a : T ⟶ c.relation => localizedSpaceFunctor.map a x) hgraph

/-- The deck group acts freely on full points with values in any normed extension. -/
theorem eq_one_of_fieldPoint_fixed (γ : Γ) (q : (localizedFieldPointFunctor L).obj Y)
    (h : (localizedFieldPointFunctor L).map (c.deck γ).hom q = q) : γ = 1 := by
  let : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  let M := ValuedField.CompleteAlgebraicClosure L
  let : NormedAlgebra K M :=
    { toAlgebra := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
      norm_smul_le := fun a b => by
        change ‖algebraMap L M (algebraMap K L a) * b‖ ≤ ‖a‖ * ‖b‖
        rw [norm_mul, norm_algebraMap' M, norm_algebraMap' L] }
  let i : L →ₐ[K] M :=
    { toRingHom := algebraMap L M
      commutes' := fun _ => rfl }
  let η := localizedFieldPointValueChange.{u, v, uL} i (norm_algebraMap' M)
  let E := localizedFieldPointFunctor (K := K) M
  let r := η.app Y q
  have hr : E.map (c.deck γ).hom r = r := by
    have hn := congrArg (fun k => k q) (η.naturality (c.deck γ).hom)
    simpa only [types_comp_apply, h] using hn.symm
  have hone : (c.deck 1).hom = 𝟙 Y := by rw [map_one]; rfl
  have hgraph : E.map (c.graph γ) r = E.map (c.graph 1) r := by
    apply Types.ext_of_isPullback
      (localizedEtaleFieldPointPullback (L := M) c.fst c.snd p p c.etale_map c.isPullback)
    · change E.map c.fst (E.map (c.graph γ) r) = E.map c.fst (E.map (c.graph 1) r)
      rw [← E.map_comp_apply, ← E.map_comp_apply, c.graph_fst, c.graph_fst]
    · change E.map c.snd (E.map (c.graph γ) r) = E.map c.snd (E.map (c.graph 1) r)
      rw [← E.map_comp_apply, ← E.map_comp_apply, c.graph_snd, c.graph_snd, hone,
        E.map_id_apply]
      exact hr
  have hpoint := congrArg (fun t => ((localizedFieldPointProjection M).app c.relation t).down)
    hgraph
  change ((localizedFieldPointProjection M).app c.relation
      ((localizedFieldPointFunctor M).map (c.graph γ) r)).down =
    ((localizedFieldPointProjection M).app c.relation
      ((localizedFieldPointFunctor M).map (c.graph 1) r)).down at hpoint
  rw [localizedFieldPointProjection_down_naturality,
    localizedFieldPointProjection_down_naturality] at hpoint
  exact c.eq_one_of_graph_points_eq hpoint

end AnalyticGaloisCover

/-- Every analytic Galois covering acts freely on full field-valued points
and on arrows from nonempty analytic spaces. -/
def AnalyticGaloisCoverFreenessStatement (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X} {Γ : Type z} [Group Γ]
    (c : AnalyticGaloisCover Γ p) (γ : Γ),
    (∀ (L : Type uL) [NormedField L] [NormedAlgebra K L]
      (q : (localizedFieldPointFunctor L).obj Y),
      (localizedFieldPointFunctor L).map (c.deck γ).hom q = q → γ = 1) ∧
    (∀ {T : LocalizedCategory.{u, v, v} (K := K)} (f : T ⟶ Y)
      (_ : localizedSpaceFunctor.obj T), f ≫ (c.deck γ).hom = f → γ = 1)

theorem analyticGaloisCoverFreeness : AnalyticGaloisCoverFreenessStatement.{u, v, z, uL} K := by
  intro Y X p Γ _ c γ
  exact ⟨fun _ _ _ q => c.eq_one_of_fieldPoint_fixed γ q,
    fun f x hf => c.eq_one_of_comp_deck_eq f x hf⟩

end Langlands.Analytic.SaturatedAtlasPresentation
