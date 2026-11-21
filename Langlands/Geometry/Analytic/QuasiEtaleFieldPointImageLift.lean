import Langlands.Geometry.Analytic.QuasiEtaleGeometricPointGeometry
import Langlands.Geometry.Analytic.FullRecognitionFieldPointLifts
import Langlands.Geometry.Analytic.OpenImmersionFieldPointLifting

/-! # Field-point image lifting along quasi-étale morphisms -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Topology

section Pointed

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [NormedAlgebra K L]

/-- Pointed lifting of `L`-valued points along a localized morphism: an `L`-valued point of the
target lifts, at every prescribed ordinary source point above its underlying point, to an
`L`-valued point of the source with exactly that image. -/
def PointedFieldPointLift {X Y : LocalizedCategory.{u, v, v} (K := K)} (f : X ⟶ Y) : Prop :=
  ∀ (p : (localizedFieldPointFunctor L).obj Y) (x : localizedSpaceFunctor.obj X),
    localizedSpaceFunctor.map f x = ((localizedFieldPointProjection L).app Y p).down →
    ∃ q : (localizedFieldPointFunctor L).obj X,
      ((localizedFieldPointProjection L).app X q).down = x ∧
        (localizedFieldPointFunctor L).map f q = p

variable {L}

/-- Pointed lifts compose. -/
theorem PointedFieldPointLift.comp {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : PointedFieldPointLift L f)
    (hg : PointedFieldPointLift L g) : PointedFieldPointLift L (f ≫ g) := by
  intro p x hx
  have hx' : localizedSpaceFunctor.map g (localizedSpaceFunctor.map f x) =
      ((localizedFieldPointProjection L).app Z p).down := by
    rw [← hx, Functor.map_comp, TopCat.comp_app]
  obtain ⟨r, hr, hrp⟩ := hg p _ hx'
  obtain ⟨q, hq, hqr⟩ := hf r x hr.symm
  exact ⟨q, hq, by rw [Functor.map_comp_apply, hqr, hrp]⟩

/-- Isomorphisms have pointed lifts. -/
theorem pointedFieldPointLift_of_isIso {X Y : LocalizedCategory.{u, v, v} (K := K)}
    (f : X ⟶ Y) [IsIso f] : PointedFieldPointLift L f := by
  intro p x hx
  refine ⟨(localizedFieldPointFunctor L).map (inv f) p, ?_, ?_⟩
  · rw [localizedFieldPointProjection_map_down, ← hx, ← TopCat.comp_app, ← Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, TopCat.id_app]
  · rw [← Functor.map_comp_apply, IsIso.inv_hom_id, Functor.map_id_apply]

/-- Pointed lifting is invariant under isomorphisms in the arrow category. -/
theorem PointedFieldPointLift.of_arrow_iso {A B X Y : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ B} {g : X ⟶ Y} (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : PointedFieldPointLift L f) : PointedFieldPointLift L g := by
  have hg : g = e.inv.left ≫ f ≫ e.hom.right := by
    have h₁ : e.inv.left ≫ f = g ≫ e.inv.right := e.inv.w
    have h₂ : e.inv.right ≫ e.hom.right = 𝟙 Y := Arrow.inv_hom_id_right e
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.comp_id]
  rw [hg]
  exact (pointedFieldPointLift_of_isIso e.inv.left).comp
    (hf.comp (pointedFieldPointLift_of_isIso e.hom.right))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism of an analytic domain has pointed lifts: a full field point whose
ordinary point lies in the domain restricts to the domain. -/
theorem pointedFieldPointLift_localizedDomainInclusion
    (S : SaturatedAtlasPresentation.{u, v, v} K) (D : S.AnalyticDomain) :
    PointedFieldPointLift L (S.localizedDomainInclusion D) := by
  intro p x hx
  rw [localizedSpaceFunctor_map_localizedDomainInclusion] at hx
  have hx'' : (x : D.carrier).val =
      AffinoidAtlasPresentation.FieldPoint.point (L := L) (A := S.presentation) p := hx
  have hp : AffinoidAtlasPresentation.FieldPoint.point (L := L) (A := S.presentation) p ∈
      D.carrier := hx'' ▸ x.property
  let q := AffinoidAtlasPresentation.FieldPoint.restrictOriginalDomain p D hp
  refine ⟨q, Subtype.ext hx''.symm, ?_⟩
  change q.map (S.domainInclusion D) (S.domain D).hasAllLocalDomains = p
  exact fieldPoint_map_restrictOriginalDomain D p hp

/-- Affinoid domain embeddings have pointed lifts. -/
theorem pointedFieldPointLift_of_isAffinoidDomainEmbedding
    {V W : LocalizedCategory.{u, v, v} (K := K)} {j : V ⟶ W}
    (hj : IsAffinoidDomainEmbedding j) : PointedFieldPointLift L j := by
  obtain ⟨i, e, rfl⟩ := hj
  exact (pointedFieldPointLift_of_isIso e.hom).comp
    (pointedFieldPointLift_localizedDomainInclusion _ _)

variable [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]

/-- The image of an all-pieces étale strong map has pointed lifts: it is finite at every source
point, and the full field-point lift of a finite map can be taken at any prescribed point. -/
theorem pointedFieldPointLift_localizationFunctor_map_of_etale
    {A B : AffinoidAtlasPresentation.{u, v, v} K} (g : ofSaturation A ⟶ ofSaturation B)
    (hg : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces (A := A) (B := B) g) :
    PointedFieldPointLift L (localizationFunctor.map g) := by
  intro p x hx
  rw [localizedSpaceFunctor_map] at hx
  have hx' : AffinoidAtlasPresentation.FieldPoint.point
      (L := L) (A := B.saturatedPresentation) p = g.baseMap x := hx.symm
  obtain ⟨q, hq, hqp⟩ := (hg.isEtale.isQuasifinite x).hasFieldPointLiftAt
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity p hx'
  exact ⟨q, hq, hqp⟩

/-- Localized étale morphisms have pointed lifts. -/
theorem pointedFieldPointLift_of_etale {X Y : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ Y} (hf : etale f) : PointedFieldPointLift L f := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  exact (pointedFieldPointLift_localizationFunctor_map_of_etale g hg).of_arrow_iso e

/-- The image of a quasi-étale strong map has pointed lifts: near the prescribed source point,
the map is an affinoid domain embedding followed by an étale morphism. -/
theorem pointedFieldPointLift_localizationFunctor_map_of_quasiEtale
    {A B : AffinoidAtlasPresentation.{u, v, v} K} (g : ofSaturation A ⟶ ofSaturation B)
    (hg : IsQuasiEtale g) : PointedFieldPointLift L (localizationFunctor.map g) := by
  intro p x hx
  obtain ⟨σ, -, hn, hσ⟩ := hg x
  obtain ⟨V, hVσ, hxV⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨i, hV, W, w, j, hw, hj, hjw⟩ := hσ V hVσ
  let D := (ofSaturation A).chartDomain i
  have hxD : x ∈ D.carrier := by
    rw [chartDomain_carrier, hV]
    exact hxV
  let x' : localizedSpaceFunctor.obj (localizationFunctor.obj ((ofSaturation A).domain D)) :=
    (⟨x, hxD⟩ : D.carrier)
  have hx' : localizedSpaceFunctor.map ((ofSaturation A).localizedDomainInclusion D) x' = x :=
    localizedSpaceFunctor_map_localizedDomainInclusion _ D ⟨x, hxD⟩
  have hjw' : localizedSpaceFunctor.map (j ≫ w) x' =
      ((localizedFieldPointProjection L).app _ p).down := by
    rw [hjw, Functor.map_comp, TopCat.comp_app, hx', hx]
  obtain ⟨q, hq, hqp⟩ := ((pointedFieldPointLift_of_isAffinoidDomainEmbedding hj).comp
    (pointedFieldPointLift_of_etale hw)) p x' hjw'
  refine ⟨(localizedFieldPointFunctor L).map
    ((ofSaturation A).localizedDomainInclusion D) q, ?_, ?_⟩
  · rw [localizedFieldPointProjection_map_down, hq, hx']
  · rw [← Functor.map_comp_apply, ← hjw, hqp]

/-- Localized quasi-étale morphisms have pointed lifts. -/
theorem pointedFieldPointLift_of_quasiEtale {X Y : LocalizedCategory.{u, v, v} (K := K)}
    {f : X ⟶ Y} (hf : quasiEtale f) : PointedFieldPointLift L f := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  exact (pointedFieldPointLift_localizationFunctor_map_of_quasiEtale g hg).of_arrow_iso e

end Pointed

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]

/-- An `L`-valued point of the target of a quasi-étale morphism lifts to the source whenever its
underlying point lies in the image. -/
theorem localizedQuasiEtaleFieldPointImageLift :
    LocalizedQuasiEtaleFieldPointImageLiftStatement.{u, v, uL} K L := by
  intro A B f hf p hp
  obtain ⟨x, hx⟩ := hp
  obtain ⟨q, -, hq⟩ := pointedFieldPointLift_of_quasiEtale hf p x hx
  exact ⟨q, hq⟩

end Langlands.Analytic.SaturatedAtlasPresentation
