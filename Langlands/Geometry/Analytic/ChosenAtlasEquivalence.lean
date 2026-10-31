import Langlands.Geometry.Analytic.ChosenAtlasReconstruction

/-! # Chosen atlas isomorphisms from compatible bounded chart equivalences -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An equivalence of actual chart containments with compatible bounded algebra
 equivalences. Neither an ambient map nor its inverse is supplied. -/
structure ChartEquivData (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  indexEquiv : A.atlas.Index ≃ B.atlas.Index
  chart_subset_iff : ∀ i j,
    Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j) ↔
      Set.range (B.atlas.chart (indexEquiv i)) ⊆ Set.range (B.atlas.chart (indexEquiv j))
  pullbackEquiv : ∀ i,
    BoundedAlgEquiv K (B.atlas.algebra (indexEquiv i)) (A.atlas.algebra i)
  restriction_comm : ∀ i j h,
    (A.atlas.restriction i j h).comp (pullbackEquiv j).toBoundedAlgHom =
      (pullbackEquiv i).toBoundedAlgHom.comp
        (B.atlas.restriction (indexEquiv i) (indexEquiv j) ((chart_subset_iff i j).mp h))

namespace ChartEquivData

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The index equivalence is an order isomorphism for actual chart containment. -/
def chartOrderIso (d : ChartEquivData A B) :
    IndexedAffinoidAtlas.ChartObject A.atlas ≃o IndexedAffinoidAtlas.ChartObject B.atlas where
  toFun i := ⟨d.indexEquiv i.index⟩
  invFun j := ⟨d.indexEquiv.symm j.index⟩
  left_inv i := IndexedAffinoidAtlas.ChartObject.ext (d.indexEquiv.symm_apply_apply i.index)
  right_inv j := IndexedAffinoidAtlas.ChartObject.ext (d.indexEquiv.apply_symm_apply j.index)
  map_rel_iff' := fun {i j} => (d.chart_subset_iff i.index j.index).symm

/-- The forward compatible bounded data, with no ambient map as input. -/
def forwardData (d : ChartEquivData A B) : ChartMapData A B where
  indexMap := d.indexEquiv
  index_mono i j := (d.chart_subset_iff i j).mp
  pullback i := (d.pullbackEquiv i).toBoundedAlgHom
  restriction_comm := d.restriction_comm

/-- The inverse local bounded map, transported only along the index inverse law. -/
def inversePullback (d : ChartEquivData A B) (j : B.atlas.Index) :
    BoundedAlgHom K (A.atlas.algebra (d.indexEquiv.symm j)) (B.atlas.algebra j) := by
  exact cast (congrArg (fun k => BoundedAlgHom K
    (A.atlas.algebra (d.indexEquiv.symm j)) (B.atlas.algebra k))
    (d.indexEquiv.apply_symm_apply j))
    (d.pullbackEquiv (d.indexEquiv.symm j)).symm.toBoundedAlgHom

/-- The transported inverse is heterogeneously equal to the local inverse. -/
theorem inversePullback_heq (d : ChartEquivData A B) (j : B.atlas.Index)
    (i : A.atlas.Index) (h : d.indexEquiv.symm j = i) :
    HEq (d.inversePullback j) (d.pullbackEquiv i).symm.toBoundedAlgHom := by
  subst i
  exact cast_heq _ _

/-- The transport retains the original bounded inverse at corresponding indices. -/
theorem inversePullback_index (d : ChartEquivData A B) (i : A.atlas.Index) :
    HEq (d.inversePullback (d.indexEquiv i))
      (d.pullbackEquiv i).symm.toBoundedAlgHom := by
  exact d.inversePullback_heq _ _ (d.indexEquiv.symm_apply_apply i)

/-- Containment is preserved by the inverse choice of charts. -/
theorem inverse_mono (d : ChartEquivData A B) (i j : B.atlas.Index)
    (h : Set.range (B.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    Set.range (A.atlas.chart (d.indexEquiv.symm i)) ⊆
      Set.range (A.atlas.chart (d.indexEquiv.symm j)) := by
  exact d.chartOrderIso.symm.monotone
    (show (⟨i⟩ : IndexedAffinoidAtlas.ChartObject B.atlas) ≤ ⟨j⟩ from h)

/-- Inverting the algebra equivalences reverses every restriction square. -/
theorem inverse_restriction_comm (d : ChartEquivData A B) (i j : B.atlas.Index)
    (h : Set.range (B.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    (B.atlas.restriction i j h).comp (d.inversePullback j) =
      (d.inversePullback i).comp
        (A.atlas.restriction (d.indexEquiv.symm i) (d.indexEquiv.symm j)
          (d.inverse_mono i j h)) := by
  obtain ⟨i, rfl⟩ := d.indexEquiv.surjective i
  obtain ⟨j, rfl⟩ := d.indexEquiv.surjective j
  have hsquare (i' j' : A.atlas.Index) (hi' : i' = i) (hj' : j' = j)
      (ψi : BoundedAlgHom K (A.atlas.algebra i') (B.atlas.algebra (d.indexEquiv i)))
      (ψj : BoundedAlgHom K (A.atlas.algebra j') (B.atlas.algebra (d.indexEquiv j)))
      (hψi : HEq ψi (d.pullbackEquiv i).symm.toBoundedAlgHom)
      (hψj : HEq ψj (d.pullbackEquiv j).symm.toBoundedAlgHom)
      (h' : Set.range (A.atlas.chart i') ⊆ Set.range (A.atlas.chart j')) :
      (B.atlas.restriction (d.indexEquiv i) (d.indexEquiv j) h).comp ψj =
        ψi.comp (A.atlas.restriction i' j' h') := by
    subst i'
    subst j'
    rw [eq_of_heq hψi, eq_of_heq hψj]
    apply BoundedAlgHom.ext
    intro x
    apply (d.pullbackEquiv i).toAlgEquiv.injective
    have hc := d.restriction_comm i j h'
    have hx := congrArg (fun f => f ((d.pullbackEquiv j).symm x)) hc
    simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
      BoundedAlgEquiv.apply_symm_apply] using hx.symm
  exact hsquare _ _ (d.indexEquiv.symm_apply_apply i) (d.indexEquiv.symm_apply_apply j)
    _ _ (d.inversePullback_index i) (d.inversePullback_index j) _

/-- Construct all inverse bounded data from the original equivalences. -/
def inverseData (d : ChartEquivData A B) : ChartMapData B A where
  indexMap := d.indexEquiv.symm
  index_mono := d.inverse_mono
  pullback := d.inversePullback
  restriction_comm := d.inverse_restriction_comm

/-- Reconstruct the forward ambient continuous map and chosen arrow. -/
def hom (d : ChartEquivData A B) : A ⟶ B := d.forwardData.toHom

/-- Reconstruct the inverse ambient continuous map and chosen arrow. -/
def inv (d : ChartEquivData A B) : B ⟶ A := d.inverseData.toHom

/-- The reconstructed arrows compose to the identity with all bounded data retained. -/
@[simp]
theorem hom_inv_id (d : ChartEquivData A B) : d.hom ≫ d.inv = 𝟙 A := by
  apply (ChartMapData.homEquiv (A := A) (B := A)).symm.injective
  apply ChartMapData.ext
  · funext i
    exact d.indexEquiv.symm_apply_apply i
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    change HEq ((d.pullbackEquiv i).toBoundedAlgHom.comp
      (d.inversePullback (d.indexEquiv i))) (BoundedAlgHom.id K (A.atlas.algebra i))
    have hcomp (i' : A.atlas.Index) (hi' : i' = i)
        (ψ : BoundedAlgHom K (A.atlas.algebra i') (B.atlas.algebra (d.indexEquiv i)))
        (hψ : HEq ψ (d.pullbackEquiv i).symm.toBoundedAlgHom) :
        HEq ((d.pullbackEquiv i).toBoundedAlgHom.comp ψ)
          (BoundedAlgHom.id K (A.atlas.algebra i)) := by
      subst i'
      rw [eq_of_heq hψ]
      apply heq_of_eq
      apply BoundedAlgHom.ext
      intro x
      exact (d.pullbackEquiv i).apply_symm_apply x
    exact hcomp _ (d.indexEquiv.symm_apply_apply i) _ (d.inversePullback_index i)

/-- The reverse composite is also the identity on the chosen presentation. -/
@[simp]
theorem inv_hom_id (d : ChartEquivData A B) : d.inv ≫ d.hom = 𝟙 B := by
  apply (ChartMapData.homEquiv (A := B) (B := B)).symm.injective
  apply ChartMapData.ext
  · funext j
    exact d.indexEquiv.apply_symm_apply j
  · apply Function.hfunext rfl
    intro j k hjk
    cases eq_of_heq hjk
    obtain ⟨i, rfl⟩ := d.indexEquiv.surjective j
    change HEq ((d.inversePullback (d.indexEquiv i)).comp
      (d.pullbackEquiv (d.indexEquiv.symm (d.indexEquiv i))).toBoundedAlgHom)
      (BoundedAlgHom.id K (B.atlas.algebra (d.indexEquiv i)))
    have hcomp (i' : A.atlas.Index) (hi' : i' = i)
        (ψ : BoundedAlgHom K (A.atlas.algebra i') (B.atlas.algebra (d.indexEquiv i)))
        (hψ : HEq ψ (d.pullbackEquiv i).symm.toBoundedAlgHom) :
        HEq (ψ.comp (d.pullbackEquiv i').toBoundedAlgHom)
          (BoundedAlgHom.id K (B.atlas.algebra (d.indexEquiv i))) := by
      subst i'
      rw [eq_of_heq hψ]
      apply heq_of_eq
      apply BoundedAlgHom.ext
      intro x
      exact (d.pullbackEquiv i).symm_apply_apply x
    exact hcomp _ (d.indexEquiv.symm_apply_apply i) _ (d.inversePullback_index i)

/-- A chosen atlas isomorphism constructed only from bounded chart equivalences. -/
def iso (d : ChartEquivData A B) : A ≅ B where
  hom := d.hom
  inv := d.inv
  hom_inv_id := d.hom_inv_id
  inv_hom_id := d.inv_hom_id

/-- The reconstructed continuous maps give a homeomorphism of the actual spaces. -/
def homeomorph (d : ChartEquivData A B) : A.space ≃ₜ B.space where
  toFun := d.hom.baseMap
  invFun := d.inv.baseMap
  left_inv x := congrArg (fun f : A ⟶ A => f.baseMap x) d.hom_inv_id
  right_inv y := congrArg (fun f : B ⟶ B => f.baseMap y) d.inv_hom_id
  continuous_toFun := d.hom.baseMap.continuous
  continuous_invFun := d.inv.baseMap.continuous

/-- On each chart the homeomorphism is exactly the actual bounded spectrum map. -/
theorem homeomorph_chart (d : ChartEquivData A B) (i : A.atlas.Index)
    (x : BanachSpectrum (A.atlas.algebra i)) :
    d.homeomorph (A.atlas.chart i x) =
      B.atlas.chart (d.indexEquiv i) ((d.pullbackEquiv i).spectrumHomeomorph x) :=
  (d.hom.chart_comm i x).symm

/-- The inverse homeomorphism retains precisely the constructed bounded inverses. -/
theorem homeomorph_symm_chart (d : ChartEquivData A B) (j : B.atlas.Index)
    (y : BanachSpectrum (B.atlas.algebra j)) :
    d.homeomorph.symm (B.atlas.chart j y) =
      A.atlas.chart (d.indexEquiv.symm j)
        (BanachSpectrum.comap (d.inversePullback j).toBoundedRingHom y) :=
  (d.inv.chart_comm j y).symm

/-- At corresponding indices the inverse chart formula uses the original spectrum inverse. -/
theorem homeomorph_symm_chart_index (d : ChartEquivData A B) (i : A.atlas.Index)
    (y : BanachSpectrum (B.atlas.algebra (d.indexEquiv i))) :
    d.homeomorph.symm (B.atlas.chart (d.indexEquiv i) y) =
      A.atlas.chart i ((d.pullbackEquiv i).spectrumHomeomorph.symm y) := by
  apply d.homeomorph.injective
  rw [Homeomorph.apply_symm_apply, d.homeomorph_chart, Homeomorph.apply_symm_apply]

/-- The constructed ambient homeomorphism carries each whole chart onto its partner. -/
theorem homeomorph_image_chart (d : ChartEquivData A B) (i : A.atlas.Index) :
    d.homeomorph '' Set.range (A.atlas.chart i) =
      Set.range (B.atlas.chart (d.indexEquiv i)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(d.pullbackEquiv i).spectrumHomeomorph x, (d.homeomorph_chart i x).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨A.atlas.chart i ((d.pullbackEquiv i).spectrumHomeomorph.symm z), ⟨_, rfl⟩, ?_⟩
    rw [d.homeomorph_chart, Homeomorph.apply_symm_apply]

end ChartEquivData

end Langlands.Analytic.AffinoidAtlasPresentation
