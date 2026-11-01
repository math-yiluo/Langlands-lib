import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedFamilyExtension

/-! # Complete bounded atlas maps on the actual coset copies -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type v} [Group G] [TopologicalSpace G] (H : Subgroup G)

/-- Assemble chosen bounded atlas maps into an arbitrary actual atlas target. -/
def assembleCopyAtlasMap {X : NormContinuousSpace K H}
    {Y : AffinoidAtlasPresentation.{u, max u v, v} K}
    (f : G ⧸ H → ((localFamily H X).atlasPresentation ⟶ Y)) :
    (family H X.unop).atlasPresentation ⟶ Y where
  baseMap :=
    { toFun := fun z => (f z.fst).baseMap ⟨PUnit.unit, z.snd⟩
      continuous_toFun := continuous_sigma fun c =>
        (f c).baseMap.continuous.comp
          (continuous_sigmaMk (σ := fun _ : PUnit.{v+1} =>
            LocalSpectrum H X.unop) (i := PUnit.unit)) }
  indexMap c := (f c.val).indexMap ⟨PUnit.unit, c.property⟩
  index_mono c d h := by
    have he := DisjointAffinoidAtlas.chart_eq_of_subset (family H X.unop).algebra c d h
    subst d
    exact Set.Subset.rfl
  pullback c := (f c.val).pullback ⟨PUnit.unit, c.property⟩
  chart_comm c x := (f c.val).chart_comm ⟨PUnit.unit, c.property⟩ x
  restriction_comm c d h := by
    have he := DisjointAffinoidAtlas.chart_eq_of_subset (family H X.unop).algebra c d h
    subst d
    rw [(family H X.unop).atlasPresentation.atlas.restriction_id, Y.atlas.restriction_id]
    exact BoundedAlgHom.ext fun _ => rfl

/-- Every complete copy map is recovered, including its chosen chart and pullback. -/
@[simp]
theorem copyMap_assembleCopyAtlasMap {X : NormContinuousSpace K H}
    {Y : AffinoidAtlasPresentation.{u, max u v, v} K}
    (f : G ⧸ H → ((localFamily H X).atlasPresentation ⟶ Y))
    (c : G ⧸ H) :
    (copyMap H X c).atlasMap ≫ assembleCopyAtlasMap H f = f c := by
  apply AffinoidAtlasPresentation.Hom.ext
  · apply ContinuousMap.ext
    rintro ⟨⟨⟩, x⟩
    rfl
  · funext i
    obtain ⟨⟨⟩, hi⟩ := i
    rfl
  · apply heq_of_eq
    funext i
    obtain ⟨⟨⟩, hi⟩ := i
    exact BoundedAlgHom.ext fun _ => rfl

/-- Copy restrictions determine the entire bounded atlas arrow, for any target. -/
theorem familyAtlasHom_ext {X : NormContinuousSpace K H}
    {Y : AffinoidAtlasPresentation.{u, max u v, v} K}
    {f k : (family H X.unop).atlasPresentation ⟶ Y}
    (h : ∀ c, (copyMap H X c).atlasMap ≫ f = (copyMap H X c).atlasMap ≫ k) :
    f = k := by
  cases f with
  | mk fb fi fm fp fc fr =>
    cases k with
    | mk kb ki km kp kc kr =>
      have hb : fb = kb := by
        apply ContinuousMap.ext
        rintro ⟨c, x⟩
        exact congrArg
          (fun q : (localFamily H X).atlasPresentation ⟶ Y =>
            q.baseMap ⟨PUnit.unit, x⟩) (h c)
      have hi : fi = ki := funext fun c =>
        congrFun (congrArg AffinoidAtlasPresentation.Hom.indexMap (h c.val))
          ⟨PUnit.unit, c.property⟩
      subst ki
      apply AffinoidAtlasPresentation.Hom.ext
        (f := ⟨fb, fi, fm, fp, fc, fr⟩) (g := ⟨kb, fi, km, kp, kc, kr⟩) hb rfl
      apply heq_of_eq
      funext c
      have hc := congrArg
        (fun q : (localFamily H X).atlasPresentation ⟶ Y =>
          (⟨q.indexMap ⟨PUnit.unit, c.property⟩,
            q.pullback ⟨PUnit.unit, c.property⟩⟩ :
            Σ j, BoundedAlgHom K (Y.atlas.algebra j) X.unop.obj.V)) (h c.val)
      have he := eq_of_heq (Sigma.mk.inj hc).2
      change (BoundedAlgHom.id K X.unop.obj.V).comp (fp c) =
        (BoundedAlgHom.id K X.unop.obj.V).comp (kp c) at he
      exact he

/-- The actual coset atlas is a coproduct of its one-component atlas copies. -/
def copyAtlasHomEquiv {X : NormContinuousSpace K H}
    {Y : AffinoidAtlasPresentation.{u, max u v, v} K} :
    ((family H X.unop).atlasPresentation ⟶ Y) ≃
      (G ⧸ H → ((localFamily H X).atlasPresentation ⟶ Y)) where
  toFun p c := (copyMap H X c).atlasMap ≫ p
  invFun := assembleCopyAtlasMap H
  left_inv p := by
    apply familyAtlasHom_ext H
    intro c
    exact copyMap_assembleCopyAtlasMap H _ c
  right_inv f := funext (copyMap_assembleCopyAtlasMap H f)

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
