import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedFunctor

/-! # Equivariant bounded atlases on actual induced affinoid spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The quotient action with bounded pullbacks on every admissible chart pair. -/
def strongActionMap (X : NormContinuousSpace K H) (g : G) :
    AffinoidAtlasPresentation.StrongHom
      (atlasPresentation H hH X) (atlasPresentation H hH X) where
  baseMap := ⟨(fun z : Spectrum H X.unop => g • z),
    show Continuous (fun z : Spectrum H X.unop => g • z) from continuous_const_smul g⟩
  target_exists c := ⟨chartTarget H X.unop hH g c, image_chart_subset H X.unop hH g c⟩
  pullback := chartPullback H X.unop hH g
  chart_comm := chartPullback_chart H X.unop hH g
  restriction_comm := chartPullback_naturality H X.unop hH g

/-- Each full-group element is an actual bounded chosen-atlas endomorphism. -/
def atlasActionMap (X : NormContinuousSpace K H) (g : G) :
    atlasPresentation H hH X ⟶ atlasPresentation H hH X where
  baseMap := ⟨(fun z : Spectrum H X.unop => g • z),
    show Continuous (fun z : Spectrum H X.unop => g • z) from continuous_const_smul g⟩
  indexMap := chartTarget H X.unop hH g
  index_mono c c' hc := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c c' hc
    subst c'
    exact Set.Subset.rfl
  pullback c := pullback H X.unop g c.val
  chart_comm c x := (actionMap_realization H X.unop hH g ⟨c.val, x⟩).symm
  restriction_comm c c' hc := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c c' hc
    subst c'
    exact chartPullback_naturality H X.unop hH g c c
      (chartTarget H X.unop hH g c) (chartTarget H X.unop hH g c) hc Set.Subset.rfl
      (image_chart_subset H X.unop hH g c) (image_chart_subset H X.unop hH g c)

@[simp]
theorem atlasActionMap_one (X : NormContinuousSpace K H) :
    atlasActionMap H hH X 1 = 𝟙 (atlasPresentation H hH X) := by
  apply AffinoidAtlasPresentation.Hom.ext
    (ContinuousMap.ext fun (z : Spectrum H X.unop) => one_smul G z)
    (funext (chartTarget_one H X.unop hH))
  exact heq_of_eq (funext fun c => pullback_one H X.unop c.val)

theorem atlasActionMap_mul (X : NormContinuousSpace K H) (g k : G) :
    atlasActionMap H hH X (g * k) =
      atlasActionMap H hH X k ≫ atlasActionMap H hH X g := by
  apply AffinoidAtlasPresentation.Hom.ext
    (ContinuousMap.ext fun (z : Spectrum H X.unop) => mul_smul g k z)
    (funext (chartTarget_mul H X.unop hH g k))
  exact heq_of_eq (funext fun c => pullback_mul H X.unop g k c.val)

/-- The full group acts through bounded atlas maps on the actual balanced quotient. -/
def atlasAction (X : NormContinuousSpace K H) :
    Action (AffinoidAtlasPresentation.{u, max u v, v} K) G where
  V := atlasPresentation H hH X
  ρ :=
    { toFun := atlasActionMap H hH X
      map_one' := atlasActionMap_one H hH X
      map_mul' := atlasActionMap_mul H hH X }

/-- The inverse of each bounded atlas map is supplied by the full-group action. -/
def atlasAutomorphisms (X : NormContinuousSpace K H) :
    G →* Aut (atlasPresentation H hH X) :=
  (atlasAction H hH X).ρAut

/-- Induced maps intertwine the entire bounded atlas endomorphisms. -/
theorem atlasMap_equivariant {X Y : NormContinuousSpace K H} (f : X ⟶ Y) (g : G) :
    atlasActionMap H hH X g ≫ atlasMap H hH f =
      atlasMap H hH f ≫ atlasActionMap H hH Y g := by
  apply AffinoidAtlasPresentation.Hom.ext
    (ContinuousMap.ext fun z => balancedMap_equivariant H f g z)
    (funext fun c => Subtype.ext (by rfl))
  apply heq_of_eq
  funext c
  apply BoundedAlgHom.ext
  intro a
  change (X.unop.actionAut (correction H g c.val)).inv.toAlgHom
      (NormContinuousAction.homMap f.unop a) =
    NormContinuousAction.homMap f.unop
      ((Y.unop.actionAut (correction H g c.val)).inv.toAlgHom a)
  exact (NormContinuousAction.homMap_apply_action f.unop (correction H g c.val)⁻¹ a).symm

/-- Functorial induction retaining the full-group action and actual bounded atlas maps. -/
def equivariantAtlasFunctor : NormContinuousSpace K H ⥤
    Action (AffinoidAtlasPresentation.{u, max u v, v} K) G where
  obj := atlasAction H hH
  map f := ⟨atlasMap H hH f, atlasMap_equivariant H hH f⟩
  map_id X := Action.Hom.ext (atlasMap_id H hH X)
  map_comp f k := Action.Hom.ext (atlasMap_comp H hH f k)

/-- Forgetting the group action recovers precisely the constructed atlas functor. -/
theorem equivariantAtlasFunctor_forget :
    equivariantAtlasFunctor (K := K) H hH ⋙
        Action.forget (AffinoidAtlasPresentation.{u, max u v, v} K) G =
      atlasFunctor H hH := rfl

/-- The realized bounded atlas action is jointly continuous on the actual quotient. -/
def continuousAtlasFunctor :
    NormContinuousSpace K H ⥤ ContAction TopCat.{max u v} G :=
  (Action.isContinuous TopCat G).lift
    (equivariantAtlasFunctor H hH ⋙ AffinoidAtlasPresentation.spaceFunctor.mapAction G)
    (fun X => (Action.isContinuous_def _).mpr (by
      change Continuous (fun p : G × Spectrum H X.unop => p.1 • p.2)
      exact continuous_smul))

/-- The continuous realization is exactly the original balanced-quotient functor. -/
theorem continuousAtlasFunctor_eq_balancedFunctor :
    continuousAtlasFunctor (K := K) H hH = balancedFunctor H := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
