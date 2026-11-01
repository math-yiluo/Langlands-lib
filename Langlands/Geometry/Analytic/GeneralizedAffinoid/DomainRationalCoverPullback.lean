import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Rational restriction of actual finite full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

private theorem hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

/-- Intersect an actual domain inclusion with a fixed ambient rational chart.
The full representation constructs its bounded restriction. -/
def rationalInterMap (d : RationalChart K A) {U V : Domain K A} (f : U ⟶ V) :
    U.rationalInter d ⟶ V.rationalInter d :=
  rationalInterLift (U.rationalInterLeft d ≫ f) (U.rationalInterRight d)

@[simp] theorem rationalInterMap_left (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    rationalInterMap d f ≫ V.rationalInterLeft d = U.rationalInterLeft d ≫ f :=
  hom_unique _ _

@[simp] theorem rationalInterMap_right (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    rationalInterMap d f ≫ V.rationalInterRight d = U.rationalInterRight d :=
  hom_unique _ _

/-- The actual bounded restriction commutes with both left projections. -/
theorem rationalInterMap_restriction_comp_left (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    (rationalInterMap d f).restriction.comp (V.rationalInterLeft d).restriction =
      (U.rationalInterLeft d).restriction.comp f.restriction :=
  congrArg Inclusion.restriction (rationalInterMap_left d f)

/-- Rational intersection is functorial on actual represented domains. -/
def rationalInterFunctor (d : RationalChart K A) : Domain K A ⥤ Domain K A where
  obj U := U.rationalInter d
  map f := rationalInterMap d f
  map_id _ := hom_unique _ _
  map_comp _ _ := hom_unique _ _

/-- The actual quotient structural maps give a natural projection. -/
def rationalInterLeftNat (d : RationalChart K A) :
    rationalInterFunctor d ⟶ 𝟭 (Domain K A) where
  app U := U.rationalInterLeft d
  naturality _ _ _ := hom_unique _ _

/-- Quotient transport to the fixed rational chart is also natural. -/
def rationalInterRightNat (d : RationalChart K A) :
    rationalInterFunctor d ⟶ (Functor.const (Domain K A)).obj d.toDomain where
  app U := U.rationalInterRight d
  naturality _ _ _ := hom_unique _ _

/-- The naturality square of rational restriction has the actual two
bounded restrictions as projections. -/
def rationalInterMapPullbackCone (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    PullbackCone f (V.rationalInterLeft d) :=
  PullbackCone.mk (U.rationalInterLeft d) (rationalInterMap d f)
    (rationalInterMap_left d f).symm

/-- Full-test representation constructs the lift into the rational
intersection; uniqueness of actual domain arrows proves the limit laws. -/
def rationalInterMapPullbackConeIsLimit (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    IsLimit (rationalInterMapPullbackCone d f) :=
  PullbackCone.IsLimit.mk _
    (fun S => rationalInterLift S.fst (S.snd ≫ V.rationalInterRight d))
    (fun _ => hom_unique _ _)
    (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

/-- The naturality square also commutes on actual quotient spectra. -/
theorem rationalInterMap_spectrum_left (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    TopCat.ofHom (rationalInterMap d f).spectrumMap ≫
        TopCat.ofHom (V.rationalInterLeft d).spectrumMap =
      TopCat.ofHom (U.rationalInterLeft d).spectrumMap ≫
        TopCat.ofHom f.spectrumMap := by
  apply TopCat.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun φ : BoundedAlgHom K V.algebra (U.rationalInter d).algebra =>
    x (φ a)) (rationalInterMap_restriction_comp_left d f)

/-- The actual spectrum square over the original component spectrum map. -/
def rationalInterMapSpectrumCone (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    PullbackCone (TopCat.ofHom f.spectrumMap)
      (TopCat.ofHom (V.rationalInterLeft d).spectrumMap) :=
  PullbackCone.mk (TopCat.ofHom (U.rationalInterLeft d).spectrumMap)
    (TopCat.ofHom (rationalInterMap d f).spectrumMap)
    (rationalInterMap_spectrum_left d f).symm

/-- Cancelling the right rational spectrum pullback from the outer rational
spectrum pullback proves the actual component spectrum square is a limit. -/
def rationalInterMapSpectrumConeIsLimit (d : RationalChart K A)
    {U V : Domain K A} (f : U ⟶ V) :
    IsLimit (rationalInterMapSpectrumCone d f) := by
  have hright :
      TopCat.ofHom (rationalInterMap d f).spectrumMap ≫
          TopCat.ofHom (V.rationalInterRight d).spectrumMap =
        TopCat.ofHom (U.rationalInterRight d).spectrumMap := by
    apply TopCat.ext
    intro x
    apply BanachSpectrum.ext
    intro a
    exact congrArg
      (fun φ : BoundedAlgHom K d.algebra (U.rationalInter d).algebra => x (φ a))
      (congrArg Inclusion.restriction (rationalInterMap_right d f))
  have hbase :
      TopCat.ofHom f.spectrumMap ≫ TopCat.ofHom V.spectrumMap =
        TopCat.ofHom U.spectrumMap := by
    apply TopCat.ext
    intro x
    exact f.spectrumMap_over_base x
  have hU :
      IsPullback (TopCat.ofHom (U.rationalInterLeft d).spectrumMap)
        (TopCat.ofHom (U.rationalInterRight d).spectrumMap)
        (TopCat.ofHom U.spectrumMap) (TopCat.ofHom d.spectrumMap) :=
    .of_isLimit (U.rationalInterSpectrumConeIsLimit d)
  have hV :
      IsPullback (TopCat.ofHom (V.rationalInterLeft d).spectrumMap)
        (TopCat.ofHom (V.rationalInterRight d).spectrumMap)
        (TopCat.ofHom V.spectrumMap) (TopCat.ofHom d.spectrumMap) :=
    .of_isLimit (V.rationalInterSpectrumConeIsLimit d)
  have houter :
      IsPullback
        (TopCat.ofHom (rationalInterMap d f).spectrumMap ≫
          TopCat.ofHom (V.rationalInterRight d).spectrumMap)
        (TopCat.ofHom (U.rationalInterLeft d).spectrumMap)
        (TopCat.ofHom d.spectrumMap)
        (TopCat.ofHom f.spectrumMap ≫ TopCat.ofHom V.spectrumMap) := by
    rw [hright, hbase]
    exact hU.flip
  exact (houter.of_right (rationalInterMap_spectrum_left d f) hV.flip).flip.isLimit

namespace FiniteCover

variable {U : Domain K A}

/-- Restrict any actual finite full-domain cover along an ambient rational
chart, retaining its index and taking actual pulled rational quotients. -/
def rationalInter (c : FiniteCover U) (d : RationalChart K A) :
    FiniteCover (U.rationalInter d) where
  size := c.size
  obj i := (c.obj i).rationalInter d
  map i := rationalInterMap d (c.map i)
  covers x hx := by
    obtain ⟨i, hi⟩ := c.covers x hx.1
    exact ⟨i, hi, hx.2⟩

@[simp] theorem rationalInter_size (c : FiniteCover U) (d : RationalChart K A) :
    (c.rationalInter d).size = c.size := rfl

@[simp] theorem rationalInter_obj (c : FiniteCover U) (d : RationalChart K A)
    (i : Fin c.size) :
    (c.rationalInter d).obj i = (c.obj i).rationalInter d := rfl

@[simp] theorem rationalInter_obj_algebra (c : FiniteCover U)
    (d : RationalChart K A) (i : Fin c.size) :
    ((c.rationalInter d).obj i).algebra =
      (RationalChart.pullback (c.obj i).baseMap d).algebra := rfl

@[simp] theorem rationalInter_map (c : FiniteCover U) (d : RationalChart K A)
    (i : Fin c.size) :
    (c.rationalInter d).map i = rationalInterMap d (c.map i) := rfl

/-- The cover has exactly the ordinary intersection loci at its components. -/
@[simp] theorem rationalInter_obj_locus (c : FiniteCover U)
    (d : RationalChart K A) (i : Fin c.size) :
    ((c.rationalInter d).obj i).locus = (c.obj i).locus ∩ d.locus := rfl

/-- Each new cover component is the constructed categorical pullback of
the original component along the target's rational restriction. -/
def rationalInterComponentConeIsLimit (c : FiniteCover U)
    (d : RationalChart K A) (i : Fin c.size) :
    IsLimit (rationalInterMapPullbackCone d (c.map i)) :=
  rationalInterMapPullbackConeIsLimit d (c.map i)

/-- Each finite-cover component square is a pullback of the actual
representing spectra, without any injectivity hypothesis for full domains. -/
def rationalInterComponentSpectrumConeIsLimit (c : FiniteCover U)
    (d : RationalChart K A) (i : Fin c.size) :
    IsLimit (rationalInterMapSpectrumCone d (c.map i)) :=
  rationalInterMapSpectrumConeIsLimit d (c.map i)

/-- Every chosen refinement index is retained under rational restriction. -/
def Refinement.rationalInter {b c : FiniteCover U} (r : Refinement b c)
    (d : RationalChart K A) :
    Refinement (b.rationalInter d) (c.rationalInter d) where
  index := r.index
  map i := rationalInterMap d (r.map i)

@[simp] theorem Refinement.rationalInter_index {b c : FiniteCover U}
    (r : Refinement b c) (d : RationalChart K A) :
    (r.rationalInter d).index = r.index := rfl

@[simp] theorem Refinement.rationalInter_map {b c : FiniteCover U}
    (r : Refinement b c) (d : RationalChart K A) (i : Fin b.size) :
    (r.rationalInter d).map i = rationalInterMap d (r.map i) := rfl

/-- Rational restriction acts on finite covers and their actual refinements. -/
def rationalInterFunctor (U : Domain K A) (d : RationalChart K A) :
    FiniteCover U ⥤ FiniteCover (U.rationalInter d) where
  obj c := c.rationalInter d
  map r := r.rationalInter d
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- The component spectrum triangle uses the original component spectrum
map after the actual rational quotient projection. -/
theorem rationalInter_componentMap (c : FiniteCover U)
    (d : RationalChart K A) (i : Fin c.size) :
    (U.rationalInterLeft d).locusMap.comp ((c.rationalInter d).componentMap i) =
      (c.componentMap i).comp ((c.obj i).rationalInterLeft d).spectrumMap := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact ((c.obj i).rationalInterLeft d).spectrumMap_over_base x |>.symm

/-- The new disjoint union of actual rational quotient spectra maps to the
old disjoint union through its component bounded projections. -/
def rationalInterSpectrumMap (c : FiniteCover U) (d : RationalChart K A) :
    C((Σ i : Fin c.size, BanachSpectrum ((c.rationalInter d).obj i).algebra),
      (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra)) where
  toFun x := ⟨x.1, ((c.obj x.1).rationalInterLeft d).spectrumMap x.2⟩
  continuous_toFun := continuous_sigma fun i =>
    (continuous_sigmaMk
      (σ := fun j : Fin c.size => BanachSpectrum (c.obj j).algebra)
      (i := i)).comp ((c.obj i).rationalInterLeft d).spectrumMap.continuous

/-- The actual total spectrum-cover maps commute over the rational locus
inclusion; no component spectrum is replaced by its locus. -/
theorem rationalInter_totalMap (c : FiniteCover U) (d : RationalChart K A) :
    (U.rationalInterLeft d).locusMap.comp (c.rationalInter d).totalMap =
      c.totalMap.comp (c.rationalInterSpectrumMap d) := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum ((c.rationalInter d).obj x.1).algebra, U.locus) =>
      g x.2)
    (c.rationalInter_componentMap d x.1)

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
