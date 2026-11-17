import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralFamily
import Langlands.Representation.Plancherel.ProductInducedOrbitFullAction
import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual product action on full semistandard spectral families -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

namespace RationalSemistandard

variable {p : SemistandardSpectralIndex i} (m : LeviModel p)
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

/-- The existing actual coefficient action at every inducing representative. -/
def orbitRepresentation :
    Representation ℂ (rationalPoints G × rationalPoints G) (OrbitSections m pi) :=
  productInducedOrbitRepresentation (decomposition p) (isClosed_radical p)
    m.normCharacters pi

variable (d : CompactData p)

/-- Full-group stability uses the actual Laurent character coordinates and
the published compact-picture smoothness theorem. -/
theorem orbitRepresentation_smooth_mem
    (x : rationalPoints G × rationalPoints G) {q : OrbitSections m pi}
    (hq : q ∈ smoothOrbitSections m d pi) :
    orbitRepresentation m pi x q ∈ smoothOrbitSections m d pi := by
  have := (isClosed_parabolic p).locallyCompactSpace
  exact productInducedOrbitRepresentation_full_smooth_mem
    (decomposition p) (isClosed_radical p) m.normCharacters pi d.compact
    (isClosed_parabolic p) d.isCompact m.continuous_normCharacters
    d.projection_continuous d.factorization m.unitaryCoordinates.toMulEquiv
    m.unitaryCoordinates_hasLaurent x hq

/-- One open subgroup fixes the entire smooth component simultaneously at
every parameter and every inducing representative. -/
theorem smoothOrbitSections_isSmoothVector (q : smoothOrbitSections m d pi) :
    Langlands.IsSmoothVector (orbitRepresentation m pi) q.val := by
  have := (isClosed_parabolic p).locallyCompactSpace
  exact productInducedSmoothOrbitSections_isSmoothVector
    (decomposition p) (isClosed_radical p) m.normCharacters pi d.compact
    (isClosed_parabolic p) d.isCompact m.continuous_normCharacters
    d.projection_continuous d.factorization m.unitaryCoordinates.toMulEquiv q

end RationalSemistandard

open RationalSemistandard

section Families

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-- The full product action on the actual dependent product, before any
finite-support or Weyl-invariance condition. -/
def rationalSemistandardThetaRepresentation :
    Representation ℂ (rationalPoints G × rationalPoints G)
      (RationalSemistandardThetaSections.{u, uV} a ha mu) where
  toFun x :=
    { toFun := fun f t => orbitRepresentation (chosenLeviModel t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
        x (f t)
      map_add' := fun f g => funext fun t => map_add _ _ _
      map_smul' := fun c f => funext fun t => map_smul _ c _ }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext t
    exact congrArg (fun L => L (f t))
      (orbitRepresentation (chosenLeviModel t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)).map_one
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    funext t
    exact congrArg (fun L => L (f t))
      ((orbitRepresentation (chosenLeviModel t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)).map_mul x y)

@[simp] theorem rationalSemistandardThetaRepresentation_apply
    (x : rationalPoints G × rationalPoints G)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f t =
      orbitRepresentation (chosenLeviModel t.1)
        (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
        x (f t) := rfl

/-- The actual action preserves literal support exactly, since each component
operator is invertible with inverse the action of the inverse group element. -/
theorem rationalSemistandardThetaRepresentation_support
    (x : rationalPoints G × rationalPoints G)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu
        (rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f) =
      rationalSemistandardThetaSupport.{u, uV} a ha mu f := by
  ext t
  exact not_congr (map_eq_zero_iff _
    ((orbitRepresentation (chosenLeviModel t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)).apply_bijective x).injective)

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

/-- Full product-group stability of the already published smooth direct sum. -/
theorem rationalSemistandardThetaRepresentation_smooth_mem
    (x : rationalPoints G × rationalPoints G)
    {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f ∈
      rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d := by
  refine ⟨fun t => orbitRepresentation_smooth_mem _ _ (d t.1) x (hf.1 t), ?_⟩
  change (rationalSemistandardThetaSupport.{u, uV} a ha mu
    (rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f)).Finite
  rw [rationalSemistandardThetaRepresentation_support]
  exact hf.2

/-- The actual action restricted to coherent smooth finite-support families. -/
def rationalSemistandardThetaSmoothRepresentation :
    Representation ℂ (rationalPoints G × rationalPoints G)
      (rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :=
  (rationalSemistandardThetaRepresentation.{u, uV} a ha mu).subrepresentation
    (rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (fun x _ hf => rationalSemistandardThetaRepresentation_smooth_mem
      a ha mu d x hf)

@[simp] theorem rationalSemistandardThetaSmoothRepresentation_val
    (x : rationalPoints G × rationalPoints G)
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    (rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d x f).val =
      rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f.val := rfl

/-- Finite input support gives a single open stabilizer of the entire family
by finite intersection of the actual component stabilizers. -/
theorem rationalSemistandardThetaSmoothRepresentation_isSmooth :
    Langlands.IsSmooth
      (rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d) := by
  classical
  intro f
  have hcomponent : ∀ t : RationalSemistandardTheta.{u, uV} a ha mu,
      ∃ H : OpenSubgroup (rationalPoints G × rationalPoints G),
        ∀ x : H, orbitRepresentation (chosenLeviModel t.1)
          (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
          x (f.val t) = f.val t := by
    intro t
    exact smoothOrbitSections_isSmoothVector _ _ (d t.1)
      (rationalSemistandardThetaComponent.{u, uV} a ha mu d t f)
  choose H hH using hcomponent
  let s := f.property.2.toFinset
  refine ⟨s.inf H, ?_⟩
  intro x
  apply Subtype.ext
  funext t
  by_cases ht : t ∈ s
  · have hle : s.inf H ≤ H t := Finset.inf_le ht
    exact hH t ⟨x.val, hle x.property⟩
  · have hz : f.val t = 0 := by
      by_contra h
      exact ht (f.property.2.mem_toFinset.mpr h)
    change orbitRepresentation (chosenLeviModel t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
      x.val (f.val t) = f.val t
    rw [hz, map_zero]

/-- The full actual spectral direct sum in the canonical smooth category. -/
def rationalSemistandardThetaSmoothObject :
    SmoothRep ℂ (rationalPoints G × rationalPoints G) :=
  ⟨Rep.of (rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d),
    rationalSemistandardThetaSmoothRepresentation_isSmooth.{u, uV} a ha mu d⟩

end Families

end Langlands.HarishChandraSchwartz
