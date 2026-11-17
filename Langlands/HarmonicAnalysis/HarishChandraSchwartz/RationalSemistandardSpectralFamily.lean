import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FiniteSupportSections

/-! # Full actual semistandard spectral families -/

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

open RationalSemistandard

section Families

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-- Waldspurger's full actual `Theta`: a semistandard triple and a unitary
unramified orbit of its literal Levi's discrete series modulo its split center.
The chosen representing model is fixed by the intrinsic index, not index data. -/
abbrev RationalSemistandardTheta : Type _ :=
  Σ p : SemistandardSpectralIndex i, OrbitClass.{u, uV} (p := p) (chosenLeviModel p) (a p) (ha p) (mu p)

/-- The actual normalized product-induced section space at one full index. -/
abbrev RationalSemistandardThetaSection (t : RationalSemistandardTheta.{u, uV} a ha mu) : Type _ :=
  OrbitSections (p := t.1) (chosenLeviModel t.1)
    (orbitRepresentative.{u, uV} (p := t.1) (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)

/-- The dependent product of all actual coefficient section spaces. -/
abbrev RationalSemistandardThetaSections : Type _ :=
  ∀ t : RationalSemistandardTheta.{u, uV} a ha mu, RationalSemistandardThetaSection.{u, uV} a ha mu t

/-- Literal support in the full `(P,O)` index, before any Weyl quotient. -/
def rationalSemistandardThetaSupport (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    Set (RationalSemistandardTheta.{u, uV} a ha mu) := FiniteSupportSections.support f

@[simp] theorem mem_rationalSemistandardThetaSupport
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    t ∈ rationalSemistandardThetaSupport.{u, uV} a ha mu f ↔ f t ≠ 0 := Iff.rfl

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

/-- The coherent smooth submodule at one actual index, retaining all inducing
equivalence and self-twist covariance from the published section construction. -/
def rationalSemistandardThetaComponentSpace (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    Submodule ℂ (RationalSemistandardThetaSection.{u, uV} a ha mu t) := by
  let W := smoothOrbitSections.{u, uV} (p := t.1) (chosenLeviModel t.1) (d t.1)
    (orbitRepresentative.{u, uV} (p := t.1) (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
  exact W

/-- Waldspurger VI.3's direct sum `C^infinity(Theta)`: smooth coherent
components and finite support are defining properties of an input family. -/
def rationalSemistandardThetaSmoothSections :
    Submodule ℂ (RationalSemistandardThetaSections.{u, uV} a ha mu) :=
  FiniteSupportSections.submodule (rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d)

@[simp] theorem mem_rationalSemistandardThetaSmoothSections
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d ↔
      (∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
        (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite := Iff.rfl

/-- Linear evaluation into the actual smooth component. -/
def rationalSemistandardThetaComponent (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t :=
  FiniteSupportSections.component _ t

/-- Extend one actual smooth component by zero at every other `(P,O)`. -/
def rationalSemistandardThetaSingle (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d :=
  FiniteSupportSections.single _ t

@[simp] theorem rationalSemistandardThetaComponent_val
    (t : RationalSemistandardTheta.{u, uV} a ha mu)
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    (rationalSemistandardThetaComponent.{u, uV} a ha mu d t f).val = f.val t := rfl

@[simp] theorem rationalSemistandardThetaComponent_single
    (t : RationalSemistandardTheta.{u, uV} a ha mu)
    (v : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) :
    rationalSemistandardThetaComponent.{u, uV} a ha mu d t
      (rationalSemistandardThetaSingle.{u, uV} a ha mu d t v) = v :=
  FiniteSupportSections.component_single_same _ t v

theorem rationalSemistandardThetaComponent_single_ne
    {s t : RationalSemistandardTheta.{u, uV} a ha mu} (h : s ≠ t)
    (v : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) :
    rationalSemistandardThetaComponent.{u, uV} a ha mu d s
      (rationalSemistandardThetaSingle.{u, uV} a ha mu d t v) = 0 :=
  FiniteSupportSections.component_single_ne _ h v

theorem rationalSemistandardThetaSupport_single_subset
    (t : RationalSemistandardTheta.{u, uV} a ha mu)
    (v : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu
      (rationalSemistandardThetaSingle.{u, uV} a ha mu d t v).val ⊆ {t} :=
  FiniteSupportSections.support_single_subset _ t v

@[ext] theorem rationalSemistandardThetaSmoothSections_ext
    {f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d}
    (h : ∀ t, rationalSemistandardThetaComponent.{u, uV} a ha mu d t f =
      rationalSemistandardThetaComponent.{u, uV} a ha mu d t g) : f = g :=
  FiniteSupportSections.ext _ h

@[simp] theorem rationalSemistandardThetaSupport_zero :
    rationalSemistandardThetaSupport.{u, uV} a ha mu
      (0 : RationalSemistandardThetaSections.{u, uV} a ha mu) = ∅ :=
  FiniteSupportSections.support_zero

theorem rationalSemistandardThetaSupport_add_subset
    (f g : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu (f + g) ⊆
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ∪ rationalSemistandardThetaSupport.{u, uV} a ha mu g :=
  FiniteSupportSections.support_add_subset f g

theorem rationalSemistandardThetaSupport_smul_subset
    (c : ℂ) (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu (c • f) ⊆
      rationalSemistandardThetaSupport.{u, uV} a ha mu f :=
  FiniteSupportSections.support_smul_subset c f

section StandardRestriction

variable {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)

/-- The standard slice retains the canonical full-family model, split center
and Haar data, and only restricts the parabolic index. -/
abbrev RationalSemistandardStandardTheta : Type _ :=
  Σ I : Finset (RationalPointFamily.SimpleRoot i nu),
    OrbitClass.{u, uV} (p := standardIndex hG hi hnu I)
      (chosenLeviModel (standardIndex hG hi hnu I))
      (a (standardIndex hG hi hnu I)) (ha (standardIndex hG hi hnu I))
      (mu (standardIndex hG hi hnu I))

/-- The actual standard-index map into the full, unquotiented `Theta`. -/
def rationalSemistandardStandardIndex
    (t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu) :
    RationalSemistandardTheta.{u, uV} a ha mu :=
  ⟨standardIndex hG hi hnu t.1, t.2⟩

/-- Finite root-subset presentations give finite fibers. No injectivity of
standard presentations or geometric finiteness of all parabolics is assumed. -/
theorem rationalSemistandardStandardIndex_finite_fibers
    (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    ((rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu) ⁻¹' {t}).Finite := by
  have := finite_simpleRoot hG hi hnu
  let X := ↥((rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu) ⁻¹' {t})
  have hinj : Function.Injective (fun s : X => s.val.1) := by
    rintro ⟨⟨I, O⟩, hx⟩ ⟨⟨J, Q⟩, hy⟩ h
    change rationalSemistandardStandardIndex a ha mu hG hi hnu ⟨I, O⟩ = t at hx
    change rationalSemistandardStandardIndex a ha mu hG hi hnu ⟨J, Q⟩ = t at hy
    change I = J at h
    subst J
    have hO : O = Q := eq_of_heq (Sigma.mk.inj_iff.mp (hx.trans hy.symm)).2
    apply Subtype.ext
    cases hO
    rfl
  have : Finite X := Finite.of_injective _ hinj
  exact Set.toFinite _

/-- Restrict raw full families to their actual standard indices. -/
def rationalSemistandardStandardRestrict :
    RationalSemistandardThetaSections.{u, uV} a ha mu →ₗ[ℂ]
      ∀ t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu,
        RationalSemistandardThetaSection.{u, uV} a ha mu
          (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t) :=
  FiniteSupportSections.restrict (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu)

/-- Restrict finitely supported smooth full families to the standard slice. -/
def rationalSemistandardStandardSmoothRestrict :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      FiniteSupportSections.submodule (fun t =>
        rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
          (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t)) :=
  FiniteSupportSections.restrictFiniteFibers
    (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu) _
    (rationalSemistandardStandardIndex_finite_fibers.{u, uV} a ha mu hG hi hnu)

@[simp] theorem rationalSemistandardStandardRestrict_apply
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu) :
    rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu f t =
      f (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t) := rfl

@[simp] theorem rationalSemistandardStandardSmoothRestrict_val
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu) :
    (rationalSemistandardStandardSmoothRestrict.{u, uV} a ha mu d hG hi hnu f).val t =
      f.val (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t) := rfl

theorem rationalSemistandardStandardRestrict_support
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    FiniteSupportSections.support
      (rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu f) =
      (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu) ⁻¹'
        rationalSemistandardThetaSupport.{u, uV} a ha mu f := rfl

end StandardRestriction
end Families

end Langlands.HarishChandraSchwartz
