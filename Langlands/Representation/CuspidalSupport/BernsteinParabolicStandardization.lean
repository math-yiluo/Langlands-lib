import Langlands.Representation.Jacquet.StandardBernsteinFixedVectorReduction
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerReduction

/-! # Standard Bernstein families through a specified rational parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

open RepresentedParabolic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G P M N : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance parabolicStandardizationAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance parabolicStandardizationAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

/-- A standard family in which the specified parabolic, Levi and radical have
standard images on every test scheme. -/
structure BernsteinParabolicPresentation (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) where
  torus : CommGroupScheme (Spec (CommRingCat.of F))
  inclusion : torus.toGrp ⟶ G
  cocharacter : cocharacterLattice torus
  family : BernsteinStandardFamily inclusion cocharacter
  roots : Finset (SimpleRoot inclusion cocharacter)
  parabolic_eq : SubgroupFunctor.range p =
    standardParabolic inclusion cocharacter (rootSet inclusion cocharacter roots)
  levi_eq : SubgroupFunctor.range (l ≫ p) =
    standardLevi inclusion cocharacter (rootSet inclusion cocharacter roots)
  radical_eq : SubgroupFunctor.range (r ≫ p) =
    standardUnipotent inclusion cocharacter (rootSet inclusion cocharacter roots)

/-- The specified parabolic and Levi are put into standard position by the
choice of family. The radical then has the standard unipotent range. -/
theorem exists_bernsteinParabolicPresentation
    (hG : IsConnectedReductive G) (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    Nonempty (BernsteinParabolicPresentation p l r) := by
  classical
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  obtain ⟨A, a, ha⟩ := exists_isSplitComponent M
  obtain ⟨D⟩ := parabolicRootPresentationExistence F G hG P M A p l a hp hl ha
  let d := D.data
  let hd := D.isCompatible
  let family := Jacquet.standardBernsteinFamily d.i d.ν hG hd.maximalSplit hd.generic
  let := family.finiteSimpleRoots
  let := Fintype.ofFinite (SimpleRoot d.i d.ν)
  let I : Finset (SimpleRoot d.i d.ν) := Finset.univ.filter fun α => α.val ∈ d.J
  have hI : rootSet d.i d.ν I = d.J := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      exact (Finset.mem_filter.mp hβ).2
    · intro hα
      exact ⟨⟨α, hd.subset_simpleRoots hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩
  obtain ⟨ζ, hζ, hP, _⟩ := hd.realization
  have hU := (standardCocharacter F G hG d.T d.i hd.maximalSplit d.ν hd.generic
    d.J hd.subset_simpleRoots).2 ζ hζ
  have hrad := radical_range_eq_dynamic_unipotent hG hp hr
    (CommGroupScheme.groupHom ζ ≫ d.i) hP
  refine ⟨⟨d.T, d.i, d.ν, family, I, ?_, ?_, ?_⟩⟩
  · rw [hI]
    exact hd.parabolic_eq
  · rw [hI]
    exact hd.levi_eq
  · rw [hI, hrad]
    exact hU.2.2.symm

/-- Existence of a standard Bernstein family through any specified actual
parabolic, Levi and geometric radical over a nonarchimedean local field. -/
def BernsteinParabolicPresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    ∀ (P M N : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
        LeviSubgroup.IsGeometricUnipotentRadical r →
          Nonempty (BernsteinParabolicPresentation p l r)

/-- The standard presentation exists for every displayed actual triple. -/
theorem bernsteinParabolicPresentation : BernsteinParabolicPresentationStatement.{u} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  intro P M N p l r hp hl hr
  exact exists_bernsteinParabolicPresentation hG p l r hp hl hr

namespace BernsteinParabolicPresentation

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  (D : BernsteinParabolicPresentation p l r)

/-- The Levi point group is identified with the literal standard Levi. -/
def leviPoints (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    rationalPoints M ≃ₜ* levi D.inclusion D.cocharacter D.roots := by
  letI := leviPointTopology l hl
  exact (leviPointsEquiv p l hp hl).trans (subgroupCongrContinuous
    (congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) D.levi_eq))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The identification on points comes from the specified composite inclusion. -/
@[simp] theorem leviPoints_apply_coe
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (x : rationalPoints M) :
    (D.leviPoints hp hl x : rationalPoints G) = rationalPoints.map (l ≫ p) x := rfl

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction of every smooth representation agrees with induction
from the literal standard triple after transporting the Levi action. -/
def inductionObjIso [T2Space F]
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    (leviInductionFunctor p l r hp hr hl hmul).obj σ ≅
      (normalizedInductionFunctor (D.family.decomposition D.roots)
        (D.family.closedUnipotent D.roots)).obj
        (letI := leviPointTopology l hl; SmoothRep.pullback (D.leviPoints hp hl).symm σ) :=
  leviInductionObjIsoOfPointImages p l r hp hr hl hmul
    (D.family.decomposition D.roots) (D.family.closedUnipotent D.roots)
    (congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) D.parabolic_eq)
    (congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) D.levi_eq)
    (congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _))) D.radical_eq)
    (D.leviPoints hp hl) (D.leviPoints_apply_coe hp hl) σ

end BernsteinParabolicPresentation

end Langlands.CuspidalSupport
