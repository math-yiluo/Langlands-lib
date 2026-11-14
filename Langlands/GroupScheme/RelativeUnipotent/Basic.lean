import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Relative vector-bundle additive groups and finite normal series

The bundle data are actual sheaves of modules with finite local bases. Their
pullbacks, rather than arbitrary local additive-group charts, control the points
of the represented additive group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeUnipotent

open Langlands.SchemeModule

variable {S : Scheme.{u}}

/-- An actual module sheaf with finite local bases. Their sizes may vary over
the base, and the covering family need not be finite. -/
def IsFiniteLocallyFree (M : S.Modules) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ q.IsFiniteType

/-- Pull back a bundle section along a morphism of test schemes, using the
canonical composition and equal-morphism comparisons for module pullback. -/
def sectionPullback (M : S.Modules) {T T' : Over S} (b : T' ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    GlobalSections ((Scheme.Modules.pullback T'.hom).obj M) :=
  (((Scheme.Modules.pullbackComp b.left T.hom).hom.app M) ≫
    ((Scheme.Modules.pullbackCongr (Over.w b)).hom.app M)).app ⊤
      (pullbackSection b.left ((Scheme.Modules.pullback T.hom).obj M) s)

/-- The actual smooth affine additive group of a finite locally free module.
The all-test identifications are natural for the canonical pullback of sections
of one fixed module sheaf, so their local transition maps are linear.
Affineness and smoothness are recorded explicitly for consumers of the series. -/
def IsVectorBundleAdditive (V : GroupScheme S) : Prop :=
  IsAffineHom V.X.hom ∧ Smooth V.X.hom ∧
    ∃ M : S.Modules, IsFiniteLocallyFree M ∧
      ∃ e : ∀ T : Over S, (T ⟶ V.X) ≃*
          Multiplicative (GlobalSections ((Scheme.Modules.pullback T.hom).obj M)),
        ∀ (T T' : Over S) (b : T' ⟶ T) (x : T ⟶ V.X),
          (e T' (b ≫ x)).toAdd = sectionPullback M b (e T x).toAdd

/-- A descending finite normal series on actual group schemes, with smooth
closed kernels, represented fppf quotient homomorphisms, and vector-bundle
additive successive quotients. The terminal group is trivial on every test.
This predicate includes no cocycle or torsor vanishing assertion. -/
def HasVectorBundleSeries : ℕ → GroupScheme S → Prop
  | 0, H => SubgroupFunctor.range (𝟙 H) = ⊥
  | n + 1, H => ∃ (K V : GroupScheme S) (j : K ⟶ H) (q : H ⟶ V),
      IsClosedSubgroup j ∧ Smooth K.X.hom ∧
        (SubgroupFunctor.range j).IsNormal ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q ∧
        IsVectorBundleAdditive V ∧ HasVectorBundleSeries n K

/-- Existence of a finite vector-bundle normal series, with no chosen length. -/
def HasFiniteVectorBundleSeries (H : GroupScheme S) : Prop :=
  ∃ n : ℕ, HasVectorBundleSeries n H

end Langlands.GroupScheme.RelativeUnipotent
