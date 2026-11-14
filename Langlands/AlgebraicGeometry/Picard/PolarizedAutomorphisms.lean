import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison
import Mathlib.CategoryTheory.Endomorphism

/-! # Actual integral polarized automorphisms and their rationalization -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "dualA" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hA geometryA MA evaluationA

/-- The actual integral dual-pullback equation, with no abstract group supplied. -/
def IsPolarizationPreservingAut (lam : A ⟶ DA) (f : Aut A) : Prop :=
  f.hom ≫ lam ≫ dualA f.hom = lam

local notation "Preserves" => IsPolarizationPreservingAut preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA

/-- The subgroup of actual integral automorphisms preserving the given dual-valued map. -/
def polarizedAutGroup (lam : A ⟶ DA) : Subgroup (Aut A) where
  carrier := Preserves lam
  one_mem' := by
    change (𝟙 A) ≫ lam ≫ dualA (𝟙 A) = lam
    rw [dualAbelianSchemeMapFromEvaluation_id]
    simp
  mul_mem' := by
    intro f g hf hg
    change (g.hom ≫ f.hom) ≫ lam ≫ dualA (g.hom ≫ f.hom) = lam
    rw [dualAbelianSchemeMapFromEvaluation_comp (hB := hA) (geometryB := geometryA)
      (MB := MA) (evaluationB := evaluationA)]
    change f.hom ≫ lam ≫ dualA f.hom = lam at hf
    change g.hom ≫ lam ≫ dualA g.hom = lam at hg
    calc
      _ = g.hom ≫ (f.hom ≫ lam ≫ dualA f.hom) ≫ dualA g.hom := by
        simp only [Category.assoc]
      _ = lam := by rw [hf]; exact hg
  inv_mem' := by
    intro f hf
    change f.inv ≫ lam ≫ dualA f.inv = lam
    change f.hom ≫ lam ≫ dualA f.hom = lam at hf
    have hdual : dualA f.hom ≫ dualA f.inv = 𝟙 DA := by
      rw [← dualAbelianSchemeMapFromEvaluation_comp (hB := hA) (geometryB := geometryA)
        (MB := MA) (evaluationB := evaluationA), f.inv_hom_id,
        dualAbelianSchemeMapFromEvaluation_id]
    calc
      _ = f.inv ≫ (f.hom ≫ lam ≫ dualA f.hom) ≫ dualA f.inv := by rw [hf]
      _ = lam := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hdual, Category.comp_id]

local notation "AutLam" => polarizedAutGroup preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA

/-- Membership is exactly the actual dual-pullback equation. -/
@[simp] lemma mem_polarizedAutGroup_iff (lam : A ⟶ DA) (f : Aut A) :
    f ∈ AutLam lam ↔ f.hom ≫ lam ≫ dualA f.hom = lam := Iff.rfl

/-- An integral polarized automorphism determines its actual rational self-isogeny. -/
def polarizedAutRationalization (lam : A ⟶ DA) :
    AutLam lam →* Aut (Langlands.Rationalization.of A) :=
  (Functor.mapAut A (rationalization S)).comp (AutLam lam).subtype

/-- The bridge uses the canonical rationalization of the original integral homomorphism. -/
@[simp] lemma polarizedAutRationalization_hom (lam : A ⟶ DA) (f : AutLam lam) :
    (polarizedAutRationalization preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA lam f).hom =
        homToHom0 f.val.hom := rfl

/-- Its inverse is the canonical rationalization of the original integral inverse. -/
@[simp] lemma polarizedAutRationalization_inv (lam : A ⟶ DA) (f : AutLam lam) :
    (polarizedAutRationalization preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA lam f).inv =
        homToHom0 f.val.inv := rfl

variable (additivity : DualSchemeMapAdditivity preservation stability A A hA hA)

/-- Rationalizing the integral equation gives the same actual rational dual-pullback equation. -/
theorem polarizedAutRationalization_preserves (lam : A ⟶ DA) (f : AutLam lam) :
    rationalDualPullbackHom0 preservation composition unitCoherence associativity comparison
      symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA additivity
      (polarizedAutRationalization preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam f).hom
      (homToHom0 lam) = homToHom0 lam := by
  rw [polarizedAutRationalization_hom, rationalDualPullbackHom0_homToHom0]
  exact congrArg homToHom0 f.property

/-- The rational self-isogeny has multiplier one in the existing rational-Hom interface. -/
theorem polarizedAutRationalization_multiplier_one (lam : A ⟶ DA) (f : AutLam lam) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA
      additivity 1
      (polarizedAutRationalization preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam f).hom
      (homToHom0 lam) (homToHom0 lam) := by
  simpa only [IsRationalDualPullbackMultiple, one_smul] using
    polarizedAutRationalization_preserves preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA additivity lam f

end Langlands.AbelianScheme
