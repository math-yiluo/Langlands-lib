import Langlands.Geometry.Building.RealTorusSpace
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-! # Character-normalized centralizer valuations and dominant sets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual restriction of a rational character of `Z` along `s : S → Z`,
viewed in the actual character lattice of `S`. -/
def characterRestriction (s : S.toGrp ⟶ Z) :
    rationalCharacters Z →+ characterLattice S :=
  (rationalCharacters.equivCharacterLattice S).toAddMonoidHom.comp (characterRestrict s)

/-- Evaluation of actual restricted characters on the real cocharacter space.
Bijectivity of this map is an explicit structural comparison, not part of its definition. -/
def restrictionEvaluation (s : S.toGrp ⟶ Z) :
    RealTorusSpace.V S →ₗ[ℝ] (rationalCharacters Z →+ ℝ) where
  toFun v :=
    { toFun := fun χ => RealTorusSpace.eval S (characterRestriction s χ) v
      map_zero' := by simp [RealTorusSpace.eval_eq_pair]
      map_add' := by
        intro χ ψ
        simp [RealTorusSpace.eval_eq_pair, TensorProduct.tmul_add] }
  map_add' v w := by
    ext χ
    change RealTorusSpace.eval S (characterRestriction s χ) (v + w) = _
    exact (RealTorusSpace.eval S (characterRestriction s χ)).map_add v w
  map_smul' r v := by
    ext χ
    change RealTorusSpace.eval S (characterRestriction s χ) (r • v) =
      r • RealTorusSpace.eval S (characterRestriction s χ) v
    exact (RealTorusSpace.eval S (characterRestriction s χ)).map_smul r v

@[simp] theorem restrictionEvaluation_apply (s : S.toGrp ⟶ Z)
    (v : RealTorusSpace.V S) (χ : rationalCharacters Z) :
    restrictionEvaluation s v χ = RealTorusSpace.eval S (characterRestriction s χ) v := rfl

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The source-positive valuation on the actual `Z(F)`, transported into `V(S)`
through the actual restriction-evaluation map. Its sole comparison hypothesis
is the displayed bijectivity, with no building or Cartan conclusion included. -/
def centralizerValuation (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    rationalPoints Z →* Multiplicative (RealTorusSpace.V S) :=
  (AddMonoidHom.toMultiplicative
    (LinearEquiv.ofBijective (restrictionEvaluation s) h).symm.toAddMonoidHom).comp
      (rationalNormLogarithm Z)

/-- The positive character-valuation normalization uniquely specifies the transported map. -/
theorem centralizerValuation_spec (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (z : rationalPoints Z)
    (χ : rationalCharacters Z) :
    RealTorusSpace.eval S (characterRestriction s χ) (centralizerValuation s h z).toAdd =
      ((rationalCharacterValuation Z z).toAdd χ : ℝ) := by
  have he := (LinearEquiv.ofBijective (restrictionEvaluation s) h).apply_symm_apply
    (rationalNormLogarithm Z z).toAdd
  have hc := DFunLike.congr_fun he χ
  change RealTorusSpace.eval S (characterRestriction s χ)
    (centralizerValuation s h z).toAdd = _ at hc
  exact hc.trans (rationalNormLogarithm_eq_intValuation Z z χ)

/-- The normalization determines the value at every actual centralizer point uniquely. -/
theorem eq_centralizerValuation_iff (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (z : rationalPoints Z)
    (v : RealTorusSpace.V S) :
    v = (centralizerValuation s h z).toAdd ↔
      ∀ χ : rationalCharacters Z,
        RealTorusSpace.eval S (characterRestriction s χ) v =
          ((rationalCharacterValuation Z z).toAdd χ : ℝ) := by
  constructor
  · rintro rfl χ
    exact centralizerValuation_spec s h z χ
  · intro hv
    apply h.injective
    ext χ
    exact (hv χ).trans (centralizerValuation_spec s h z χ).symm

/-- The actual valuation image in `V(S)`. No identification with the full cocharacter
lattice, rank, discreteness or index assertion is implicit. -/
def centralizerValuationImage (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    Subgroup (Multiplicative (RealTorusSpace.V S)) :=
  (centralizerValuation s h).range

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- KP's corrected dominant centralizer set, for the positive relative roots selected
by the actual generic cocharacter `ν`. The inequality is nonnegative for positive order. -/
def dominantCentralizer (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :
    Set (rationalPoints Z) :=
  {z | ∀ α ∈ positiveRelativeRoots i ν,
    0 ≤ RealTorusSpace.eval S α (centralizerValuation s h z).toAdd}

/-- The chamber in the actual valuation image, rather than in an assumed full
integral cocharacter lattice. -/
def dominantValuationImage (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s)) :
    Set (centralizerValuationImage s h) :=
  {v | ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ RealTorusSpace.eval S α v.1.toAdd}

end Langlands.BruhatTits.Cartan
