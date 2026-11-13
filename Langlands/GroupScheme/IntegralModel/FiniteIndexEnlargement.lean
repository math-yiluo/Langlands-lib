import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite-index enlargements of schematic integral-point subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M N : IntegralModel R K G) (j : M.Hom N (𝟙 G))
  (V : Subgroup (rationalPoints G))

/-- A smooth affine enlargement with the specified literal integral-point
subgroup, an open inclusion of the original model, and preservation of every
supplied representative of its relative identity component. -/
def IsOpenEnlargement : Prop :=
  N.IsSmooth ∧
    N.integralPoints = V ∧
    IsOpenImmersion j.hom.hom.hom.left ∧
    ∀ (C : GroupScheme (Spec (CommRingCat.of R))) (i : C ⟶ M.group),
      IsRelativeIdentityComponent M.group i →
        IsRelativeIdentityComponent N.group (i ≫ j.hom)

variable {M N j V}

/-- Compatibility of the generic identity gives the required inclusion of
literal integral-point subgroups for every open enlargement. -/
theorem IsOpenEnlargement.integralPoints_le
    (h : IsOpenEnlargement M N j V) : M.integralPoints ≤ V := by
  rw [← h.2.1]
  intro g hg
  have hi := j.map_mem_integralPoints hg
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hi

/-- For a smooth original model, the relative-component clause of an open
enlargement is not vacuous: the original model has an actual representing
open subgroup, and its composite with the enlargement morphism represents the
relative identity component of the enlargement. -/
theorem IsOpenEnlargement.exists_relativeIdentityComponent
    (h : IsOpenEnlargement M N j V) (hM : M.IsSmooth) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of R))) (i : C ⟶ M.group),
      IsRelativeIdentityComponent M.group i ∧
        IsRelativeIdentityComponent N.group (i ≫ j.hom) := by
  obtain ⟨C, i, hi, -, -⟩ :=
    RelativeIdentityComponent.smoothExistence _ M.group hM
  exact ⟨C, i, hi, h.2.2.2 C i hi⟩

/-- The finite-index part of KP Proposition A.7.1, specialized to a Henselian
DVR with algebraically closed residue field and existing smooth affine models.
The original point subgroup is normal and of finite index in the containing
subgroup. -/
def FiniteIndexEnlargementStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    Smooth G.X.hom →
    ∀ (M : IntegralModel R K G), M.IsSmooth →
      ∀ (V : Subgroup (rationalPoints G)), M.integralPoints ≤ V →
        (M.integralPoints.subgroupOf V).Normal →
        (M.integralPoints.subgroupOf V).FiniteIndex →
        ∃ (N : IntegralModel R K G) (j : M.Hom N (𝟙 G)),
          IsOpenEnlargement M N j V

end Langlands.GroupScheme.IntegralModel
