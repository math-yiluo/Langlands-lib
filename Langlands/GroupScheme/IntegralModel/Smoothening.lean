import Langlands.GroupScheme.IntegralModel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Smoothening of affine integral group models

The smoothening property of Kaletha–Prasad, Appendix A.6, for actual integral
group models, its elementary integral-point consequence, and the existence
target over a Henselian discrete valuation ring with algebraically closed
residue field. No existence proof is given here. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M N : IntegralModel R K G) (π : N.Hom M (𝟙 G))

/-- `π : N → M`, compatible with the identity of `G`, is a smoothening of `M`:
the actual structural morphism of `N.group` is smooth, `π` is bijective on actual
`R`-sections, and every homomorphism from a smooth group scheme over `Spec R`
to `M.group` factors through `π` by a unique homomorphism. -/
def IsSmoothening : Prop :=
  N.IsSmooth ∧
    Function.Bijective (rationalPoints.map π.hom) ∧
    ∀ (H : GroupScheme (Spec (CommRingCat.of R))), Smooth H.X.hom →
      ∀ f : H ⟶ M.group,
        ∃! f' : H ⟶ N.group, f' ≫ π.hom = f

/-- A generic-identity morphism surjective on integral sections preserves the
literal integral-point subgroup of the supplied generic group. -/
theorem integralPoints_eq_of_surjective_sections
    (hπ : Function.Surjective (rationalPoints.map π.hom)) :
    N.integralPoints = M.integralPoints := by
  ext g
  constructor
  · intro hg
    have h := π.map_mem_integralPoints hg
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hπ x
    refine ⟨y, ?_⟩
    have h := π.integralPointMap_naturality y
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h.symm

/-- Smoothening preserves the actual integral points, not merely an abstract
isomorphism class of groups. -/
theorem IsSmoothening.integralPoints_eq (hπ : IsSmoothening M N π) :
    N.integralPoints = M.integralPoints :=
  integralPoints_eq_of_surjective_sections M N π hπ.2.1.2

/-- Smoothening existence over a Henselian discrete valuation ring with
algebraically closed residue field: every affine flat finite-type integral model
of a smooth affine generic group has a smoothening. This is the strictly
Henselian perfect-residue specialization of KP Appendix A.6, where the source's
points over the maximal unramified integers are the actual `R`-sections. -/
def SmootheningStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    Smooth G.X.hom →
    ∀ M : IntegralModel R K G,
      ∃ (N : IntegralModel R K G) (π : N.Hom M (𝟙 G)), IsSmoothening M N π

end Langlands.GroupScheme.IntegralModel
