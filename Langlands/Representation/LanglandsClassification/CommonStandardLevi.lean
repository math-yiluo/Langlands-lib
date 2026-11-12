import Langlands.Representation.LanglandsClassification.LanglandsTriplet
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Comparing actual standard Levis with the same root index

This internal adapter assumes equality of the standard indices. It constructs
the inclusion-compatible scheme and topological point isomorphisms and expresses
the common-ambient-point conclusions using the resulting single group.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {T A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {J₁ J₂ : Set (characterLattice T)} {f₁ : A₁ ⟶ T} {f₂ : A₂ ⟶ T}
  {p₁ : P₁ ⟶ G} {l₁ : M₁ ⟶ P₁} {a₁ : A₁.toGrp ⟶ M₁}
  {p₂ : P₂ ⟶ G} {l₂ : M₂ ⟶ P₂} {a₂ : A₂.toGrp ⟶ M₂}

namespace ParabolicRootPresentationData.IsCompatible

variable
  (h₁ : (⟨T, i, ν, J₁, f₁⟩ : ParabolicRootPresentationData A₁ G).IsCompatible p₁ l₁ a₁)
  (h₂ : (⟨T, i, ν, J₂, f₂⟩ : ParabolicRootPresentationData A₂ G).IsCompatible p₂ l₂ a₂)
  (hJ : J₁ = J₂)

include h₁ h₂ hJ

/-- Equal indices in a fixed root presentation give equal Levi images on every
test scheme. -/
theorem levi_range_eq_of_index_eq :
    SubgroupFunctor.range (l₁ ≫ p₁) = SubgroupFunctor.range (l₂ ≫ p₂) := by
  rw [h₁.levi_eq, h₂.levi_eq, hJ]

/-- The actual source group schemes of the two standard Levis are isomorphic,
compatibly with their inclusions in the ambient group. -/
def commonLeviIso : M₁ ≅ M₂ :=
  (h₁.levi.isClosedSubgroup.comp h₁.parabolic.isClosedSubgroup).sourceIsoOfRangeEq
    (h₂.levi.isClosedSubgroup.comp h₂.parabolic.isClosedSubgroup)
    (h₁.levi_range_eq_of_index_eq h₂ hJ)

@[simp] theorem commonLeviIso_hom_comp :
    (h₁.commonLeviIso h₂ hJ).hom ≫ (l₂ ≫ p₂) = l₁ ≫ p₁ :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _

@[simp] theorem commonLeviIso_inv_comp :
    (h₁.commonLeviIso h₂ hJ).inv ≫ (l₁ ≫ p₁) = l₂ ≫ p₂ := by
  rw [← h₁.commonLeviIso_hom_comp h₂ hJ, Iso.inv_hom_id_assoc]

/-- The ambient inclusion determines the common-Levi comparison uniquely. -/
theorem commonLeviIso_hom_unique {q : M₁ ⟶ M₂}
    (hq : q ≫ (l₂ ≫ p₂) = l₁ ≫ p₁) :
    q = (h₁.commonLeviIso h₂ hJ).hom := by
  have hrep :=
    (h₂.levi.isClosedSubgroup.comp h₂.parabolic.isClosedSubgroup).isRepresentedBy_range
  apply hrep.hom_ext
  rw [hq, h₁.commonLeviIso_hom_comp h₂ hJ]

end ParabolicRootPresentationData.IsCompatible

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁)
  (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
  (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂)
  (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)

local instance commonLeviAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- Equal literal Levi images identify the two canonical topological groups.
The construction passes through their common subgroup of the ambient points. -/
def commonLeviPointsEquiv
    (hL : pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂)) :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    rationalPoints M₁ ≃ₜ* rationalPoints M₂ := by
  letI := leviPointTopology l₁ hl₁
  letI := leviPointTopology l₂ hl₂
  exact (leviPointsEquiv p₁ l₁ hp₁ hl₁).trans
    ((subgroupCongrContinuous hL).trans (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm)

variable (hL : pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂))

/-- The point comparison retains the original ambient maps. -/
theorem commonLeviPointsEquiv_ambient (m : rationalPoints M₁) :
    rationalPoints.map (l₁ ≫ p₁) m =
      rationalPoints.map (l₂ ≫ p₂)
        (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m) := by
  let := leviPointTopology l₁ hl₁
  let := leviPointTopology l₂ hl₂
  exact (congrArg Subtype.val ((leviPointsEquiv p₂ l₂ hp₂ hl₂).apply_symm_apply
    (subgroupCongrContinuous hL (leviPointsEquiv p₁ l₁ hp₁ hl₁ m)))).symm

/-- Two Levi points have the same ambient image exactly when they correspond
under the constructed topological group equivalence. -/
theorem commonLeviPointsEquiv_eq_iff (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂) :
    commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁ = m₂ ↔
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ := by
  let := leviPointTopology l₁ hl₁
  let := leviPointTopology l₂ hl₂
  constructor
  · intro h
    rw [← h]
    exact commonLeviPointsEquiv_ambient p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁
  · intro h
    apply (leviPointsEquiv p₂ l₂ hp₂ hl₂).injective
    apply Subtype.ext
    change rationalPoints.map (l₂ ≫ p₂)
      (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁) =
      rationalPoints.map (l₂ ≫ p₂) m₂
    rw [← commonLeviPointsEquiv_ambient p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL]
    exact h

/-- The norm comparison on common ambient points is precisely the norm comparison
after transporting the second character to the first Levi. -/
theorem commonLeviPoints_norm_iff
    (ψ₁ : rationalPoints M₁ →* ℂˣ) (ψ₂ : rationalPoints M₂ →* ℂˣ) :
    (∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ‖(ψ₁ m₁ : ℂ)‖ = ‖(ψ₂ m₂ : ℂ)‖) ↔
    (∀ m : rationalPoints M₁, ‖(ψ₁ m : ℂ)‖ =
      ‖(ψ₂ (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m) : ℂ)‖) := by
  constructor
  · intro h m
    exact h _ _ (commonLeviPointsEquiv_ambient p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m)
  · intro h m₁ m₂ hm
    rw [← (commonLeviPointsEquiv_eq_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁ m₂).mpr hm]
    exact h m₁

section Representations

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  (ρ₁ : Representation ℂ (rationalPoints M₁) V)
  (ρ₂ : Representation ℂ (rationalPoints M₂) W)

/-- The common-ambient-point action condition is ordinary intertwining after
transport of the second action to the first Levi group. -/
theorem commonLeviPoints_intertwines_iff (φ : V →ₗ[ℂ] W) :
    (∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) ↔
    (∀ (m : rationalPoints M₁) (x : V),
      φ (ρ₁ m x) = ρ₂
        (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m) (φ x)) := by
  constructor
  · intro h m x
    exact h _ _ (commonLeviPointsEquiv_ambient p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m) x
  · intro h m₁ m₂ hm x
    rw [← (commonLeviPointsEquiv_eq_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL m₁ m₂).mpr hm]
    exact h m₁ x

/-- A linear equivalence certified on common ambient points gives an actual
representation equivalence over the first Levi. -/
def commonLeviRepresentationEquiv (φ : V ≃ₗ[ℂ] W)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    Representation.Equiv ρ₁
      (ρ₂.comp (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL).toMonoidHom) :=
  Representation.Equiv.mk φ (fun m => by
    ext x
    exact (commonLeviPoints_intertwines_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
      ρ₁ ρ₂ φ.toLinearMap).mp hφ m x)

/-- The published common-point isomorphism condition is equivalent to nonempty
ordinary representation equivalence after transport. -/
theorem exists_commonLeviRepresentationEquiv_iff :
    (∃ φ : V ≃ₗ[ℂ] W,
      ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
        rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
          ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) ↔
    (letI := leviPointTopology l₁ hl₁
     letI := leviPointTopology l₂ hl₂
     Nonempty (Representation.Equiv ρ₁
       (ρ₂.comp (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL).toMonoidHom))) := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨commonLeviRepresentationEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL ρ₁ ρ₂ φ hφ⟩
  · rintro ⟨e⟩
    refine ⟨e.toLinearEquiv, ?_⟩
    apply (commonLeviPoints_intertwines_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
      ρ₁ ρ₂ e.toLinearEquiv.toLinearMap).mpr
    intro m x
    exact congrArg (fun f : V →ₗ[ℂ] W => f x) (e.isIntertwining' m)

end Representations

section Standard

variable {T A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {J₁ J₂ : Set (characterLattice T)} {f₁ : A₁ ⟶ T} {f₂ : A₂ ⟶ T}
  {a₁ : A₁.toGrp ⟶ M₁} {a₂ : A₂.toGrp ⟶ M₂}
  (h₁ : (⟨T, i, ν, J₁, f₁⟩ : ParabolicRootPresentationData A₁ G).IsCompatible p₁ l₁ a₁)
  (h₂ : (⟨T, i, ν, J₂, f₂⟩ : ParabolicRootPresentationData A₂ G).IsCompatible p₂ l₂ a₂)
  (hJ : J₁ = J₂)

omit [TopologicalSpace k] in
include h₁ h₂ hJ in
/-- Equal standard indices supply the literal common-image equality used by
the point and representation comparisons above. -/
theorem commonStandardLevi_pointImage_eq :
    pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂) := by
  rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier,
    h₁.levi_range_eq_of_index_eq h₂ hJ]

/-- Canonical point comparison for equal standard indices, with the original
canonical Levi topologies. -/
def commonStandardLeviPointsEquiv :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    rationalPoints M₁ ≃ₜ* rationalPoints M₂ :=
  commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂
    (commonStandardLevi_pointImage_eq p₁ l₁ p₂ l₂ h₁ h₂ hJ)

/-- The topological comparison is the rational-point map of the
inclusion-compatible isomorphism of the actual Levi schemes. -/
theorem commonStandardLeviPointsEquiv_eq_map (m : rationalPoints M₁) :
    commonStandardLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ h₁ h₂ hJ m =
      rationalPoints.map (h₁.commonLeviIso h₂ hJ).hom m := by
  apply (commonLeviPointsEquiv_eq_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂
    (commonStandardLevi_pointImage_eq p₁ l₁ p₂ l₂ h₁ h₂ hJ) m _).mpr
  change m ≫ (l₁ ≫ p₁).hom.hom =
    (m ≫ (h₁.commonLeviIso h₂ hJ).hom.hom.hom) ≫ (l₂ ≫ p₂).hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, h₁.commonLeviIso_hom_comp h₂ hJ]

end Standard

end Langlands.Aubert.General.RepresentedParabolic
