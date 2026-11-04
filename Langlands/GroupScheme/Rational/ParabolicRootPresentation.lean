import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RestrictedSimpleRootCones

/-! # Compatible root presentations of specified rational parabolics

The correctness predicate concerns actual subgroup maps on every test scheme.
Existence for all specified maps and independence of the torus and generic
cocharacter are separate structural obligations.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The actual choices used to present a parabolic and its Levi split component.
No compatibility or existence assertion is part of the underlying data. -/
structure ParabolicRootPresentationData
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  T : CommGroupScheme (Spec (CommRingCat.of k))
  i : T.toGrp ⟶ G
  ν : cocharacterLattice T
  J : Set (characterLattice T)
  f : A ⟶ T

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Compatibility with the specified actual parabolic, rational Levi and split
component. The generic dynamic minimal parabolic is required to be contained in
the supplied parabolic. A standard cocharacter realizes both supplied images,
so an empty intersection of standard cocharacters cannot supply a presentation. -/
structure ParabolicRootPresentationData.IsCompatible
    (d : ParabolicRootPresentationData A G) (p : P ⟶ G) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) : Prop where
  parabolic : IsParabolicSubgroup p
  levi : IsRationalLeviSubgroup l
  splitComponent : IsSplitComponent a
  maximalSplit : IsMaximalSplitTorus d.i
  generic : IsGenericCocharacter d.i d.ν
  subset_simpleRoots : d.J ⊆ simpleRelativeRoots d.i d.ν
  parabolic_eq : SubgroupFunctor.range p = standardParabolic d.i d.ν d.J
  levi_eq : SubgroupFunctor.range (l ≫ p) = standardLevi d.i d.ν d.J
  factor_comp : CommGroupScheme.groupHom d.f ≫ d.i = a ≫ l ≫ p
  minimal : IsMinimalParabolicFunctor
    (Dynamic.parabolic (CommGroupScheme.groupHom d.ν ≫ d.i))
  minimal_le : Dynamic.parabolic (CommGroupScheme.groupHom d.ν ≫ d.i) ≤
    SubgroupFunctor.range p
  realization : ∃ ζ : cocharacterLattice d.T, IsStandardCocharacter d.i d.ν d.J ζ ∧
    SubgroupFunctor.range p = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ d.i) ∧
    SubgroupFunctor.range (l ≫ p) =
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ d.i)

/-- Verified presentation data for the specified maps. This type can be empty;
no general presentation-existence theorem is asserted by the construction. -/
structure ParabolicRootPresentation (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) where
  data : ParabolicRootPresentationData A G
  isCompatible : data.IsCompatible p l a

namespace ParabolicRootPresentation

variable {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- The minimality field supplies an actual minimal parabolic representative,
and its all-test image is contained in that of the specified parabolic. -/
theorem exists_minimalParabolic :
    ∃ (P₀ : GroupScheme (Spec (CommRingCat.of k))) (p₀ : P₀ ⟶ G),
      IsMinimalParabolicSubgroup p₀ ∧
      SubgroupFunctor.range p₀ =
        Dynamic.parabolic (CommGroupScheme.groupHom r.data.ν ≫ r.data.i) ∧
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p := by
  obtain ⟨P₀, p₀, hp₀, heq⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp r.isCompatible.minimal
  exact ⟨P₀, p₀, hp₀, heq, heq ▸ r.isCompatible.minimal_le⟩

/-- In particular the index of the defining standard intersections is nonempty. -/
theorem exists_standardCocharacter :
    ∃ ζ : cocharacterLattice r.data.T, IsStandardCocharacter r.data.i r.data.ν r.data.J ζ := by
  obtain ⟨ζ, hζ, _, _⟩ := r.isCompatible.realization
  exact ⟨ζ, hζ⟩

/-- Membership in the supplied parabolic agrees with every standard dynamic
parabolic, on an arbitrary test scheme. -/
theorem mem_parabolic {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X} :
    g ∈ (SubgroupFunctor.range p).carrier U ↔
      ∀ ζ, IsStandardCocharacter r.data.i r.data.ν r.data.J ζ →
        g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ r.data.i)).carrier U := by
  rw [r.isCompatible.parabolic_eq]
  exact mem_standardParabolic r.data.i r.data.ν

/-- The same all-test membership comparison for the supplied Levi image. -/
theorem mem_levi {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X} :
    g ∈ (SubgroupFunctor.range (l ≫ p)).carrier U ↔
      ∀ ζ, IsStandardCocharacter r.data.i r.data.ν r.data.J ζ →
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ r.data.i)).carrier U := by
  rw [r.isCompatible.levi_eq]
  exact mem_standardLevi r.data.i r.data.ν

/-- The actual split-component factor is unique for the chosen torus inclusion. -/
theorem factor_unique (f' : A ⟶ r.data.T)
    (hf' : CommGroupScheme.groupHom f' ≫ r.data.i = a ≫ l ≫ p) :
    f' = r.data.f := by
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  exact eq_of_groupHom_comp_eq r.data.i (l ≫ p) hf' r.isCompatible.factor_comp

open RealTorusSpace

/-- The published restricted simple roots, attached to the verified presentation.
The ambient space is the full real character space of `A`. -/
abbrev restrictedRoots : Set (Vstar A) :=
  restrictedSimpleRoots r.data.i r.data.ν r.data.J r.data.f

theorem mem_restrictedRoots {x : Vstar A} :
    x ∈ r.restrictedRoots ↔
      ∃ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J ∧
        (1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ α) = x :=
  mem_restrictedSimpleRoots r.data.i r.data.ν r.data.J r.data.f

theorem restrictedRoots_eq_empty_iff :
    r.restrictedRoots = ∅ ↔ simpleRelativeRoots r.data.i r.data.ν ⊆ r.data.J :=
  restrictedSimpleRoots_eq_empty_iff r.data.i r.data.ν r.data.J r.data.f

section FiniteType

variable [LocallyOfFiniteType G.X.hom]

/-- Finiteness follows from the actual split-torus Lie weights. No separate
relative root-system, finiteness or characteristic premise is needed. -/
theorem finite_simpleRoots : (simpleRelativeRoots r.data.i r.data.ν).Finite :=
  r.isCompatible.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots
    r.data.i r.data.ν

theorem finite_restrictedRoots : r.restrictedRoots.Finite :=
  finite_restrictedSimpleRoots r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

/-- The strictly positive root-combination cone of the verified presentation. -/
def positiveCone : Set (Vstar A) :=
  restrictedRootPositiveCone r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

/-- The nonnegative root-combination cone of the verified presentation. -/
def nonnegCone : Set (Vstar A) :=
  restrictedRootNonnegCone r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

theorem mem_positiveCone {x : Vstar A} :
    x ∈ r.positiveCone ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ r.restrictedRoots, 0 < c β) ∧
        ∑ᶠ β ∈ r.restrictedRoots, c β • β = x :=
  mem_restrictedRootPositiveCone r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

theorem mem_nonnegCone {x : Vstar A} :
    x ∈ r.nonnegCone ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ r.restrictedRoots, 0 ≤ c β) ∧
        ∑ᶠ β ∈ r.restrictedRoots, c β • β = x :=
  mem_restrictedRootNonnegCone r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

/-- The empty complementary-root case has the empty sum as its only value. -/
theorem positiveCone_of_eq_empty
    (h : simpleRelativeRoots r.data.i r.data.ν \ r.data.J = ∅) :
    r.positiveCone = {0} :=
  restrictedPositiveCone_of_eq_empty
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots h

theorem nonnegCone_of_eq_empty
    (h : simpleRelativeRoots r.data.i r.data.ν \ r.data.J = ∅) :
    r.nonnegCone = {0} :=
  restrictedNonnegCone_of_eq_empty
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots h

theorem positiveCone_subset_nonnegCone : r.positiveCone ⊆ r.nonnegCone :=
  restrictedRootPositiveCone_subset_nonnegCone
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

theorem zero_mem_nonnegCone : (0 : Vstar A) ∈ r.nonnegCone :=
  zero_mem_restrictedRootNonnegCone r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots

theorem add_mem_nonnegCone {x y : Vstar A} (hx : x ∈ r.nonnegCone) (hy : y ∈ r.nonnegCone) :
    x + y ∈ r.nonnegCone :=
  add_mem_restrictedRootNonnegCone
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots hx hy

theorem smul_mem_nonnegCone {t : ℝ} (ht : 0 ≤ t) {x : Vstar A} (hx : x ∈ r.nonnegCone) :
    t • x ∈ r.nonnegCone :=
  smul_mem_restrictedRootNonnegCone
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots ht hx

theorem add_mem_positiveCone {x y : Vstar A}
    (hx : x ∈ r.positiveCone) (hy : y ∈ r.positiveCone) : x + y ∈ r.positiveCone :=
  add_mem_restrictedRootPositiveCone
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots hx hy

theorem smul_mem_positiveCone {t : ℝ} (ht : 0 < t) {x : Vstar A} (hx : x ∈ r.positiveCone) :
    t • x ∈ r.positiveCone :=
  smul_mem_restrictedRootPositiveCone
    r.data.i r.data.ν r.data.J r.data.f r.finite_simpleRoots ht hx

variable {A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a' : A'.toGrp ⟶ M}

/-- A compatible isomorphism of split-component presentations pulls back the
positive cones in both directions. The torus, generic cocharacter and index
remain fixed; this is not independence across different root presentations. -/
theorem image_positiveCone_splitComponentIso (e : A ≅ A')
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) {f' : A' ⟶ r.data.T}
    (hf' : CommGroupScheme.groupHom f' ≫ r.data.i = a' ≫ l ≫ p) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootPositiveCone r.data.i r.data.ν r.data.J f' r.finite_simpleRoots =
      r.positiveCone ∧
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) '' r.positiveCone =
      restrictedRootPositiveCone r.data.i r.data.ν r.data.J f' r.finite_simpleRoots := by
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  exact image_restrictedRootPositiveCone_splitComponentIso
    r.data.i r.data.ν r.data.J r.finite_simpleRoots (l ≫ p) e hea
    r.isCompatible.factor_comp hf'

/-- The corresponding nonnegative-cone comparison for a compatible split-component
isomorphism, again keeping the root presentation fixed. -/
theorem image_nonnegCone_splitComponentIso (e : A ≅ A')
    (hea : CommGroupScheme.groupHom e.hom ≫ a' = a) {f' : A' ⟶ r.data.T}
    (hf' : CommGroupScheme.groupHom f' ≫ r.data.i = a' ≫ l ≫ p) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootNonnegCone r.data.i r.data.ν r.data.J f' r.finite_simpleRoots =
      r.nonnegCone ∧
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) '' r.nonnegCone =
      restrictedRootNonnegCone r.data.i r.data.ν r.data.J f' r.finite_simpleRoots := by
  let := r.isCompatible.maximalSplit.isSplitSubtorus.mono
  exact image_restrictedRootNonnegCone_splitComponentIso
    r.data.i r.data.ν r.data.J r.finite_simpleRoots (l ≫ p) e hea
    r.isCompatible.factor_comp hf'

end FiniteType

end ParabolicRootPresentation

end Langlands.GroupScheme
