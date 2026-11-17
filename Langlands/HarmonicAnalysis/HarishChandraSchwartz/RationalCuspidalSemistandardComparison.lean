import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceStatements
import Langlands.GroupScheme.Rational.SemistandardSpectralIndex

/-! # Actual normalized constant terms on the full semistandard index

The full index is imported from the group-scheme construction. The two closed
analytic targets assert convergence and comparison with the standard kernel.
Neither the semistandard comparison nor source spectral coverage is proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section ActualConstantTerm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G}

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual indexed radical is closed in the canonical rational-point topology. -/
theorem isClosed_semistandardRadicalPoints (p : SemistandardSpectralIndex i) :
    IsClosed (p.radical.rationalPointSubgroup : Set (rationalPoints G)) := by
  obtain ⟨H, M, U, j, l, r, _, hj, _, _, _, hr, hU, _⟩ :=
    p.isParabolicWithLeviAndRadical
  have hc : IsClosedSubgroup (r ≫ j) := hr.1.comp hj.isClosedSubgroup
  have : IsClosedImmersion (r ≫ j).hom.hom.left := hc
  exact isClosed_rationalPoint_subgroup F p.radical (r ≫ j)
    ⟨Over.mono_of_mono_left _, hU⟩ hc

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The actual indexed Levi normalizes the indexed radical, by its all-test
Levi decomposition. -/
theorem semistandardLeviPoints_le_normalizer_radicalPoints
    (p : SemistandardSpectralIndex i) :
    p.levi.rationalPointSubgroup ≤
      Subgroup.normalizer (p.radical.rationalPointSubgroup : Set (rationalPoints G)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    p.isParabolicWithLeviAndRadical
  have hp := h (Over.mk (𝟙 (Spec (CommRingCat.of F))))
  exact hp.2.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hp.1).mp hp.2.2.1)

/-- The source normalizing character: the Haar modulus of Levi conjugation on
this actual semistandard radical. No character or analytic estimate is supplied. -/
def semistandardUnipotentModulus (p : SemistandardSpectralIndex i) :
    p.levi.rationalPointSubgroup →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter p.radical.rationalPointSubgroup
    (isClosed_semistandardRadicalPoints p) p.levi.rationalPointSubgroup
    (semistandardLeviPoints_le_normalizer_radicalPoints p)

/-- On an existing standard triple the normalizing character is exactly the
published standard one, with no change of measure. -/
@[simp] theorem semistandardUnipotentModulus_ofStandard
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    semistandardUnipotentModulus (SemistandardSpectralIndex.ofStandard hG hi ν hν J hJ) =
      standardUnipotentModulus i ν J := rfl

/-- The full-index source condition, using the actual normalized integral and
all group arguments. Properness is inequality with the whole group functor. -/
def RationalSemistandardConstantTermsVanish (f : rationalPoints G → ℂ) : Prop :=
  ∀ p : SemistandardSpectralIndex i, p.parabolic ≠ ⊤ →
  ∀ muU : Measure p.radical.rationalPointSubgroup, muU.IsHaarMeasure →
  ∀ g : rationalPoints G × rationalPoints G,
    constantTermInd muU (semistandardUnipotentModulus p) f g = 0

/-- The generic convergence-and-normalized-vanishing equivalence specializes
to each actual semistandard triple, independently of source index coverage. -/
theorem isIntegrableUnipotentCuspidal_iff_semistandardConstantTermInd
    (p : SemistandardSpectralIndex i) (muU : Measure p.radical.rationalPointSubgroup)
    (f : rationalPoints G → ℂ) :
    IsIntegrableUnipotentCuspidal muU f ↔
      (∀ x y : rationalPoints G,
        Integrable (fun v : p.radical.rationalPointSubgroup =>
          f (x * (v : rationalPoints G) * y)) muU) ∧
      ∀ g : rationalPoints G × rationalPoints G,
        constantTermInd muU (semistandardUnipotentModulus p) f g = 0 :=
  isIntegrableUnipotentCuspidal_iff_constantTermInd muU _ f

end ActualConstantTerm

/-- Absolute convergence on every proper member of the full actual index and
every two-sided translate, for every actual Schwartz function. -/
def RationalSchwartzSemistandardConstantTermConvergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (f : RationalSchwartzSpace hKc hPK ρ) (p : SemistandardSpectralIndex i),
      p.parabolic ≠ ⊤ →
    ∀ (muU : Measure p.radical.rationalPointSubgroup) [muU.IsHaarMeasure]
      (x y : rationalPoints G),
      Integrable (fun v : p.radical.rationalPointSubgroup =>
        f (x * (v : rationalPoints G) * y)) muU

/-- Exact comparison of the constructed integrable standard kernel with
normalized vanishing on the full intrinsic semistandard index. Neither
convergence nor conjugacy/coverage is a premise of this closed target. -/
def RationalCuspidalSemistandardComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ f : RationalSchwartzSpace hKc hPK ρ,
      f ∈ rationalCuspidalSubmodule hKc hPK ρ ↔
        RationalSemistandardConstantTermsVanish (i := i) f

end Langlands.HarishChandraSchwartz
