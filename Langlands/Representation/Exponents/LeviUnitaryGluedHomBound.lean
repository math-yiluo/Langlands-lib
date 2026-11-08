import Langlands.Representation.Exponents.LeviUnitaryFiltration
import Langlands.Representation.Filtration.HomBounds

/-! Hom bounds on the actual unitary Jacquet module from a supplied gluing. -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- A finite sum of extended naturals, each at most one and with at most one
nonzero term, is at most one. -/
theorem sum_le_one_of_le_one_of_unique {n : ℕ} {f : Fin n → ℕ∞}
    (hone : ∀ i, f i ≤ 1) (huniq : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j) :
    ∑ i, f i ≤ 1 := by
  classical
  by_cases h : ∃ i₀, f i₀ ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h
    rw [Finset.sum_eq_single i₀
      (fun i _ hi => by_contra fun hne => hi (huniq i i₀ hne hi₀))
      (fun h => (h (Finset.mem_univ i₀)).elim)]
    exact hone i₀
  · simp only [not_exists, not_not] at h
    simp [h]

/-- An enumeration of double cosets has at most one index whose chosen
representative lies in the left subgroup. -/
theorem eq_of_doubleCoset_representative_mem {X : Type*} [Group X] {H K : Subgroup X}
    {m : ℕ} (c : Fin m ≃ DoubleCoset.Quotient (H : Set X) (K : Set X)) (z : Fin m → X)
    (hz : ∀ i, DoubleCoset.mk H K (z i) = c i) {i j : Fin m}
    (hi : z i ∈ H) (hj : z j ∈ H) : i = j := by
  have hone (x : X) (hx : x ∈ H) : DoubleCoset.mk H K x = DoubleCoset.mk H K 1 := by
    simpa using DoubleCoset.mk_mem_mul (K := K) ⟨x, hx⟩ (1 : X)
  apply c.injective
  rw [← hz i, ← hz j, hone _ hi, hone _ hj]

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N Q L U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance gluedHomAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {AL : CommGroupScheme (Spec (CommRingCat.of k))} {aL : AL.toGrp ⟶ L}
  (haL : IsSplitComponent aL) {n : ℕ} {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- The Hom lengths into a fixed target from the zero-real-part selected parts
of supplied pieces, all evaluated at one representation. -/
def selectedPieceHomLength :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    (Fin n → SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L)) →
      SmoothRep.{0, u, v} ℂ (rationalPoints M) →
      Representation ℂ (rationalPoints L) W → Fin n → ℕ∞ :=
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
  haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  fun pieces ρ τ i => HomSpace.length
    (selectedWeightPart ((pieces i).obj ρ).ρ (rationalPoints.map aL)
      haL.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart
        haL.isCentralSplitTorus.1.1 χ = 0)).toRepresentation τ

/-- If a supplied gluing has selected pieces with Hom length at most one and at
most one nonzero, then the actual unitary Jacquet module of induction has Hom
length at most one into the same target. -/
theorem leviUnitaryJacquetInductionHomLength_le_one_of_isGluedFrom :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    ∀ (pieces : Fin n →
        SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L))
      (_ : IsGluedFrom
        (leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) pieces)
      (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (_ : IsAdmissible
        ((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ)
      (τ : Representation ℂ (rationalPoints L) W),
      (∀ i, selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ i ≤ 1) →
      (∀ i j, selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ i ≠ 0 →
        selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ j ≠ 0 → i = j) →
      HomSpace.length (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)).representation τ ≤ 1 := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro pieces hglue ρ hρ τ hone huniq
  obtain ⟨s, e, hs⟩ := exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ haL pieces hglue ρ hρ
  let f := selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ
  calc HomSpace.length (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)).representation τ
      ≤ ∑ i, HomSpace.length (s.gradedRepresentation i).ρ τ := HomSpace.length_le_sum s τ
    _ = ∑ i, f (e i) :=
      Finset.sum_congr rfl fun i _ => HomSpace.length_congr_left τ (hs i).some
    _ = ∑ i, f i := Equiv.sum_comp e f
    _ ≤ 1 := sum_le_one_of_le_one_of_unique hone huniq

/-- The rank form of the preceding bound. -/
theorem leviUnitaryJacquetInductionHomRank_le_one_of_isGluedFrom :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    ∀ (pieces : Fin n →
        SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L))
      (_ : IsGluedFrom
        (leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) pieces)
      (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (_ : IsAdmissible
        ((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ)
      (τ : Representation ℂ (rationalPoints L) W),
      (∀ i, selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ i ≤ 1) →
      (∀ i j, selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ i ≠ 0 →
        selectedPieceHomLength l hl q lQ hq hlQ haL pieces ρ τ j ≠ 0 → i = j) →
      Module.rank ℂ ((leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
        ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)).representation.IntertwiningMap
          τ) ≤ 1 := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro pieces hglue ρ hρ τ hone huniq
  have h := leviUnitaryJacquetInductionHomLength_le_one_of_isGluedFrom
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ haL pieces hglue ρ hρ τ hone huniq
  rw [HomSpace.length, Module.length_eq_rank] at h
  exact Cardinal.toENat_le_one.mp h

/-- A geometric-lemma enumeration: if each selected piece has Hom length at
most one, and is nonzero only when its double-coset representative lies in the
inducing parabolic, the actual unitary Jacquet module of induction has Hom rank
at most one into the target. -/
theorem leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    ∀ {m : ℕ}
      (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
        (pointImage q : Set (rationalPoints G)))
      (z : Fin m → rationalPoints G),
      (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = c i) →
      ∀ (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
          q lQ rQ hq hrQ hlQ hmulQ (z i)),
        IsGluedFrom
          (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
          (fun i => (D i).pieceFunctor) →
      ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
        IsAdmissible
          ((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ →
      ∀ (τ : Representation ℂ (rationalPoints L) W),
        (∀ i, selectedPieceHomLength l hl q lQ hq hlQ haL
          (fun i => (D i).pieceFunctor) ρ τ i ≤ 1) →
        (∀ i, selectedPieceHomLength l hl q lQ hq hlQ haL
          (fun i => (D i).pieceFunctor) ρ τ i ≠ 0 → z i ∈ pointImage p) →
        Module.rank ℂ ((leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)).representation.IntertwiningMap
            τ) ≤ 1 := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro m c z hz D hglue ρ hρ τ hone hmem
  exact leviUnitaryJacquetInductionHomRank_le_one_of_isGluedFrom
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ haL _ hglue ρ hρ τ hone
    fun i j hi hj => eq_of_doubleCoset_representative_mem c z hz (hmem i hi) (hmem j hj)

end Langlands.Aubert.General.RepresentedParabolic
