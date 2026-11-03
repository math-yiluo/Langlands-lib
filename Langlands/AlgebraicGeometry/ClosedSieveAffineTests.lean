import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof

/-! # Closed sieves and affine tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ClosedSieveAffineTests

/-- A morphism represents a sieve when tested on affine source schemes. -/
def AffineTestRepresents {Y Z : Scheme.{u}} (E : Sieve Y) (ι : Z ⟶ Y) : Prop :=
  ∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g

/-- Agreement on affine tests extends to all tests for a topology containing
Zariski covers, if both sides descend. -/
theorem allTests_of_affineTests (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hZar : Scheme.zariskiTopology ≤ J) {Y Z : Scheme.{u}} (E : Sieve Y)
    (hE : J.IsClosed E) (ι : Z ⟶ Y) [Mono ι] (h : AffineTestRepresents E ι) :
    ∀ (T : Scheme.{u}) (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  intro T g
  have hcov : Sieve.ofArrows T.affineCover.X T.affineCover.f ∈ J T :=
    hZar _ T.affineCover.mem_grothendieckTopology
  constructor
  · rintro ⟨k, hk⟩
    refine hE g (J.superset_covering ?_ hcov)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨a⟩
    exact (h _ _).1 ⟨T.affineCover.f a ≫ k, by rw [Category.assoc, hk]⟩
  · intro hg
    refine FppfClosedLocusDescent.exists_lift_of_covering J ι g _ hcov ?_
    rintro T' u ⟨V, m, _, ⟨a⟩, rfl⟩
    obtain ⟨k, hk⟩ := (h _ (T.affineCover.f a ≫ g)).2 (E.downward_closed hg _)
    exact ⟨m ≫ k, by simp [Category.assoc, hk]⟩

/-- A closed sieve admits a closed representative if it admits closed affine-test
representatives on all affine opens of its target. -/
theorem glue (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hZar : Scheme.zariskiTopology ≤ J) {Y : Scheme.{u}} (E : Sieve Y)
    (hE : J.IsClosed E)
    (hchart : ∀ U : Y.affineOpens, ∃ (Z : Scheme.{u}) (ι : Z ⟶ (U : Y.Opens).toScheme),
      IsClosedImmersion ι ∧ AffineTestRepresents (E.pullback (U : Y.Opens).ι) ι) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  refine closedLocusFromAffineCharts Y (fun _ g ↦ E g)
    (fun _ _ f g hg ↦ E.downward_closed hg f) (fun T g hg ↦ ?_) (fun U ↦ ?_)
  · refine hE g (J.superset_covering ?_
      (hZar _ (Precoverage.generate_mem_toGrothendieck (R := Presieve.ofArrows
        (fun V : Y.affineOpens ↦ (g ⁻¹ᵁ (V : Y.Opens)).toScheme)
        (fun V ↦ (g ⁻¹ᵁ (V : Y.Opens)).ι)) ?_)))
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨V⟩
      exact hg V
    · rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun t ↦ ?_, fun V ↦ inferInstance⟩
      obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset
        (show g t ∈ (⊤ : Y.Opens) from trivial)
      exact ⟨⟨V, hV⟩, ⟨t, hgV⟩, rfl⟩
  · obtain ⟨Z, ι, hι, h⟩ := hchart U
    letI := hι
    refine ⟨Z, ι, hι, fun T g ↦ ?_⟩
    exact allTests_of_affineTests J hZar (E.pullback (U : Y.Opens).ι)
      (J.isClosed_pullback _ _ hE) ι h T g

end Langlands.AlgebraicGeometry.ClosedSieveAffineTests
