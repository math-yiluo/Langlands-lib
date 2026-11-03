import Langlands.AlgebraicGeometry.ClosedFactorizationLocusStatement
import Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus
import Langlands.AlgebraicGeometry.AffineCoordinateBaseChange
import Langlands.AlgebraicGeometry.ClosedFactorizationBaseChange
import Langlands.AlgebraicGeometry.FullProductFactorizationOver
import Langlands.AlgebraicGeometry.ClosedSieveAffineTests
import Langlands.AlgebraicGeometry.Descent.AffineFpqcClosedLocusDescent
import Langlands.AlgebraicGeometry.FullProductFactorizationGluing

/-! # The universal closed-factorization locus -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof

/-- The affine-target case, with projectivity after a faithfully flat extension
and the universal property on every test scheme. -/
theorem affine {R : CommRingCat.{u}} (X Y : Over (Spec R))
    [IsAffine X.left] [IsAffine Y.left]
    (hX : HasFpqcProjectiveCoordinateModule X) {D : Over (Spec R)}
    (d : D ⟶ X ⊗ Y) [IsClosedImmersion d.left] :
    ∃ (Z : Over (Spec R)) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec R)) (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t := by
  obtain ⟨B, hB, hproj⟩ := hX
  let := hB
  let := hproj
  let f : Spec (CommRingCat.of B) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hf : Flat f ∧ Surjective f :=
    (flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hB)
  let := hf.1
  let := hf.2
  let X' := (Over.pullback f).obj X
  let Y' := (Over.pullback f).obj Y
  let d' := ClosedFactorizationBaseChange.baseChangedMap f d
  have : IsAffine X'.left := inferInstanceAs (IsAffine (pullback X.hom f))
  have : IsAffine Y'.left := inferInstanceAs (IsAffine (pullback Y.hom f))
  have : Module.Projective B (((algΓ (CommRingCat.of B)).obj X').unop) :=
    AffineCoordinateBaseChange.projective X B
  obtain ⟨Z', i', hi', h'⟩ :=
    AffineClosedFactorizationLocus.affine_closed_locus X' Y' d'
  let := hi'
  let E' := FullProductFactorization.sieve X'.hom Y'.hom d'.left
  have hE' : Scheme.fpqcTopology.IsClosed E' :=
    FullProductFactorization.fpqc_isClosed _ _ _
  have haff : ClosedSieveAffineTests.AffineTestRepresents E' i'.left := by
    intro T _ g
    let T' : Over (Spec (CommRingCat.of B)) := Over.mk (g ≫ Y'.hom)
    let t : T' ⟶ Y' := Over.homMk g
    have : IsAffine T'.left := inferInstanceAs (IsAffine T)
    calc
      (∃ k : T ⟶ Z'.left, k ≫ i'.left = g) ↔
          (∃ k : T' ⟶ Z', k ≫ i' = t) :=
        (FullProductFactorization.exists_over_lift_iff i' t).symm
      _ ↔ (∃ q : X' ⊗ T' ⟶ (Over.pullback f).obj D, q ≫ d' = X' ◁ t) := h' T' t
      _ ↔ E' g := (FullProductFactorization.mem_iff_over d' t).symm
  have hall := ClosedSieveAffineTests.allTests_of_affineTests Scheme.fpqcTopology
    Scheme.zariskiTopology_le_fpqcTopology E' hE' i'.left haff
  let E := FullProductFactorization.sieve X.hom Y.hom d.left
  have hE : Scheme.fpqcTopology.IsClosed E :=
    FullProductFactorization.fpqc_isClosed _ _ _
  let p : Y'.left ⟶ Y.left := pullback.fst Y.hom f
  have : Flat p := inferInstanceAs (Flat (pullback.fst Y.hom f))
  have : Surjective p := inferInstanceAs (Surjective (pullback.fst Y.hom f))
  obtain ⟨Z, i, hi, h⟩ := AffineFpqcClosedLocusDescent.affine E hE p (by
    refine ⟨Z'.left, i'.left, hi', ?_⟩
    intro T g
    let T' : Over (Spec (CommRingCat.of B)) := Over.mk (g ≫ Y'.hom)
    let t : T' ⟶ Y' := Over.homMk g
    calc
      (∃ k : T ⟶ Z'.left, k ≫ i'.left = g) ↔ E' g := hall T g
      _ ↔ (∃ q : X' ⊗ T' ⟶ (Over.pullback f).obj D, q ≫ d' = X' ◁ t) :=
        FullProductFactorization.mem_iff_over d' t
      _ ↔ (∃ q : X ⊗ (Over.map f).obj T' ⟶ D,
          q ≫ d = X ◁ ClosedFactorizationBaseChange.originalMap f t) :=
        ClosedFactorizationBaseChange.factors_iff f d t
      _ ↔ E (g ≫ p) :=
        (FullProductFactorization.mem_iff_over d
          (ClosedFactorizationBaseChange.originalMap f t)).symm)
  let Z₀ : Over (Spec R) := Over.mk (i ≫ Y.hom)
  let i₀ : Z₀ ⟶ Y := Over.homMk i
  refine ⟨Z₀, i₀, hi, ?_⟩
  intro T t
  calc
    (∃ z : T ⟶ Z₀, z ≫ i₀ = t) ↔
        (∃ z : T.left ⟶ Z, z ≫ i = t.left) :=
      FullProductFactorization.exists_over_lift_iff i₀ t
    _ ↔ E t.left := h t.left
    _ ↔ _ := FullProductFactorization.mem_iff_over d t

/-- The exact universal closed-factorization statement. -/
theorem closedFactorizationLocus : ClosedFactorizationLocusStatement.{u} := by
  intro R X hAffine _hFlat hX
  let := hAffine
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have haff : FullProductFactorization.AffineTargetRepresentable X := by
    intro Y D _ d _
    obtain ⟨Z, i, hi, h⟩ := affine X Y hX d
    exact ⟨Z, i, hi, fun T _ t ↦ h T t⟩
  intro Y D d hd
  let := hd
  exact FullProductFactorization.of_affine_targets X haff Y D d

end Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
