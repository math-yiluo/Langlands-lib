import Langlands.AbelianScheme.FiberwiseIsogenyStatement
import Langlands.AlgebraicGeometry.FiberwiseFlatness
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Fibrewise detection of isogenies between smooth proper group schemes -/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- The fibre map commutes with the projections to the total spaces. -/
lemma fiberMap_fst {X Y : Over S} (f : X ⟶ Y) (s : S) :
    ((Over.pullback (S.fromSpecResidueField s)).map f).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f.left :=
  pullback.lift_fst _ _ _

/-- Every point of `X` lying over `s` comes from the residue-field fibre over `s`. -/
lemma exists_fst_eq {X : Over S} (x : X.left) {s : S} (hx : X.hom x = s) :
    ∃ x' : ((Over.pullback (S.fromSpecResidueField s)).obj X).left,
      pullback.fst X.hom (S.fromSpecResidueField s) x' = x := by
  have : x ∈ Set.range (pullback.fst X.hom (S.fromSpecResidueField s)) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hx
  exact this

lemma fst_injective (X : Over S) (s : S) :
    Function.Injective (pullback.fst X.hom (S.fromSpecResidueField s)) :=
  (pullback.fst X.hom (S.fromSpecResidueField s)).isEmbedding.injective

/-- A morphism over `S` is surjective if all of its residue-field fibres are. -/
theorem surjective_of_fiber {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ s : S, Surjective ((Over.pullback (S.fromSpecResidueField s)).map f).left) :
    Surjective f.left := by
  refine ⟨fun y => ?_⟩
  obtain ⟨y', hy'⟩ := exists_fst_eq y rfl
  obtain ⟨x', hx'⟩ := (h (Y.hom y)).surj y'
  refine ⟨pullback.fst X.hom (S.fromSpecResidueField (Y.hom y)) x', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← fiberMap_fst, Scheme.Hom.comp_apply, hx', hy']

/-- A morphism over `S` has finite fibres if all of its residue-field fibres do. -/
theorem finite_preimage_singleton_of_fiber {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (s : S) (y : ((Over.pullback (S.fromSpecResidueField s)).obj Y).left),
      (((Over.pullback (S.fromSpecResidueField s)).map f).left ⁻¹' {y}).Finite)
    (y : Y.left) : (f.left ⁻¹' {y}).Finite := by
  obtain ⟨y', hy'⟩ := exists_fst_eq y rfl
  refine ((h _ y').image (pullback.fst X.hom (S.fromSpecResidueField (Y.hom y)))).subset fun x (hx : f.left x = y) => ?_
  have hs : X.hom x = Y.hom y := by
    rw [← hx, ← Scheme.Hom.comp_apply, Over.w f]
  obtain ⟨x', rfl⟩ := exists_fst_eq x hs
  refine ⟨x', ?_, rfl⟩
  apply fst_injective Y
  rw [hy', ← Scheme.Hom.comp_apply, fiberMap_fst, Scheme.Hom.comp_apply, hx]

/-- A morphism from a proper `S`-scheme to a separated `S`-scheme is finite if all
of its residue-field fibres are. -/
theorem isFinite_of_fiber {X Y : Over S} (f : X ⟶ Y) [IsProper X.hom] [IsSeparated Y.hom]
    (h : ∀ s : S, IsFinite ((Over.pullback (S.fromSpecResidueField s)).map f).left) :
    IsFinite f.left := by
  have : IsProper (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : IsProper f.left := IsProper.of_comp f.left Y.hom
  have : LocallyQuasiFinite f.left := .of_finite_preimage_singleton _
    (finite_preimage_singleton_of_fiber f fun s y => by
      have := h s
      exact Scheme.Hom.finite_preimage_singleton _ y)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite _).mpr ⟨inferInstance, inferInstance⟩

/-- A homomorphism between smooth proper group schemes over `S` is finite, flat, and
surjective if its pullback over every residue-field point of `S` is so. -/
theorem fiberwiseIsogeny : FiberwiseIsogenyStatement.{u} := by
  intro S G H _ _ _ _ f hf
  exact ⟨isFinite_of_fiber f.hom.hom fun s => (hf s).1,
    Langlands.AlgebraicGeometry.fiberwiseFlatness S G.X H.X f.hom.hom
      inferInstance inferInstance inferInstance fun s => (hf s).2.1,
    surjective_of_fiber f.hom.hom fun s => (hf s).2.2⟩

end Langlands.GroupScheme
