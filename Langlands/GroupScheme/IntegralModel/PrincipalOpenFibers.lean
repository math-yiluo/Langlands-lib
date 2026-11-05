import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.Global.AdelicSIntegersColimitProof

/-! # Field fibres after inverting an arithmetic coefficient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Global

/-- Enlarge an actual finite S-integer ring so that a specified nonzero
coefficient becomes a unit under the literal integer-ring inclusion. -/
theorem exists_numberFieldSIntegers_isUnit (F : Type u) [Field F] [NumberField F]
    (S : Finset (FinitePlace F)) (r : (S : Set (FinitePlace F)).integer F)
    (hr : r ≠ 0) :
    ∃ T : AdelicLevelIndexAbove S, IsUnit (numberFieldSIntegersMap F T.property r) := by
  obtain ⟨T, hT⟩ := exists_mem_numberFieldSIntegersAbove F S ((r : F)⁻¹)
  refine ⟨T, isUnit_iff_exists_inv.mpr ⟨⟨(r : F)⁻¹, hT⟩, ?_⟩⟩
  apply Subtype.ext
  change (r : F) * (r : F)⁻¹ = 1
  exact mul_inv_cancel₀ (fun h => hr (Subtype.ext h))

/-- A chosen actual finite enlargement that inverts the given coefficient,
together with its proved unit property. -/
def numberFieldSIntegersUnitStage (F : Type u) [Field F] [NumberField F]
    (S : Finset (FinitePlace F)) (r : (S : Set (FinitePlace F)).integer F)
    (hr : r ≠ 0) :
    {T : AdelicLevelIndexAbove S // IsUnit (numberFieldSIntegersMap F T.property r)} :=
  ⟨(exists_numberFieldSIntegers_isUnit F S r hr).choose,
    (exists_numberFieldSIntegers_isUnit F S r hr).choose_spec⟩

end Langlands.Global

namespace Langlands.GroupScheme

/-- All actual field-valued fibres of a smooth affine family suffice for the
precise geometric-fibre predicate used by `IsReductive`. -/
theorem isReductive_of_fieldReductive {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (hSmooth : Smooth G.X.hom) (hAffine : IsAffineHom G.X.hom)
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj G)) :
    IsReductive G := by
  refine ⟨hSmooth, hAffine, ?_⟩
  intro s
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (geometricPoint _ s)
  let : Algebra R (AlgebraicClosure ((Spec (CommRingCat.of R)).residueField s)) :=
    φ.hom.toAlgebra
  change IsPseudoReductive ((baseChange (geometricPoint _ s)).obj G)
  rw [← hφ]
  exact (h _).isPseudoReductive

/-- If connected reductivity is known on the principal open of `r`, a
coefficient change that makes `r` a unit gives connected reductivity at every
actual field-valued point of the changed family. -/
theorem fieldReductive_baseChange_of_isUnit {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (G : GroupScheme (Spec (CommRingCat.of R))) (r : R)
    (hr : IsUnit (φ r))
    (h : ∀ (k : Type u) [Field k] [Algebra R k], algebraMap R k r ≠ 0 →
      IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj G)) :
    ∀ (k : Type u) [Field k] [Algebra A k],
      IsConnectedReductive ((baseChange (Spec.algebraMap A k)).obj
        ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)) := by
  intro k _ _
  let : Algebra R k := ((algebraMap A k).comp φ).toAlgebra
  have hne : algebraMap R k r ≠ 0 := (hr.map (algebraMap A k)).ne_zero
  have hg := h k hne
  have he : Spec.algebraMap R k = Spec.algebraMap A k ≫
      Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp]
    rfl
  rw [he] at hg
  exact hg.of_iso (baseChangeCompIso (Spec.map (CommRingCat.ofHom φ))
    (Spec.algebraMap A k) G).symm

open Langlands.Global

/-- The arithmetic comparison from a principal-open good-fibre premise to
all field fibres after enlarging the original exceptional set. -/
theorem exists_numberFieldSIntegers_fieldReductive
    (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F))
    (G : GroupScheme (Spec (CommRingCat.of ((S : Set (FinitePlace F)).integer F))))
    (r : (S : Set (FinitePlace F)).integer F) (hr : r ≠ 0)
    (h : ∀ (k : Type u) [Field k]
      [Algebra ((S : Set (FinitePlace F)).integer F) k],
      algebraMap ((S : Set (FinitePlace F)).integer F) k r ≠ 0 →
      IsConnectedReductive ((baseChange
        (Spec.algebraMap ((S : Set (FinitePlace F)).integer F) k)).obj G)) :
    ∃ T : AdelicLevelIndexAbove S,
      ∀ (k : Type u) [Field k] [Algebra ((T.val : Set (FinitePlace F)).integer F) k],
        IsConnectedReductive ((baseChange
          (Spec.algebraMap ((T.val : Set (FinitePlace F)).integer F) k)).obj
          ((baseChange (Spec.map
            (CommRingCat.ofHom (numberFieldSIntegersMap F T.property)))).obj G)) := by
  obtain ⟨T, hT⟩ := exists_numberFieldSIntegers_isUnit F S r hr
  exact ⟨T, fieldReductive_baseChange_of_isUnit
    (numberFieldSIntegersMap F T.property) G r hT h⟩

end Langlands.GroupScheme
