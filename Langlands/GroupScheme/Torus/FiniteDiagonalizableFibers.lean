import Langlands.GroupScheme.Torus.FiniteDiagonalizableResidues
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Irreducible

/-! # Dominant residue fibers of finite diagonalizable factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (k : Type u) [Field k] (A : Type u) [AddCommGroup A]

/-- The actual residue-field point of the full diagonalizable group. -/
def residuePoint (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    Spec (CommRingCat.of P.asIdeal.ResidueField) ⟶
      (groupScheme (CommRingCat.of k) A).X.left :=
  Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k A) P.asIdeal.ResidueField))

@[simp] theorem residuePoint_apply (P : PrimeSpectrum (AddMonoidAlgebra k A))
    (x : Spec (CommRingCat.of P.asIdeal.ResidueField)) :
    residuePoint k A P x = P := by
  have hx : x = (⊥ : PrimeSpectrum P.asIdeal.ResidueField) := Subsingleton.elim _ _
  rw [hx]
  apply PrimeSpectrum.ext
  exact P.asIdeal.ker_algebraMap_residueField

theorem range_residuePoint (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    Set.range (residuePoint k A P) = {P} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact residuePoint_apply k A P y
  · intro hx
    have hx : x = P := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨(⊥ : PrimeSpectrum P.asIdeal.ResidueField),
      residuePoint_apply k A P _⟩

/-- The residue point has the canonical scalar structure over k. -/
theorem residuePoint_over (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    residuePoint k A P ≫ (groupScheme (CommRingCat.of k) A).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

variable (X : Over (Spec (CommRingCat.of k)))

/-- Include the residue fiber into the product with the full finite factor.
The source is the actual scalar extension of X to the residue field. -/
def residueFiberInclusion (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)))).obj X).left ⟶
        (X ⊗ (groupScheme (CommRingCat.of k) A).X).left :=
  pullback.map X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField)))
    X.hom (groupScheme (CommRingCat.of k) A).X.hom
    (𝟙 X.left) (residuePoint k A P) (𝟙 _)
    (by simp) (by simpa using (residuePoint_over k A P).symm)

/-- The image is precisely the topological fiber above the selected prime. -/
theorem range_residueFiberInclusion (P : PrimeSpectrum (AddMonoidAlgebra k A)) :
    Set.range (residueFiberInclusion k A X P) =
      (snd X (groupScheme (CommRingCat.of k) A).X).left ⁻¹'
        {(P : (groupScheme (CommRingCat.of k) A).X.left)} := by
  dsimp only [residueFiberInclusion]
  erw [Scheme.Pullback.range_map]
  simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id, Set.preimage_univ,
    Set.univ_inter, range_residuePoint]
  rfl

/-- The actual residue-field fibers jointly cover the product, even when the
finite diagonalizable factor has nilpotents. -/
theorem residueFibers_cover (x : (X ⊗ (groupScheme (CommRingCat.of k) A).X).left) :
    ∃ P : PrimeSpectrum (AddMonoidAlgebra k A),
      x ∈ Set.range (residueFiberInclusion k A X P) := by
  refine ⟨(snd X (groupScheme (CommRingCat.of k) A).X).left x, ?_⟩
  rw [range_residueFiberInclusion]
  rfl

/-- A dominant map from a product with a finite diagonalizable group to an
irreducible scheme remains dominant on at least one actual residue fiber. -/
theorem exists_isDominant_residueFiber [Finite A] {Y : Scheme.{u}}
    [IrreducibleSpace Y]
    (p : (X ⊗ (groupScheme (CommRingCat.of k) A).X).left ⟶ Y) [IsDominant p] :
    ∃ P : PrimeSpectrum (AddMonoidAlgebra k A),
      IsDominant (residueFiberInclusion k A X P ≫ p) := by
  classical
  let : Fintype (PrimeSpectrum (AddMonoidAlgebra k A)) := Fintype.ofFinite _
  let C : PrimeSpectrum (AddMonoidAlgebra k A) → Set Y :=
    fun P => closure (Set.range (residueFiberInclusion k A X P ≫ p))
  have hcover : Set.range p ⊆ ⋃ P, C P := by
    rintro y ⟨x, rfl⟩
    obtain ⟨P, z, hz⟩ := residueFibers_cover k A X x
    exact Set.mem_iUnion.mpr ⟨P, subset_closure ⟨z, by
      simp only [Scheme.Hom.comp_apply, hz]⟩⟩
  have hfull : (Set.univ : Set Y) ⊆ ⋃ P, C P := by
    rw [← p.denseRange.closure_range]
    exact closure_minimal hcover (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  let t : Finset (Set Y) := Finset.univ.image C
  have ht : ∀ z ∈ t, IsClosed z := by
    intro z hz
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hz
    exact isClosed_closure
  have hsub : (Set.univ : Set Y) ⊆ ⋃₀ (t : Set (Set Y)) := by
    simpa only [t, Finset.coe_image, Finset.coe_univ, Set.sUnion_image,
      Set.biUnion_univ] using hfull
  obtain ⟨z, hz, hY⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp
      (IrreducibleSpace.isIrreducible_univ Y) t ht hsub
  obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨P, ⟨?_⟩⟩
  rw [denseRange_iff_closure_range]
  exact Set.eq_univ_of_univ_subset hY

end Langlands.GroupScheme.Diagonalizable
