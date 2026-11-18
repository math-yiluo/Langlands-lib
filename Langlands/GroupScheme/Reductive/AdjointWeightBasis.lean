import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.IntertwinerTransport
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # Weight coordinates of the adjoint representation -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix

namespace Langlands.GroupScheme.SplitPinning

section WeightBasis

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G) {n : Type} [Fintype n] [DecidableEq n]

/-- Representation weight vectors satisfy the eigenvector equation on every affine test. -/
theorem mem_representationWeightSpace_iff_affine (ρ : MatrixRepresentation G n)
    (μ : characterLattice p.torus) (v : n → k) :
    v ∈ p.representationWeightSpace ρ μ ↔
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (t : GroupScheme.affinePoints p.torus.toGrp A),
        (ρ.affineMatrix A (t ≫ p.inclusion.hom.hom) : Matrix n n A) *ᵥ
            (fun i => algebraMap k A (v i)) =
          (Lie.characterValue μ t : A) • (fun i => algebraMap k A (v i)) := by
  let := p.isSplitTorus.isAffineHom
  change v ∈ (ρ.restrict p.inclusion).characterSpace
    ((rationalCharacters.equivCharacterLattice p.torus).symm μ) ↔ _
  simp only [MatrixRepresentation.mem_characterSpace_iff_affine]
  rfl

/-- The dimension of a weight space is the number of basis vectors with that weight. -/
theorem finrank_representationWeightSpace_eq_card (ρ : MatrixRepresentation G n)
    (b : Basis n k (n → k)) (w : n → characterLattice p.torus)
    (hb : ∀ i, b i ∈ p.representationWeightSpace ρ (w i))
    (μ : characterLattice p.torus) [Fintype {i // w i = μ}] :
    Module.finrank k (p.representationWeightSpace ρ μ) = Fintype.card {i // w i = μ} := by
  classical
  let := p.isSplitTorus.isAffineHom
  let τ := ρ.restrict p.inclusion
  let χ := (rationalCharacters.equivCharacterLattice p.torus).symm
  let P := τ.characterProjector (χ μ)
  let bμ : {i // w i = μ} → (n → k) := fun i => b i
  have hspan : Submodule.span k (Set.range bμ) = p.representationWeightSpace ρ μ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      exact hi ▸ hb i
    · intro v hv
      have hPv : P v = v := by
        simpa using τ.characterProjector_of_mem (χ μ) (χ μ) hv
      have hPb (i : n) : P (b i) = if w i = μ then b i else 0 := by
        simpa only [χ.injective.eq_iff] using τ.characterProjector_of_mem (χ μ) (χ (w i)) (hb i)
      have hsum := congrArg P (b.sum_repr v)
      simp only [map_sum, map_smul, hPv, hPb] at hsum
      rw [← hsum]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      split
      · rename_i hi
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      · exact Submodule.zero_mem _
  rw [← hspan]
  exact Module.finrank_eq_card_basis
    (Basis.span (b.linearIndependent.comp (fun i : {i // w i = μ} => i.val) Subtype.val_injective))

end WeightBasis

section Adjoint

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {n : ℕ}

set_option maxHeartbeats 800000 in
private theorem adjointBaseChange_coordinates_mem_weightSpace
    (p : SplitPinning (k := K) G_K) (c : Lie.FiniteCoordinates G n)
    (μ : characterLattice p.torus) (X : Additive (lieKernel G_K K)) :
    ((c.baseChange k K).equiv (.of (CommRingCat.of K) K) X : Fin n → K) ∈
        (p.representationWeightSpace (k := K) (n := Fin n)
          ((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)) μ :
          Submodule K (Fin n → K)) ↔
      X ∈ weightSpace (R := CommRingCat.of K) (G := G_K) p.inclusion μ := by
  rw [mem_representationWeightSpace_iff_affine, mem_weightSpace]
  have htest (A : CommAlgCat.{u} (CommRingCat.of K)) (t : GroupScheme.affinePoints p.torus.toGrp A) :
      (((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)).affineMatrix A
          (t ≫ p.inclusion.hom.hom) : Matrix (Fin n) (Fin n) A) *ᵥ
          (fun i => algebraMap K A ((c.baseChange k K).equiv (.of (CommRingCat.of K) K) X i)) =
        (Lie.characterValue μ t : A) •
          (fun i => algebraMap K A ((c.baseChange k K).equiv (.of (CommRingCat.of K) K) X i)) ↔
      adjoint G_K A (t ≫ p.inclusion.hom.hom) (lieKernelMapLinear G_K (Algebra.ofId K A) X) =
        (Lie.characterValue μ t : A) • lieKernelMapLinear G_K (Algebra.ofId K A) X := by
    let : Algebra k A := Algebra.compHom A (algebraMap k K)
    let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
    let cK := c.baseChange k K
    let f : CommAlgCat.of (CommRingCat.of K) K ⟶ A := CommAlgCat.ofHom (Algebra.ofId K A)
    have hvec :
        (fun i => algebraMap K A (cK.equiv (.of (CommRingCat.of K) K) X i)) =
          cK.equiv A (lieKernelMapLinear G_K (Algebra.ofId K A) X) :=
      (cK.naturality f X).symm
    rw [hvec]
    change ((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)).affineAction A
        (t ≫ p.inclusion.hom.hom) _ = _ ↔ _
    rw [show ((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)).affineAction A
          (t ≫ p.inclusion.hom.hom) (cK.equiv A (lieKernelMapLinear G_K (Algebra.ofId K A) X)) =
        (Lie.adjointRepresentation cK).affineAction A
          (t ≫ p.inclusion.hom.hom) (cK.equiv A (lieKernelMapLinear G_K (Algebra.ofId K A) X)) by
      rw [MatrixRepresentation.affineAction_apply,
        MatrixRepresentation.affineMatrix_baseChange_fintype]
      exact (Lie.adjointRepresentation_baseChange_affineAction (k := k) (K := K) c
        (A := A) (t ≫ p.inclusion.hom.hom)
        (cK.equiv A (lieKernelMapLinear G_K (Algebra.ofId K A) X))).symm]
    rw [Lie.adjointRepresentation_affineAction,
      ← (cK.equiv A).map_smul (Lie.characterValue μ t : A)]
    exact (cK.equiv A).injective.eq_iff
  exact ⟨fun h A _ _ t => (htest (.of (CommRingCat.of K) A) t).mp (h _ t),
    fun h A t => (htest A t).mpr (h A t)⟩

/-- Pulled-back finite Lie coordinates identify the split adjoint weight spaces. -/
def adjointBaseChangeWeightSpaceEquiv
    (p : SplitPinning (k := K) G_K) (c : Lie.FiniteCoordinates G n)
    (μ : characterLattice p.torus) :
    weightSpace (R := CommRingCat.of K) (G := G_K) p.inclusion μ ≃ₗ[K]
      p.representationWeightSpace (k := K) (n := Fin n)
        ((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)) μ := by
  let e := (c.baseChange k K).equiv (.of (CommRingCat.of K) K)
  apply e.ofSubmodules
  ext v
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (p.adjointBaseChange_coordinates_mem_weightSpace c μ X).mpr hX
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply (p.adjointBaseChange_coordinates_mem_weightSpace c μ (e.symm v)).mp
    change e (e.symm v) ∈ _
    rwa [e.apply_symm_apply]

set_option maxHeartbeats 800000 in
/-- After scalar extension, an adjoint weight basis has exactly one coordinate for each root
and all remaining coordinates have weight zero. -/
theorem exists_adjointBaseChangeWeightBasis
    (p : SplitPinning (k := K) G_K) (c : Lie.FiniteCoordinates G n) :
    ∃ (b : Basis (Fin n) K (Fin n → K)) (w : Fin n → characterLattice p.torus)
      (r : p.rootIndex ↪ Fin n),
      (∀ i, b i ∈ p.representationWeightSpace
        ((Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)) (w i)) ∧
      (∀ i, w (r i) = p.rootDatum.root i) ∧
      (∀ i, i ∉ Set.range r → w i = 0) := by
  classical
  let := p.isSplitTorus.isAffineHom
  let ρ : MatrixRepresentation G_K (Fin n) :=
    (Lie.adjointRepresentation c).baseChange (algebraBaseMap k K)
  obtain ⟨b, χ, hχ⟩ := MatrixRepresentation.exists_characterBasis (ρ.restrict p.inclusion)
    (MatrixRepresentation.iSup_characterSpace_eq_top_of_isSplitTorus p.isSplitTorus _)
  let w (i : Fin n) := rationalCharacters.equivCharacterLattice p.torus (χ i)
  have hb (i : Fin n) : b i ∈ p.representationWeightSpace ρ (w i) := by
    change b i ∈ (ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm
        ((rationalCharacters.equivCharacterLattice p.torus) (χ i)))
    simpa only [AddEquiv.symm_apply_apply] using hχ i
  have hroot (i : p.rootIndex) : p.rootDatum.root i ∈ roots p.inclusion := by
    rw [← p.isRootDatum.2.1]
    exact ⟨i, rfl⟩
  have hunt (i : p.rootIndex) :
      ∃ j : {j : Fin n // w j = p.rootDatum.root i}, ∀ l, l = j := by
    apply Fintype.card_eq_one_iff.mp
    obtain ⟨e⟩ := splitRootLieLine K G_K p.isConnectedReductive
      p.torus p.isSplitTorus p.inclusion p.isMaximalTorus _ (hroot i)
    rw [← p.finrank_representationWeightSpace_eq_card ρ b w hb,
      ← (p.adjointBaseChangeWeightSpaceEquiv c (p.rootDatum.root i)).finrank_eq,
      ← e.finrank_eq, Module.finrank_self]
  choose r hr using hunt
  let e : p.rootIndex ↪ Fin n :=
    ⟨fun i => (r i).val, fun i j hij => p.rootDatum.root.injective
      ((r i).property.symm.trans ((congrArg w hij).trans (r j).property))⟩
  refine ⟨b, w, e, hb, fun i => (r i).property, ?_⟩
  intro j hj
  by_contra hzero
  have hpos : 0 < Module.finrank K (weightSpace p.inclusion (w j)) := by
    let : Nonempty {i : Fin n // w i = w j} := ⟨⟨j, rfl⟩⟩
    rw [(p.adjointBaseChangeWeightSpaceEquiv c (w j)).finrank_eq,
      p.finrank_representationWeightSpace_eq_card ρ b w hb]
    exact Fintype.card_pos
  have hmem : w j ∈ roots p.inclusion := mem_roots.mpr ⟨hzero, fun h => by
    rw [h, finrank_bot] at hpos
    exact (Nat.lt_irrefl 0) hpos⟩
  rw [← p.isRootDatum.2.1] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact hj ⟨i, (congrArg Subtype.val (hr i ⟨j, hi.symm⟩)).symm⟩

end Adjoint

end Langlands.GroupScheme.SplitPinning
