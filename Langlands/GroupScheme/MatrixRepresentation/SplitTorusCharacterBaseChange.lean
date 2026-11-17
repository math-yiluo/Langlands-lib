import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension
import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Split-torus character spaces under field extension -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix Classical

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom T.toGrp.X.hom]
  {n : ℕ}

local notation "bc" => algebraBaseMap k K

local instance characterBaseChangeAffine : IsAffineHom (((CommGroupScheme.baseChange bc).obj T).toGrp).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd T.toGrp.X.hom bc)
  infer_instance

local instance characterBaseChangeGroupAffine :
    IsAffineHom ((GroupScheme.baseChange bc).obj T.toGrp).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd T.toGrp.X.hom bc)
  infer_instance

/-- The character space indexed by the actual character lattice of a commutative group. -/
def latticeCharacterSpace (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) : Submodule k (Fin n → k) :=
  ρ.characterSpace ((rationalCharacters.equivCharacterLattice T).symm χ)

/-- Reindexing by the character lattice preserves the internal decomposition. -/
theorem isInternal_latticeCharacterSpace
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n)) :
    DirectSum.IsInternal (ρ.latticeCharacterSpace) :=
  isInternal_characterSpace_of_isSplitTorus hT ρ

/-- The extended span of a character space, in the standard extended coordinates. -/
def extendedLatticeCharacterSpace (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) : Submodule K (Fin n → K) :=
  Submodule.span K ((fun v : Fin n → k => fun i => algebraMap k K (v i)) ''
    (ρ.latticeCharacterSpace χ : Set (Fin n → k)))

/-- Every original character vector remains a vector for its pulled-back character. -/
theorem latticeCharacterSpace_baseChange_mem
    (ρ : MatrixRepresentation T.toGrp (Fin n)) (χ : characterLattice T)
    {v : Fin n → k} (hv : v ∈ ρ.latticeCharacterSpace χ) :
    (fun i => algebraMap k K (v i)) ∈
      (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  have h := ρ.characterSpace_affine hv (CommAlgCat.of (CommRingCat.of k) A)
    (Lie.affineBaseChangeEquiv k K T.toGrp A x)
  change ((ρ.baseChange bc).affineMatrix A x : Matrix (Fin n) (Fin n) A) *ᵥ
      (fun i => algebraMap K A (algebraMap k K (v i))) =
    (Lie.characterValue (characterLattice.baseChange bc T χ) x : A) •
      (fun i => algebraMap K A (algebraMap k K (v i)))
  rw [ρ.affineMatrix_baseChange, Lie.characterValue_baseChange]
  exact h

/-- The entire extended span lies in the pulled-back character space. -/
theorem extendedLatticeCharacterSpace_le
    (ρ : MatrixRepresentation T.toGrp (Fin n)) (χ : characterLattice T) :
    ρ.extendedLatticeCharacterSpace (K := K) χ ≤
      (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact latticeCharacterSpace_baseChange_mem ρ χ hv

/-- Extending a complete character decomposition still spans the extended coordinate space. -/
theorem iSup_extendedLatticeCharacterSpace_eq_top
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n)) :
    (⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ) = ⊤ := by
  have hi : (⨆ χ, ρ.latticeCharacterSpace χ) = ⊤ :=
    iSup_characterSpace_eq_top_of_isSplitTorus hT ρ
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := (Lie.coordinateTensorEquiv (k := k) (K := K) n).surjective y
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    have hv : v ∈ ⨆ χ, ρ.latticeCharacterSpace χ := by rw [hi]; trivial
    have he : (fun i => algebraMap k K (v i)) ∈
        ⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ := by
      refine Submodule.iSup_induction (fun χ => ρ.latticeCharacterSpace χ)
        (motive := fun v => (fun i => algebraMap k K (v i)) ∈
          ⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ) hv ?_ ?_ ?_
      · intro χ v hv
        exact Submodule.mem_iSup_of_mem χ (Submodule.subset_span ⟨v, hv, rfl⟩)
      · simpa only [Pi.zero_apply, map_zero, Pi.zero_def] using
          (⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ).zero_mem
      · intro v w hv hw
        simpa only [Pi.add_apply, map_add, Pi.add_def] using
          (⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ).add_mem hv hw
    simpa only [Lie.coordinateTensorEquiv_tmul, Pi.smul_def, smul_eq_mul] using
      (⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ).smul_mem c he
  | add x y hx hy =>
    simpa only [LinearEquiv.map_add] using
      (⨆ χ, ρ.extendedLatticeCharacterSpace (K := K) χ).add_mem hx hy

/-- Every new character space is the sum of the extended spaces in its character fiber. -/
theorem latticeCharacterSpace_baseChange_eq_iSup
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (ψ : characterLattice ((CommGroupScheme.baseChange bc).obj T)) :
    (ρ.baseChange bc).latticeCharacterSpace ψ =
      ⨆ χ : {χ : characterLattice T // characterLattice.baseChange bc T χ = ψ},
        ρ.extendedLatticeCharacterSpace (K := K) χ.val := by
  classical
  exact submodule_eq_iSup_of_refinement
    (ρ.extendedLatticeCharacterSpace (K := K))
    (latticeCharacterSpace (T := (CommGroupScheme.baseChange bc).obj T) (ρ.baseChange bc))
    (iSup_extendedLatticeCharacterSpace_eq_top hT ρ)
    (isInternal_latticeCharacterSpace
      (T := (CommGroupScheme.baseChange bc).obj T) (hT.baseChange bc) (ρ.baseChange bc))
    (characterLattice.baseChange bc T) (extendedLatticeCharacterSpace_le ρ) ψ

/-- Each pulled-back character space is exactly the scalar-extended original space. -/
theorem latticeCharacterSpace_baseChange_eq_extended
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) :
    (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) =
      ρ.extendedLatticeCharacterSpace (K := K) χ := by
  rw [latticeCharacterSpace_baseChange_eq_iSup hT ρ]
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    have hψ : ψ.val = χ := (hT.characterLattice_baseChange_bijective bc T).injective ψ.property
    rw [hψ]
  · exact le_iSup_of_le ⟨χ, rfl⟩ le_rfl

/-- Tensor extension maps a character space onto the actual pulled-back space. -/
theorem map_latticeCharacterSpace_baseChange
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) :
    ((ρ.latticeCharacterSpace χ).baseChange K).map
        (Lie.coordinateTensorEquiv (k := k) n).toLinearMap =
      (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) := by
  rw [latticeCharacterSpace_baseChange_eq_extended hT ρ χ]
  simp only [Submodule.baseChange_eq_span, Submodule.map_span,
    Submodule.map_coe, Set.image_image, extendedLatticeCharacterSpace]
  have he : (fun v : Fin n → k =>
      (Lie.coordinateTensorEquiv (k := k) n) ((TensorProduct.mk k K (Fin n → k) 1) v)) =
      (fun v : Fin n → k => fun i => algebraMap k K (v i)) := by
    funext v i
    simp only [TensorProduct.mk_apply, Lie.coordinateTensorEquiv_tmul, one_mul]
  change Submodule.span K
    ((fun v : Fin n → k => (Lie.coordinateTensorEquiv (k := k) n)
      ((TensorProduct.mk k K (Fin n → k) 1) v)) '' (ρ.latticeCharacterSpace χ : Set _)) = _
  rw [he]

/-- The usual tensor product gives the actual character space after arbitrary field extension. -/
def latticeCharacterSpaceBaseChangeEquiv
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) :
    K ⊗[k] ρ.latticeCharacterSpace χ ≃ₗ[K]
      (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) :=
  (Submodule.toBaseChange.toLinearEquiv K (ρ.latticeCharacterSpace χ)).trans
    ((Submodule.equivMapOfInjective
      (Lie.coordinateTensorEquiv (k := k) (K := K) n).toLinearMap
      (Lie.coordinateTensorEquiv (k := k) (K := K) n).injective
      ((ρ.latticeCharacterSpace χ).baseChange K)).trans
        (LinearEquiv.ofEq _ _ (map_latticeCharacterSpace_baseChange hT ρ χ)))

/-- Extension of the base field preserves every split-torus character-space dimension. -/
theorem finrank_latticeCharacterSpace_baseChange
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) :
    Module.finrank K ((ρ.baseChange bc).latticeCharacterSpace
      (characterLattice.baseChange bc T χ)) =
      Module.finrank k (ρ.latticeCharacterSpace χ) := by
  rw [← (latticeCharacterSpaceBaseChangeEquiv hT ρ χ).finrank_eq,
    Module.finrank_baseChange]

/-- The nonzero character support is unchanged under extension of the base field. -/
theorem latticeCharacterSpace_baseChange_ne_bot_iff
    (hT : IsSplitTorus T.toGrp) (ρ : MatrixRepresentation T.toGrp (Fin n))
    (χ : characterLattice T) :
    (ρ.baseChange bc).latticeCharacterSpace (characterLattice.baseChange bc T χ) ≠ ⊥ ↔
      ρ.latticeCharacterSpace χ ≠ ⊥ := by
  have hdim := finrank_latticeCharacterSpace_baseChange (K := K) hT ρ χ
  exact not_congr (Submodule.finrank_eq_zero.symm.trans
    ((iff_of_eq (congrArg (fun d : ℕ => d = 0) hdim)).trans Submodule.finrank_eq_zero))

end Langlands.GroupScheme.MatrixRepresentation
