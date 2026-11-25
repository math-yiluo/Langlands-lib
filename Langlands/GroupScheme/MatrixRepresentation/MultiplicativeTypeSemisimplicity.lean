import Langlands.GroupScheme.MatrixRepresentation.SemisimplicityScalarExtension
import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof

/-! # Semisimplicity of actual representations of groups of multiplicative type -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisPiDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Every subspace of an actual character space is stable on all affine algebra tests. -/
theorem isStableSubspace_of_le_characterSpace (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (V : Submodule k (n → k)) (hV : V ≤ ρ.characterSpace χ) :
    ρ.IsStableSubspace V := by
  intro A x v hv ℓ
  rw [characterSpace_affine (hV hv) A x]
  let a : A := Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom)
  have h (c : k) : ℓ (a * algebraMap k A c) = c * ℓ a := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  change (fun i => ℓ (a * algebraMap k A (v i))) ∈ V
  simp only [h]
  simpa only [Pi.smul_def, smul_eq_mul, mul_comm] using V.smul_mem (ℓ a) hv

/-- Spanning by actual character spaces implies the exact sum-of-simple-subspaces
semisimplicity condition, including the zero representation. -/
theorem isSemisimple_of_iSup_characterSpace_eq_top (ρ : MatrixRepresentation G n)
    (hspan : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤) :
    ρ.IsSemisimple := by
  apply top_unique
  rw [← hspan]
  apply iSup_le
  intro χ v hv
  by_cases hv0 : v = 0
  · subst v
    exact Submodule.zero_mem _
  let L := Submodule.span k ({v} : Set (n → k))
  have hL : L ≤ ρ.characterSpace χ := (Submodule.span_singleton_le_iff_mem v _).mpr hv
  have hstable := isStableSubspace_of_le_characterSpace ρ χ L hL
  have hatom : IsAtom L :=
    Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton hv0)
  have hsimple : L ∈ {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} :=
    ⟨hstable, hatom.ne_bot, fun U _ hU => hatom.le_iff.mp hU⟩
  exact (le_sSup hsimple) (Submodule.mem_span_singleton_self v)

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- Every finite-coordinate representation of an affine group scheme of
multiplicative type over an arbitrary field is semisimple. -/
theorem isSemisimple_of_isMultiplicativeType (ρ : MatrixRepresentation G n)
    (hG : IsMultiplicativeType G) : ρ.IsSemisimple := by
  let K := SeparableClosure k
  have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
    k K G hG
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
  let := hΛ
  let := hfg
  apply isSemisimple_of_baseChange (K := K) ρ
  apply isSemisimple_of_iSup_characterSpace_eq_top
  exact iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e _

end Langlands.GroupScheme.MatrixRepresentation
