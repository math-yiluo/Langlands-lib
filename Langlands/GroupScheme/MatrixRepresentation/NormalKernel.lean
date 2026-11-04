import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterRepresentation
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter
import Langlands.GroupScheme.MatrixRepresentation.TensorFixedStabilizer
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Actual representations with a prescribed normal kernel -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section CharacterVectors

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An all-test character vector satisfies the universal affine character equation. -/
theorem mem_characterSpace_of_pointwise (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (v : n → k)
    (hv : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun r => scalarMap T (v r)) =
        (characterEval χ T x : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r))) :
    v ∈ ρ.characterSpace χ := by
  let A := CharacterUnits.Coord G
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let x := CharacterUnits.universalPoint G
  let e := Corepresented.affineSectionsAlgEquiv A
  have hunit : e (characterEval χ T x : Γ(T.left, ⊤)) =
      (CharacterUnits.unit χ : A) := by
    change (Corepresented.affineSectionsIso A).hom.hom.toRingHom _ = _
    rw [Corepresented.affineSectionsIso_hom_ringHom]
    exact (Gm.affinePointsEquiv_val T.hom (x ≫ χ.toMul.hom.hom)).symm
  have hu : e.symm (CharacterUnits.unit χ : A) =
      (characterEval χ T x : Γ(T.left, ⊤)) := by
    apply e.injective
    rw [e.apply_symm_apply, hunit]
  have h := hv T x
  rw [pointMatrix_eq_affineMatrix] at h
  have hs : (fun r => scalarMap T (v r)) =
      (fun r => e.symm (algebraMap k A (v r))) := by
    funext r
    exact UnipotentMatrixCriterion.scalarMap_affine A (v r)
  rw [hs] at h
  rw [mem_characterSpace_iff]
  funext r
  apply e.symm.injective
  have hr := congrFun h r
  change e.symm (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
      (fun s => algebraMap k A (v s))) r) = _
  calc
    _ = ((ρ.affineMatrix A x : Matrix n n A).map e.symm.toRingHom *ᵥ
        (fun s => e.symm (algebraMap k A (v s)))) r :=
      e.symm.toRingHom.map_mulVec _ _ r
    _ = _ := by
      change ((ρ.affineMatrix A x : Matrix n n A).map e.symm.toRingHom *ᵥ
        (fun s => e.symm (algebraMap k A (v s)))) r =
          e.symm ((CharacterUnits.unit χ : A) * algebraMap k A (v r))
      rw [map_mul, hu]
      exact hr

/-- The chosen coordinate vector belongs to the character space of its line action. -/
theorem coordinateLine_mem_characterSpace (ρ : MatrixRepresentation G n)
    (j : n) (hline : ρ.PreservesCoordinateLine j) :
    (Pi.single j 1 : n → k) ∈
      ρ.characterSpace (ρ.coordinateLineRationalCharacter j hline) := by
  apply mem_characterSpace_of_pointwise
  intro T x
  have hs : (fun r => scalarMap T ((Pi.single j (1 : k) : n → k) r)) =
      (Pi.single j (1 : Γ(T.left, ⊤)) : n → Γ(T.left, ⊤)) := by
    ext r
    by_cases h : r = j <;> simp [h]
  rw [hs]
  exact ρ.coordinateLineCharacter_action j hline T x

/-- Vectors of opposite rational characters have a fixed pure tensor on all tests. -/
theorem isFixedVector_tensor_of_opposite_characters
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (χ : rationalCharacters G) {v : n → k} {w : m → k}
    (hv : v ∈ ρ.characterSpace χ) (hw : w ∈ σ.characterSpace (-χ)) :
    (ρ.tensor σ).IsFixedVector (fun ij => v ij.1 * w ij.2) := by
  apply (isFixedVector_iff_affine_model (ρ.tensor σ) (Lie.coordinateIso G) _).2
  rw [← CharacterUnits.universalPoint_eq]
  simp only [map_mul]
  rw [tensor_affineMatrix]
  rw [GeneralLinear.kroneckerHom_mulVec n m _ _
    (fun r => algebraMap k (CharacterUnits.Coord G) (v r))
    (fun s => algebraMap k (CharacterUnits.Coord G) (w s))]
  have hv' := hv
  have hw' := hw
  rw [mem_characterSpace_iff] at hv' hw'
  unfold universalCharacterMatrix at hv' hw'
  rw [hv', hw', characterUnit_neg]
  funext ij
  change ((CharacterUnits.unit χ : CharacterUnits.Coord G) * _) *
    (((CharacterUnits.unit χ)⁻¹ : (CharacterUnits.Coord G)ˣ) * _) = _
  calc
    _ = ((CharacterUnits.unit χ : CharacterUnits.Coord G) *
        ((CharacterUnits.unit χ)⁻¹ : (CharacterUnits.Coord G)ˣ)) *
        (algebraMap k (CharacterUnits.Coord G) (v ij.1) *
          algebraMap k (CharacterUnits.Coord G) (w ij.2)) := by ring
    _ = _ := by rw [Units.mul_inv, one_mul]

end CharacterVectors

section NormalKernels

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Over an algebraically closed field, a closed normal subgroup of a reduced
finite-type affine group is the full kernel of an actual finite representation.
The subgroup itself need not be reduced or smooth. -/
theorem nonempty_kernelRepresentation_of_normal_closed
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : Nonempty (KernelRepresentation i) := by
  classical
  have : IsClosedImmersion i.hom.hom.left := hc
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨a, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G H i hc
  have hline : (ρ.restrict i).PreservesCoordinateLine j := by
    intro T x
    simpa only [pointMatrix_restrict] using
      (hρ T (x ≫ i.hom.hom)).1 (SubgroupFunctor.mem_range.2 ⟨x, rfl⟩)
  let χ := (ρ.restrict i).coordinateLineRationalCharacter j hline
  have hv : (Pi.single j 1 : Fin (a + 1) → k) ∈
      (ρ.restrict i).characterSpace χ :=
    coordinateLine_mem_characterSpace (ρ.restrict i) j hline
  have hne : (Pi.single j 1 : Fin (a + 1) → k) ≠ 0 := by
    intro hz
    have he := congrFun hz j
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using he)
  obtain ⟨d, σ, w, hwn, hwm⟩ := exists_inverse_normal_characterVector ρ i hN χ hv hne
  obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
    by_contra h
    apply hwn
    ext s
    exact not_not.mp ((not_exists.mp h) s)
  let w' : Fin d → k := (w s)⁻¹ • w
  have hwm' : w' ∈ (σ.restrict i).characterSpace (-χ) :=
    ((σ.restrict i).characterSpace (-χ)).smul_mem (w s)⁻¹ hwm
  have hw' : w' s = 1 := by
    change (w s)⁻¹ * w s = 1
    exact inv_mul_cancel₀ hs
  have hfixed : ((ρ.tensor σ).restrict i).IsFixedVector
      (fun ij => (Pi.single j (1 : k) : Fin (a + 1) → k) ij.1 * w' ij.2) := by
    rw [← tensor_restrict]
    exact isFixedVector_tensor_of_opposite_characters (ρ.restrict i) (σ.restrict i) χ hv hwm'
  refine nonempty_kernelRepresentation_of_fixedTensor i hN ρ σ
    (Pi.single j 1) w' j s (Pi.single_eq_same _ _) hw' hfixed ?_
  intro T x hx
  apply (hρ T x).2
  have hsingle : (fun r => scalarMap T ((Pi.single j (1 : k) : Fin (a + 1) → k) r)) =
      (Pi.single j (1 : Γ(T.left, ⊤)) : Fin (a + 1) → Γ(T.left, ⊤)) := by
    ext r
    by_cases h : r = j <;> simp [h]
  simpa only [hsingle] using hx

/-- Choose the actual exact-kernel representation of a closed normal subgroup
of a reduced affine group over an algebraically closed field. -/
def normalKernelRepresentation (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal) : KernelRepresentation i :=
  Classical.choice (nonempty_kernelRepresentation_of_normal_closed i hc hN)

end NormalKernels

end Langlands.GroupScheme.MatrixRepresentation
