import Langlands.GroupScheme.MatrixRepresentation.PositiveTensorPower
import Langlands.GroupScheme.MatrixRepresentation.NormalKernel

/-! # Exact normal kernels from inverse positive multiple characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- If a normalized subgroup character vector detects subgroup membership by its line,
an ambient vector of the inverse of any positive multiple character gives an exact kernel.
No reducedness or smoothness assumption is made. -/
theorem nonempty_kernelRepresentation_of_inverse_multiple
    (i : H ⟶ G) (hN : (SubgroupFunctor.range i).IsNormal)
    (ρ : MatrixRepresentation G n) (χ : rationalCharacters H)
    (v : n → k) (j : n) (hv : v j = 1)
    (hχ : v ∈ (ρ.restrict i).characterSpace χ)
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
          (fun s => scalarMap T (v s)) =
            (a : Γ(T.left, ⊤)) • (fun s => scalarMap T (v s))) →
        x ∈ (SubgroupFunctor.range i).carrier T)
    (r : ℕ) (σ : MatrixRepresentation G m) (w : m → k)
    (hw : w ≠ 0)
    (hwm : w ∈ (σ.restrict i).characterSpace (-((r + 1) • χ))) :
    Nonempty (KernelRepresentation i) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
    by_contra h
    apply hw
    ext s
    exact not_not.mp ((not_exists.mp h) s)
  let w' : m → k := (w s)⁻¹ • w
  have hwm' : w' ∈ (σ.restrict i).characterSpace (-((r + 1) • χ)) :=
    ((σ.restrict i).characterSpace (-((r + 1) • χ))).smul_mem (w s)⁻¹ hwm
  have hw' : w' s = 1 := by
    change (w s)⁻¹ * w s = 1
    exact inv_mul_cancel₀ hs
  have hpow : positiveTensorVector v r ∈
      ((ρ.positiveTensorPower r).restrict i).characterSpace ((r + 1) • χ) := by
    rw [← positiveTensorPower_restrict]
    exact positiveTensorPower_characterSpace (ρ.restrict i) hχ r
  have hfixed : (((ρ.positiveTensorPower r).tensor σ).restrict i).IsFixedVector
      (fun ij => positiveTensorVector v r ij.1 * w' ij.2) := by
    rw [← tensor_restrict]
    exact isFixedVector_tensor_of_opposite_characters
      ((ρ.positiveTensorPower r).restrict i) (σ.restrict i) ((r + 1) • χ) hpow hwm'
  refine nonempty_kernelRepresentation_of_fixedTensor i hN
    (ρ.positiveTensorPower r) σ (positiveTensorVector v r) w'
    (positiveTensorDiagonal j r) s (positiveTensorVector_diagonal v j hv r) hw' hfixed ?_
  intro T x hx
  exact hline T x ((positiveTensorPower_preserves_line_iff ρ v j hv r T x).1 hx)

/-- An actual ambient representation containing the inverse of a positive multiple
of the specified subgroup character. The degree is always `exponentPred + 1`. -/
structure InverseMultipleNormalCharacterVector (i : H ⟶ G) (χ : rationalCharacters H) where
  exponentPred : ℕ
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  vector : Fin dimension → k
  nonzero : vector ≠ 0
  character_mem : vector ∈
    (representation.restrict i).characterSpace (-((exponentPred + 1) • χ))

/-- The inverse-multiple occurrence property for normal-subgroup character vectors. -/
def HasInverseMultipleNormalCharacters (i : H ⟶ G) : Prop :=
  ∀ (a : ℕ) (ρ : MatrixRepresentation G (Fin (a + 1)))
    (χ : rationalCharacters H) (v : Fin (a + 1) → k),
      v ≠ 0 → v ∈ (ρ.restrict i).characterSpace χ →
        Nonempty (InverseMultipleNormalCharacterVector i χ)

/-- A closed normal subgroup is an exact represented kernel provided its occurring
characters satisfy inverse positive multiple occurrence. -/
theorem nonempty_kernelRepresentation_of_normal_closed_inverse_multiples
    [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (hInverse : HasInverseMultipleNormalCharacters i) :
    Nonempty (KernelRepresentation i) := by
  classical
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
  obtain ⟨D⟩ := hInverse a ρ χ (Pi.single j 1) hne hv
  refine nonempty_kernelRepresentation_of_inverse_multiple i hN ρ χ
    (Pi.single j 1) j (Pi.single_eq_same _ _) hv ?_
    D.exponentPred D.representation D.vector D.nonzero D.character_mem
  intro T x hx
  apply (hρ T x).2
  simpa only [scalarMap_single] using hx

/-- Choose the exact-kernel representation from inverse-multiple occurrence. -/
def normalKernelRepresentationOfInverseMultiples [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (hInverse : HasInverseMultipleNormalCharacters i) : KernelRepresentation i :=
  Classical.choice
    (nonempty_kernelRepresentation_of_normal_closed_inverse_multiples i hc hN hInverse)

end Langlands.GroupScheme.MatrixRepresentation
