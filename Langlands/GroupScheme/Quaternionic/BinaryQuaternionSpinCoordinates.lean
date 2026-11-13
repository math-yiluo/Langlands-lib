import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinDiagonal
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Root-of-unity coordinates of the diagonal binary spin homomorphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.BinaryKernel

/-- Characters of the two-element lattice are exactly units whose square is one. -/
def characterRootsEquiv (R : Type v) [CommRing R] :
    (Multiplicative TwoLattice.{u} →* Rˣ) ≃* rootsOfUnity 2 R where
  toFun χ := ⟨characterUnit χ, (mem_rootsOfUnity 2 _).mpr (by
    rw [pow_two, characterUnit_mul])⟩
  invFun u := characterOfUnit u.val (by
    simpa only [pow_two] using (mem_rootsOfUnity 2 _).mp u.property)
  left_inv χ := by
    apply characterUnit_injective
    exact characterUnit_characterOfUnit _ _
  right_inv u := by
    apply Subtype.ext
    exact characterUnit_characterOfUnit _ _
  map_mul' χ ψ := Subtype.ext (map_mul characterUnit χ ψ)

@[simp] theorem characterRootsEquiv_val (R : Type v) [CommRing R]
    (χ : Multiplicative TwoLattice.{u} →* Rˣ) :
    (characterRootsEquiv R χ).val = characterUnit χ := rfl

@[simp] theorem characterUnit_characterRootsEquiv_symm
    (R : Type v) [CommRing R] (u : rootsOfUnity 2 R) :
    characterUnit ((characterRootsEquiv R).symm u : Multiplicative TwoLattice.{u} →* Rˣ) =
      u.val :=
  congrArg Subtype.val ((characterRootsEquiv.{u, v} R).apply_symm_apply u)

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The actual original μ₂ points on every test scheme, in square-root-of-one coordinates. -/
def rootsPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (muTwo (K := K)).X) ≃* rootsOfUnity 2 (BinaryScheme.coefficients T) :=
  (Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T).trans
    (characterRootsEquiv (BinaryScheme.coefficients T))

/-- The scalar norm-one point associated to a square root of one. -/
def rootScalarNormOne (hdim : Module.finrank K D = 4)
    (R : Type u) [CommRing R] [Algebra K R] :
    rootsOfUnity 2 R →* Langlands.CentralSimple.reducedNormOne K D R :=
  (scalarNormOne hdim R).comp (characterRootsEquiv R).symm.toMonoidHom

@[simp] theorem rootScalarNormOne_val (hdim : Module.finrank K D = 4)
    (R : Type u) [CommRing R] [Algebra K R] (u : rootsOfUnity 2 R) :
    (rootScalarNormOne hdim R u).val =
      Langlands.CentralSimple.normCoverScalarUnits K D R u.val := by
  change Langlands.CentralSimple.normCoverScalarUnits K D R
    (characterUnit ((characterRootsEquiv R).symm u)) = _
  rw [characterUnit_characterRootsEquiv_symm]

/-- The original diagonal point has exactly the scalar diagonal and scalar norm-one coordinates. -/
theorem diagonal_root_coordinates (hdim : Module.finrank K D = 4)
    (T : Over (Spec (CommRingCat.of K))) (u : rootsOfUnity 2 (BinaryScheme.coefficients T)) :
    BinaryScheme.pointsEquiv T
      (((rootsPointsEquiv T).symm u) ≫ (diagonal hdim).hom.hom) =
      (BinaryAction.diagonalSL u.val,
        rootScalarNormOne hdim (BinaryScheme.coefficients T) u) := by
  rw [diagonal_points, diagonalPoints_coordinates]
  change characterProduct hdim (BinaryScheme.coefficients T)
    ((Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T)
      ((Diagonalizable.characterPointsEquiv (CommRingCat.of K) TwoLattice.{u} T).symm
        ((characterRootsEquiv (BinaryScheme.coefficients T)).symm u))) = _
  rw [MulEquiv.apply_symm_apply]
  apply Prod.ext
  · change BinaryAction.diagonalSL (characterUnit
      ((characterRootsEquiv (BinaryScheme.coefficients T)).symm u)) = _
    rw [characterUnit_characterRootsEquiv_symm]
  · rfl

/-- The first projection of the original diagonal root point is the actual upper cocharacter. -/
theorem diagonal_root_fst (hdim : Module.finrank K D = 4)
    (T : Over (Spec (CommRingCat.of K))) (u : rootsOfUnity 2 (BinaryScheme.coefficients T)) :
    (((rootsPointsEquiv T).symm u) ≫ (diagonal hdim).hom.hom) ≫ fst _ _ =
      ((Gm.pointsEquiv (Spec (CommRingCat.of K)) T).symm u.val) ≫
        (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K)).hom.hom := by
  apply (SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T).injective
  change (BinaryScheme.pointsEquiv T
    (((rootsPointsEquiv T).symm u) ≫ (diagonal hdim).hom.hom)).1 = _
  rw [diagonal_root_coordinates, SpecialLinear.BinaryRoot.pointsEquiv_upperCocharacter,
    MulEquiv.apply_symm_apply]
  rfl

/-- The second projection of the original diagonal root point is the scalar norm-one point. -/
theorem diagonal_root_snd (hdim : Module.finrank K D = 4)
    (T : Over (Spec (CommRingCat.of K))) (u : rootsOfUnity 2 (BinaryScheme.coefficients T)) :
    (((rootsPointsEquiv T).symm u) ≫ (diagonal hdim).hom.hom) ≫ snd _ _ =
      (CentralSimpleUnits.normOnePointsEquiv K D T).symm
        (rootScalarNormOne hdim (BinaryScheme.coefficients T) u) := by
  apply (CentralSimpleUnits.normOnePointsEquiv K D T).injective
  change (BinaryScheme.pointsEquiv T
    (((rootsPointsEquiv T).symm u) ≫ (diagonal hdim).hom.hom)).2 = _
  rw [diagonal_root_coordinates, MulEquiv.apply_symm_apply]

end Langlands.GroupScheme.Quaternionic.BinaryKernel

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- On all tests the diagonal spin morphism is μ(u)ψ(u·1), with the actual point models. -/
theorem diagonalSpin_root_points
    (T : Over (Spec (CommRingCat.of K))) (u : rootsOfUnity 2 (BinaryScheme.coefficients T)) :
    ((BinaryKernel.rootsPointsEquiv T).symm u) ≫
        (diagonalSpin σ hdim hsym h hπ hsc).hom.hom =
      (((Gm.pointsEquiv (Spec (CommRingCat.of K)) T).symm u.val) ≫
          (scalar σ hdim hsym h hπ hsc).hom.hom) *
        (((CentralSimpleUnits.normOnePointsEquiv K D T).symm
            (BinaryKernel.rootScalarNormOne hdim (BinaryScheme.coefficients T) u)) ≫
          (normOne σ hdim hsym h hπ hsc).hom.hom) := by
  rw [diagonalSpin, Grp.comp_hom_hom, ← Category.assoc, productHom_points,
    BinaryKernel.diagonal_root_fst, BinaryKernel.diagonal_root_snd]
  congr 1

/-- Diagonal monomorphy and coverage of the spin kernel by the combined image give
the unique square-root-of-one parametrization, on every original test scheme. -/
theorem existsUnique_root_of_kernel
    (hm : Mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom)
    (hcover : SubgroupFunctor.range (kernelι π) ≤
      SubgroupFunctor.range (productHom σ hdim hsym h hπ hsc))
    (T : Over (Spec (CommRingCat.of K))) (s : T ⟶ S.X)
    (hs : s ≫ π.hom.hom = 1) :
    ∃! u : rootsOfUnity 2 (BinaryScheme.coefficients T),
      ((BinaryKernel.rootsPointsEquiv T).symm u) ≫
        (diagonalSpin σ hdim hsym h hπ hsc).hom.hom = s := by
  let := hm
  have hk : s ∈ (SubgroupFunctor.range (kernelι π)).carrier T :=
    (mem_range_kernelι_iff π s).mpr hs
  have hd : s ∈ (SubgroupFunctor.range (diagonalSpin σ hdim hsym h hπ hsc)).carrier T := by
    rw [diagonalSpin_range]
    exact ⟨hcover T hk, hk⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hd
  refine ⟨BinaryKernel.rootsPointsEquiv T x, ?_, ?_⟩
  · change ((BinaryKernel.rootsPointsEquiv T).symm
      (BinaryKernel.rootsPointsEquiv T x)) ≫
        (diagonalSpin σ hdim hsym h hπ hsc).hom.hom = s
    rw [MulEquiv.symm_apply_apply, hx]
  · intro v hv
    have hvx : (BinaryKernel.rootsPointsEquiv T).symm v = x := by
      apply (cancel_mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom).mp
      exact hv.trans hx.symm
    simpa only [MulEquiv.apply_symm_apply] using
      congrArg (BinaryKernel.rootsPointsEquiv T) hvx

end Langlands.GroupScheme.Quaternionic.BinarySpinLift
