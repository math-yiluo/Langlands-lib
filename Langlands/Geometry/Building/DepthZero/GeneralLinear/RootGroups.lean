import Langlands.Geometry.Building.DepthZero.GeneralLinear.Transvection
import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.GeneralLinearLatticeCentralizer
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints

/-!
# Root groups of the diagonal torus of `GL_N`

For a field `F` and the diagonal torus `D_N → GL_N` over `F`, the relative roots are the
characters `e_k - e_l` with `k ≠ l` (`relativeRoots_diagonalTorus`). This module shows that the
rational points of the relative root subgroup of `e_k - e_l` are elementary transvections
`1 + t E_{kl}`: such a point lies in the dynamic unipotent subgroups of the cocharacters with
weights `e_k` and `-e_l`, which are block unipotent subgroups of `GL_N`
(`unipotent_diagonalCocharacter`), and the two block unipotent subgroups meet in the
transvections at `(k, l)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable (F : Type u) [Field F] (N : ℕ)

/-- The split torus `𝔾_m^N` indexed by `ULift (Fin N)`, the source of the diagonal torus. -/
abbrev diagonalSplitTorus : CommGroupScheme (Spec (CommRingCat.of F)) :=
  splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift.{u} (Fin N))

/-- The diagonal torus of `GL_N` over `F`. -/
abbrev diagTorus : (diagonalSplitTorus F N).toGrp ⟶ GeneralLinear.groupScheme (Fin N)
    (CommRingCat.of F) :=
  GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of F)

variable {F N}

/-- The character `e_k - e_l` of the diagonal torus. -/
def rootCharacter (k l : Fin N) : characterLattice (diagonalSplitTorus F N) :=
  (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).symm
    (Pi.single ⟨k⟩ 1 - Pi.single ⟨l⟩ 1)

theorem characterLatticeEquiv_rootCharacter (k l : Fin N) :
    splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N)) (rootCharacter (F := F) k l) =
      Pi.single ⟨k⟩ 1 - Pi.single ⟨l⟩ 1 :=
  AddEquiv.apply_symm_apply _ _

theorem rootCharacter_mem_relativeRoots {k l : Fin N} (hkl : k ≠ l) :
    rootCharacter (F := F) k l ∈ relativeRoots (diagTorus F N) := by
  rw [diagTorus, GeneralLinear.relativeRoots_diagonalTorus]
  exact ⟨k, l, hkl, characterLatticeEquiv_rootCharacter k l⟩

/-- Every relative root of the diagonal torus is some `e_k - e_l` with `k ≠ l`. -/
theorem exists_eq_rootCharacter {a : characterLattice (diagonalSplitTorus F N)}
    (ha : a ∈ relativeRoots (diagTorus F N)) :
    ∃ k l : Fin N, k ≠ l ∧ a = rootCharacter k l := by
  rw [diagTorus, GeneralLinear.relativeRoots_diagonalTorus] at ha
  obtain ⟨k, l, hkl, h⟩ := ha
  refine ⟨k, l, hkl, ?_⟩
  apply (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).injective
  rw [h, characterLatticeEquiv_rootCharacter]

/-- The rational points of `GL_N` over `F` as invertible matrices. -/
abbrev toMatrixGL : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)) ≃*
    GL (Fin N) F :=
  GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)

/-- The matrix entries of a rational point are the images of its section entries. -/
theorem toMatrixGL_apply (g : rationalPoints (GeneralLinear.groupScheme (Fin N)
    (CommRingCat.of F))) (p q : Fin N) :
    ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p q =
      GeneralLinear.globalSectionsEquiv (CommRingCat.of F)
        (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) g p q) :=
  rfl

/-- A rational point in the block unipotent subgroup of the weights `e` has the entries of the
identity matrix at all positions `(p, q)` with `e p ≤ e q`. -/
theorem toMatrixGL_apply_of_mem_unipotent (e : Fin N → ℤ)
    {g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))}
    (hg : g ∈ (Dynamic.unipotent (GeneralLinear.diagonalCocharacter (Fin N)
      (CommRingCat.of F) e)).carrier (Over.mk (𝟙 _))) {p q : Fin N} (hpq : e p ≤ e q) :
    ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p q =
      (1 : Matrix (Fin N) (Fin N) F) p q := by
  rw [GeneralLinear.unipotent_diagonalCocharacter] at hg
  have h := (GeneralLinear.mem_blockUnipotent e).1 hg p q hpq
  rw [toMatrixGL_apply, h]
  by_cases hpq' : p = q
  · subst hpq'
    simp
  · simp [one_apply_ne hpq']

/-- The diagonal-torus point formula, in the form used by
`GeneralLinear.cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points`. -/
theorem diagTorus_points (U : Over (Spec (CommRingCat.of F)))
    (t : U ⟶ (splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin N))).X) :
    (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of F) U (t ≫ (diagTorus F N).hom.hom) :
        Matrix (Fin N) (Fin N) Γ(U.left, ⊤)) =
      Matrix.diagonal fun j =>
        ((splitTorus.pointsEquiv (ULift.{u} (Fin N)) U t (ULift.up j) : (Γ(U.left, ⊤))ˣ) :
          Γ(U.left, ⊤)) :=
  GeneralLinear.pointsEquiv_diagonalTorus_val t

/-- A rational point of the root subgroup of `a` lies in the block unipotent subgroup of the
weights of every cocharacter pairing positively with `a`. -/
theorem toMatrixGL_apply_of_mem_rootGroupPoints {a : characterLattice (diagonalSplitTorus F N)}
    (m : ULift.{u} (Fin N) → ℤ)
    (hm : 0 < latticePairing (diagonalSplitTorus F N) a
      ((splitTorus.cocharacterLatticeEquiv F (ULift.{u} (Fin N))).symm m))
    {g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))}
    (hg : g ∈ rootGroupPoints (diagTorus F N) a) {p q : Fin N} (hpq : m ⟨p⟩ ≤ m ⟨q⟩) :
    ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p q =
      (1 : Matrix (Fin N) (Fin N) F) p q := by
  have hU := RelativeRoot.subgroup_le_dynamicUnipotent (diagTorus F N) _ hm (Over.mk (𝟙 _)) hg
  rw [GeneralLinear.cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points F
    (diagTorus F N) diagTorus_points] at hU
  refine toMatrixGL_apply_of_mem_unipotent _ hU ?_
  simpa only [AddEquiv.apply_symm_apply] using hpq

theorem latticePairing_rootCharacter (k l : Fin N) (m : ULift.{u} (Fin N) → ℤ) :
    latticePairing (diagonalSplitTorus F N) (rootCharacter k l)
        ((splitTorus.cocharacterLatticeEquiv F (ULift.{u} (Fin N))).symm m) =
      m ⟨k⟩ - m ⟨l⟩ := by
  rw [splitTorus.latticePairing_eq_sum, characterLatticeEquiv_rootCharacter]
  simp only [AddEquiv.apply_symm_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single ⟨k⟩, Finset.sum_eq_single ⟨l⟩]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/-- **Root groups of the diagonal torus.** A rational point of the root subgroup of `e_k - e_l`
is an elementary transvection `1 + t E_{kl}`. -/
theorem exists_eq_transvectionGL_of_mem_rootGroupPoints {k l : Fin N} (hkl : k ≠ l)
    {g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))}
    (hg : g ∈ rootGroupPoints (diagTorus F N) (rootCharacter k l)) :
    ∃ t : F, toMatrixGL g = transvectionGL hkl t := by
  classical
  have hkl' : (⟨k⟩ : ULift.{u} (Fin N)) ≠ ⟨l⟩ := fun h => hkl (congrArg ULift.down h)
  -- the cocharacter with weights `e_k`
  have h₁ : ∀ p q : Fin N, (p ≠ k ∨ q = k) →
      ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p q =
        (1 : Matrix (Fin N) (Fin N) F) p q := by
    intro p q hpq
    refine toMatrixGL_apply_of_mem_rootGroupPoints (Pi.single ⟨k⟩ 1) ?_ hg ?_
    · rw [latticePairing_rootCharacter]
      simp [Pi.single_eq_of_ne hkl'.symm]
    · rcases hpq with hp | hq
      · have : (⟨p⟩ : ULift.{u} (Fin N)) ≠ ⟨k⟩ := fun h => hp (congrArg ULift.down h)
        rw [Pi.single_eq_of_ne this]
        by_cases hq : q = k
        · subst hq
          simp
        · have : (⟨q⟩ : ULift.{u} (Fin N)) ≠ ⟨k⟩ := fun h => hq (congrArg ULift.down h)
          rw [Pi.single_eq_of_ne this]
      · subst hq
        simp only [Pi.single_eq_same]
        by_cases hp : p = q
        · subst hp
          simp
        · have : (⟨p⟩ : ULift.{u} (Fin N)) ≠ ⟨q⟩ := fun h => hp (congrArg ULift.down h)
          rw [Pi.single_eq_of_ne this]
          norm_num
  -- the cocharacter with weights `-e_l`
  have h₂ : ∀ p q : Fin N, (q ≠ l ∨ p = l) →
      ((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) p q =
        (1 : Matrix (Fin N) (Fin N) F) p q := by
    intro p q hpq
    refine toMatrixGL_apply_of_mem_rootGroupPoints (-Pi.single ⟨l⟩ 1) ?_ hg ?_
    · rw [latticePairing_rootCharacter]
      simp [Pi.single_eq_of_ne hkl']
    · rcases hpq with hq | hp
      · have : (⟨q⟩ : ULift.{u} (Fin N)) ≠ ⟨l⟩ := fun h => hq (congrArg ULift.down h)
        simp only [Pi.neg_apply, Pi.single_eq_of_ne this, neg_zero, Left.neg_nonpos_iff]
        by_cases hp : p = l
        · subst hp
          simp
        · have : (⟨p⟩ : ULift.{u} (Fin N)) ≠ ⟨l⟩ := fun h => hp (congrArg ULift.down h)
          rw [Pi.single_eq_of_ne this]
      · subst hp
        simp only [Pi.neg_apply, Pi.single_eq_same]
        by_cases hq : q = p
        · subst hq
          simp
        · have : (⟨q⟩ : ULift.{u} (Fin N)) ≠ ⟨p⟩ := fun h => hq (congrArg ULift.down h)
          rw [Pi.single_eq_of_ne this]
          norm_num
  refine ⟨((toMatrixGL g : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) k l, ?_⟩
  ext p q : 2
  rw [coe_transvectionGL, Matrix.add_apply, single_apply]
  by_cases hpq : p = k ∧ q = l
  · obtain ⟨rfl, rfl⟩ := hpq
    simp [one_apply_ne hkl]
  · have hne : ¬(k = p ∧ l = q) := fun h => hpq ⟨h.1.symm, h.2.symm⟩
    simp only [hne, ↓reduceIte, add_zero]
    by_cases hp : p = k
    · subst hp
      have hq : q ≠ l := fun h => hpq ⟨rfl, h⟩
      exact h₂ p q (Or.inl hq)
    · exact h₁ p q (Or.inl hp)

end Langlands.Geometry.Building.GeneralLinearParahoric
