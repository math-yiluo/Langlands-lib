import Langlands.AlgebraicGeometry.Picard.FiniteWeilBaseChange
import Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyStatement
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.GroupScheme.FiniteEtaleCharacterPoints
import Langlands.GroupScheme.Cartier.AlgClosedCharacterSeparation

/-! # Geometric-point finite Weil nondegeneracy from field Cartier bijectivity -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- Characters of a finite étale group scheme over an algebraically closed field, killed by
an integer invertible in the field, separate its rational points. -/
def FiniteEtaleCharacterSeparationStatement : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (G : CommGroupScheme (Spec (CommRingCat.of K)))
    [IsFinite G.X.hom] [Etale G.X.hom] (n : ℕ), (n : K) ≠ 0 →
    GroupScheme.multiplication G.toGrp (n : ℤ) = 1 →
    ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, x ≠ 1 →
      ∃ χ : (Cartier.characters G).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))),
        Cartier.characterEvaluation χ x ≠ 1

section Field

variable (field : FieldDualKernelCharacterBijectiveStatement.{u})
  (separation : FiniteEtaleCharacterSeparationStatement.{u})
  (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {K : Type u} [Field K] [IsAlgClosed K] (B : AbelianScheme (Spec (CommRingCat.of K)))
  (hB : HasDualScheme B)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (n : ℕ) (hn : (n : K) ≠ 0)

local notation "GB" => Langlands.CommGroupScheme.toGrp
  (dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB stability composition
    unitCoherence associativity comparison symmetry)
local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hB MB evaluationB
local notation "chi" => dualTorsionCharacter preservation composition unitCoherence
  associativity comparison symmetry stability hB MB evaluationB
local notation "ki" => relativeDualMultiplicationKernelIso preservation composition
  unitCoherence associativity comparison symmetry stability hB MB evaluationB ((n : ℕ) : ℤ)

omit [IsAlgClosed K] in
/-- A pairing value vanishes exactly when the character evaluation is trivial. -/
lemma finiteWeilLevelBilinearMap_eq_zero_iff {T : Over (Spec (CommRingCat.of K))}
    (x : GroupScheme.Tate.Level B.toGrp T n) (y : GroupScheme.Tate.Level GB T n) :
    levelPair n T x y = 0 ↔
      Cartier.characterEvaluation (chi n (GroupScheme.Tate.kernelLift GB T n y))
        (GroupScheme.Tate.kernelLift B.toGrp T n x) = 1 := by
  have hc := finiteWeilLevelBilinearMap_coe B preservation composition unitCoherence
    associativity comparison symmetry stability hB MB evaluationB n T x y
  rw [← map_eq_one_iff _ (Gm.pointsEquiv _ T).injective, ← hc, OneMemClass.coe_eq_one,
    toMul_eq_one]

include field separation hn in
/-- Over an algebraically closed field in which `n` is nonzero, the actual finite Weil pairing
on rational points has trivial left and right kernels. -/
theorem finiteWeilLevelBilinearMap_nondegenerate_of_field :
    (∀ x, (∀ y, levelPair n (Over.mk (𝟙 (Spec (CommRingCat.of K)))) x y = 0) → x = 0) ∧
      (∀ y, (∀ x, levelPair n (Over.mk (𝟙 (Spec (CommRingCat.of K)))) x y = 0) → y = 0) := by
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let G := kernelCommGroupScheme (multiplication B (n : ℤ))
  have : IsFinite G.X.hom := multiplicationKernel_isFinite_of_ne_zero B n hn
  have : Etale G.X.hom := multiplicationKernel_etale_of_ne_zero B n hn
  have hG : GroupScheme.multiplication G.toGrp (n : ℤ) = 1 :=
    torsion_multiplication_eq_one B.toGrp (n : ℤ)
  have hiso : IsIsogeny (multiplication B (n : ℤ)) :=
    multiplication_isIsogeny_of_ne_zero B n hn
  have hbij := field preservation composition unitCoherence associativity comparison symmetry
    stability K B B hB hB MB evaluationB MB evaluationB (multiplication B (n : ℤ)) hiso T
  have hlift (x : GroupScheme.Tate.Level B.toGrp T n)
      (h : GroupScheme.Tate.kernelLift B.toGrp T n x = 1) : x = 0 := by
    have hx := (GroupScheme.Tate.kernelLevelEquiv B.toGrp T n).apply_symm_apply x
    rw [← hx]
    change GroupScheme.Tate.kernelLevelEquiv B.toGrp T n
      (Additive.ofMul (GroupScheme.Tate.kernelLift B.toGrp T n x)) = 0
    rw [h, ofMul_one, map_zero]
  have hkx (x' : T ⟶ G.X) : ∃ x, GroupScheme.Tate.kernelLift B.toGrp T n x = x' :=
    ⟨GroupScheme.Tate.kernelLevelEquiv B.toGrp T n (Additive.ofMul x'), by
      simp [GroupScheme.Tate.kernelLift]⟩
  constructor
  · intro x hx
    by_contra hne
    have hx1 : GroupScheme.Tate.kernelLift B.toGrp T n x ≠ 1 := fun h ↦ hne (hlift x h)
    obtain ⟨χ, hχ⟩ := separation G n hn hG (GroupScheme.Tate.kernelLift B.toGrp T n x) hx1
    obtain ⟨z, hz⟩ := hbij.2 χ
    let y := GroupScheme.Tate.kernelLevelEquiv GB T n
      (Additive.ofMul (z ≫ (ki).hom.hom.hom))
    have hy : GroupScheme.Tate.kernelLift GB T n y = z ≫ (ki).hom.hom.hom := by
      simp [y, GroupScheme.Tate.kernelLift]
    have hz' : (z ≫ (ki).hom.hom.hom) ≫ (ki).inv.hom.hom = z := by
      rw [Category.assoc, ← Grp.comp_hom_hom, (ki).hom_inv_id, Grp.id_hom_hom,
        Category.comp_id]
    have hχy : chi n (GroupScheme.Tate.kernelLift GB T n y) = χ := by
      rw [hy]
      unfold dualTorsionCharacter
      rw [hz']
      exact hz
    apply hχ
    rw [← hχy]
    exact (finiteWeilLevelBilinearMap_eq_zero_iff preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB n x y).mp (hx y)
  · intro y hy
    have hχ : ∀ x' : T ⟶ G.X,
        Cartier.characterEvaluation (chi n (GroupScheme.Tate.kernelLift GB T n y)) x' = 1 := by
      intro x'
      obtain ⟨x, rfl⟩ := hkx x'
      exact (finiteWeilLevelBilinearMap_eq_zero_iff preservation composition unitCoherence
        associativity comparison symmetry stability B hB MB evaluationB n x y).mp (hy x)
    have h0 := characters_eq_zero_of_evaluation (G := G) n hn hG _ hχ
    have h1 : GroupScheme.Tate.kernelLift GB T n y ≫ (ki).inv.hom.hom =
        1 ≫ (ki).inv.hom.hom := by
      apply hbij.1
      change chi n (GroupScheme.Tate.kernelLift GB T n y) = chi n 1
      rw [h0, dualTorsionCharacter_one]
    have h2 : GroupScheme.Tate.kernelLift GB T n y = 1 := by
      have h3 := congrArg (fun w ↦ w ≫ (ki).hom.hom.hom) h1
      simp only [Category.assoc] at h3
      rw [← Grp.comp_hom_hom, (ki).inv_hom_id, Grp.id_hom_hom] at h3
      exact (Category.comp_id _).symm.trans (h3.trans (Category.comp_id _))
    have hyy := (GroupScheme.Tate.kernelLevelEquiv GB T n).apply_symm_apply y
    rw [← hyy]
    change GroupScheme.Tate.kernelLevelEquiv GB T n
      (Additive.ofMul (GroupScheme.Tate.kernelLift GB T n y)) = 0
    rw [h2, ofMul_one, map_zero]

end Field

/-- Field Cartier bijectivity and character separation imply geometric-point nondegeneracy of
the actual finite Weil pairing. -/
theorem geometricFiniteWeilNondegeneracy_of_field
    (field : FieldDualKernelCharacterBijectiveStatement.{u})
    (separation : FiniteEtaleCharacterSeparationStatement.{u}) :
    GeometricFiniteWeilNondegeneracyStatement.{u} := by
  intro preservation _square universality composition unitCoherence associativity comparison
    symmetry stability _compatibility S _ A hA _geometryA MA evaluationA K _ _ s n hn
  let hA' : HasDualScheme ((baseChange s).obj A) := hasDualScheme_baseChange universality s A hA
  obtain ⟨MA', ⟨evaluationA'⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((RigidifiedLineBundle.forget _).obj (poincareFamily ((baseChange s).obj A) hA'))
  have hT : (Over.map s).obj (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = Over.mk s :=
    congrArg Over.mk (Category.id_comp s)
  have key := finiteWeilLevelBilinearMap_nondegenerate_baseChange_iff s A preservation
    composition unitCoherence associativity comparison symmetry stability universality hA MA
    evaluationA hA' MA' evaluationA' n (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  rw [hT] at key
  exact key.mp (finiteWeilLevelBilinearMap_nondegenerate_of_field field separation
    preservation composition unitCoherence associativity comparison symmetry stability
    ((baseChange s).obj A) hA' MA' evaluationA' n hn)

/-- The separation hypothesis holds, by `exists_characterEvaluation_ne_one_of_isAlgClosed`. -/
theorem finiteEtaleCharacterSeparation : FiniteEtaleCharacterSeparationStatement.{u} := by
  intro K _ _ G _ _ n hn hG x hx
  exact Cartier.exists_characterEvaluation_ne_one_of_isAlgClosed G n hn hG x hx

/-- Field Cartier bijectivity alone implies geometric-point nondegeneracy of the actual finite
Weil pairing. -/
theorem geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective
    (field : FieldDualKernelCharacterBijectiveStatement.{u}) :
    GeometricFiniteWeilNondegeneracyStatement.{u} :=
  geometricFiniteWeilNondegeneracy_of_field field finiteEtaleCharacterSeparation

end Langlands.AbelianScheme
