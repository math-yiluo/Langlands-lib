import Langlands.ClassFieldTheory.Local.UnramifiedInvariant
import Langlands.Galois.Local.AbsoluteProof
import Langlands.Galois.Local.SeparableUnramifiedProof

/-! # Arithmetic Frobenius on finite unramified stages -/

noncomputable section

open IsLocalRing Langlands.LocalGalois Langlands.LocalGalois.Separable

namespace Langlands.ClassFieldTheory.Local

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance finiteFrobeniusNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteFrobeniusUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteFrobeniusComplete : CompleteSpace F := localNormedField_complete F
local instance finiteFrobeniusResidueFinite : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

variable (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E]

local notation "κ" => ResidueField (baseIntegers F)
local notation "κE" => ResidueField (extensionIntegers F E)

/-- The action on residues is faithful for a finite arithmetic-unramified
Galois extension. -/
theorem finiteUnramified_residueHom_injective (hE : ArithmeticUnramified F E) :
    Function.Injective (residueHom F E) := by
  let : IsGalois κ κE := isGalois_of_finite_base _ _
  apply ((residueHom_surjective F E).bijective_of_nat_card_le ?_).1
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    (arithmeticUnramified_iff_residue_finrank F E).mp hE]

/-- The actual residue Galois equivalence on a finite unramified stage. -/
def finiteUnramifiedResidueEquiv (hE : ArithmeticUnramified F E) :
    Gal(E/F) ≃* Gal(κE/κ) :=
  MulEquiv.ofBijective (residueHom F E)
    ⟨finiteUnramified_residueHom_injective F E hE, residueHom_surjective F E⟩

/-- Arithmetic Frobenius is the unique lift of the base residue cardinality
power automorphism. -/
def finiteUnramifiedFrobenius (hE : ArithmeticUnramified F E) : Gal(E/F) :=
  letI : Fintype κ := Fintype.ofFinite κ
  (finiteUnramifiedResidueEquiv F E hE).symm
    (FiniteField.frobeniusAlgEquivOfAlgebraic κ κE)

theorem finiteUnramifiedFrobenius_residue (hE : ArithmeticUnramified F E) (x : κE) :
    residueHom F E (finiteUnramifiedFrobenius F E hE) x = x ^ Nat.card κ := by
  let : Fintype κ := Fintype.ofFinite κ
  let e := finiteUnramifiedResidueEquiv F E hE
  change e (e.symm (FiniteField.frobeniusAlgEquivOfAlgebraic κ κE)) x = _
  rw [e.apply_symm_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Fintype.card_eq_nat_card]

theorem finiteUnramifiedFrobenius_generates (hE : ArithmeticUnramified F E) (σ : Gal(E/F)) :
    σ ∈ Subgroup.zpowers (finiteUnramifiedFrobenius F E hE) := by
  let : Fintype κ := Fintype.ofFinite κ
  let e := finiteUnramifiedResidueEquiv F E hE
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow κ κE).surjective (e σ)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(i.val : ℤ), e.injective ?_⟩
  change e (e.symm (FiniteField.frobeniusAlgEquivOfAlgebraic κ κE) ^ (i.val : ℤ)) = e σ
  simpa only [map_zpow, map_pow, MulEquiv.apply_symm_apply, zpow_natCast] using hi

/-- Cyclic coordinates with arithmetic Frobenius at the positive generator. -/
def finiteUnramifiedCyclicCoordinate (hE : ArithmeticUnramified F E) :
    Gal(E/F) ≃* Multiplicative (ZMod (Module.finrank F E)) :=
  (zmodMulEquivOfGenerator (finiteUnramifiedFrobenius_generates F E hE)
    (IsGalois.card_aut_eq_finrank F E)).symm

@[simp]
theorem cyclicCoordinateGenerator_finiteUnramified (hE : ArithmeticUnramified F E) :
    cyclicCoordinateGenerator (finiteUnramifiedCyclicCoordinate F E hE) =
      finiteUnramifiedFrobenius F E hE :=
  zmodMulEquivOfGenerator_apply_ofAdd_one (finiteUnramifiedFrobenius_generates F E hE)
    (IsGalois.card_aut_eq_finrank F E)

variable (M : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F M] [IsGalois F M]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction to a smaller finite unramified stage preserves arithmetic
Frobenius. -/
theorem restrictNormalHom_finiteUnramifiedFrobenius
    (h : E ≤ M) (hE : ArithmeticUnramified F E) (hM : ArithmeticUnramified F M) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (IntermediateField.inclusion h)
    AlgEquiv.restrictNormalHom E (finiteUnramifiedFrobenius F M hM) =
      finiteUnramifiedFrobenius F E hE := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (IntermediateField.inclusion h)
  let : IsScalarTower E M (SeparableClosure F) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let τ := finiteUnramifiedFrobenius F M hM
  let ρ := τ.liftNormal (SeparableClosure F)
  have hρM : ρ.restrictNormal M = τ := τ.restrict_liftNormal (SeparableClosure F)
  have hρE : ρ.restrictNormal E = τ.restrictNormal E :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E M ρ).trans
      (congrArg (fun g : Gal(M/F) => g.restrictNormal E) hρM)
  change τ.restrictNormal E = finiteUnramifiedFrobenius F E hE
  apply finiteUnramified_residueHom_injective F E hE
  apply AlgEquiv.ext
  intro x
  rw [finiteUnramifiedFrobenius_residue]
  obtain ⟨z, rfl⟩ := residue_surjective x
  let zM : extensionIntegers F M := ⟨IntermediateField.inclusion h z, by
    have hn := (spectralNorm.eq_of_tower (K := F) (L := SeparableClosure F)
      (IntermediateField.inclusion h (z : E))).trans
      (spectralNorm.eq_of_tower (K := F) (L := SeparableClosure F) (z : E)).symm
    exact hn.le.trans z.property⟩
  let iE := residueInclusion F (SeparableClosure F) E
  let iM := residueInclusion F (SeparableClosure F) M
  have hz : iE (residue _ z) = iM (residue _ zM) := by
    change residue _ (integerInclusion F (SeparableClosure F) E z) =
      residue _ (integerInclusion F (SeparableClosure F) M zM)
    congr 1
  have hres := residueHom_restrict F (SeparableClosure F) M ρ (residue _ zM)
  change iM (residueHom F M (ρ.restrictNormal M) (residue _ zM)) =
    residueHom F (SeparableClosure F) ρ (iM (residue _ zM)) at hres
  rw [hρM] at hres
  change iM (residueHom F M (finiteUnramifiedFrobenius F M hM) (residue _ zM)) = _ at hres
  rw [finiteUnramifiedFrobenius_residue, map_pow] at hres
  apply iE.injective
  change iE (residueHom F E (τ.restrictNormal E) (residue _ z)) = _
  rw [← hρE, residueHom_restrict, map_pow, hz]
  exact hres.symm

end Langlands.ClassFieldTheory.Local
