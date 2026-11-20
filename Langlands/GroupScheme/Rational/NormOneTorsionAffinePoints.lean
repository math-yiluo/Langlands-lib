import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Actual tensor-unit points of norm-one torsion -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

open Langlands.Algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F B : Type u} [Field F] [Field B] [Algebra F B] [FiniteDimensional F B]

local notation "A" => CommRingCat.of F
local notation "W" => groupScheme A B
local notation "N" => normOne A B

/-- The scheme of `n`-torsion in the actual norm-one Weil group. -/
def normOneTorsion (F B : Type u) [Field F] [Field B] [Algebra F B] [FiniteDimensional F B]
    (n : ℕ) : GroupScheme (Spec (CommRingCat.of F)) :=
  letI := (normOneCommGroupScheme (CommRingCat.of F) B).comm
  torsion (normOne (CommRingCat.of F) B) (n : ℤ)

private abbrev affineTest (R : CommAlgCat.{u} A) := (algSpec A).obj (op R)

/-- The actual group scheme norm agrees on affine tests with the determinant norm of
original tensor units. -/
theorem norm_affineUnits (R : CommAlgCat.{u} A) (x : (W).affinePoints R) :
    Gm.affinePointsEquiv (affineTest R).hom (x ≫ (norm A B).hom.hom) =
      tensorNormUnits F B R (affineUnitsEquiv A B R x) := by
  let U := affineTest R
  let γ := Corepresented.affineSectionsIso R
  have h := Corepresented.map_affineSectionsIso_pointsEquiv (functor A B)
    (corepresentableBy A B) R x
  change Units.map (Algebra.TensorProduct.lTensor (S := B) B γ.hom.hom).toMonoidHom
    (pointsEquiv A B U x) = affineUnitsEquiv A B R x at h
  rw [← h, tensorNormUnits_naturality]
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    (Gm.pointsEquiv (Spec A) U (x ≫ (norm A B).hom.hom)).val = _
  rw [norm_points A B U x]
  exact (DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom R) _).symm

/-- The actual composite of the torsion and norm-kernel inclusions. -/
def normOneTorsionInclusion (n : ℕ) : normOneTorsion F B n ⟶ W :=
  letI := (normOneCommGroupScheme A B).comm
  torsionι N (n : ℤ) ≫ normOneι A B

/-- The subgroup of tensor units with norm one and `n`-th power one. -/
def normOneTorsionUnits (n : ℕ) (R : CommAlgCat.{u} A) : Subgroup ((B ⊗[F] R)ˣ) :=
  rootsOfUnity n (B ⊗[F] R) ⊓ (tensorNormUnits F B R).ker

/-- On an affine test, the torsion inclusion followed by the tensor-unit equivalence. -/
def normOneTorsionUnitMap (n : ℕ) (R : CommAlgCat.{u} A) :
    (normOneTorsion F B n).affinePoints R →* (B ⊗[F] R)ˣ :=
  (affineUnitsEquiv A B R).toMonoidHom.comp
    ((normOneTorsion F B n).affinePointsTarget (normOneTorsionInclusion n) R)

private theorem normOneTorsionUnitMap_injective (n : ℕ) (R : CommAlgCat.{u} A) :
    Function.Injective (normOneTorsionUnitMap (B := B) n R) := by
  let _ := (normOneCommGroupScheme A B).comm
  intro x y h
  have he := (affineUnitsEquiv A B R).injective h
  change x ≫ (normOneTorsionInclusion (F := F) (B := B) n).hom.hom =
    y ≫ (normOneTorsionInclusion (F := F) (B := B) n).hom.hom at he
  rw [normOneTorsionInclusion, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc] at he
  exact (cancel_mono (torsionι N (n : ℤ)).hom.hom).mp
    ((cancel_mono (kernelι (norm A B)).hom.hom).mp he)

private theorem normOneTorsionUnitMap_mem (n : ℕ) (R : CommAlgCat.{u} A)
    (x : (normOneTorsion F B n).affinePoints R) :
    normOneTorsionUnitMap n R x ∈ normOneTorsionUnits (B := B) n R := by
  let _ := (normOneCommGroupScheme A B).comm
  let i := torsionι N (n : ℤ)
  let y := x ≫ i.hom.hom
  have hy : y ^ n = 1 := by
    have ht := (mem_torsionPoints N (n : ℤ) (affineTest R) _).mp
      (torsionPointsEquiv N (n : ℤ) (affineTest R) x).property
    simpa only [torsionPointsEquiv_val, zpow_natCast] using ht
  let j := ((N).affinePointsTarget (normOneι A B) R)
  change affineUnitsEquiv A B R (j y) ∈ rootsOfUnity n (B ⊗[F] R) ⊓ (tensorNormUnits F B R).ker
  refine ⟨(mem_rootsOfUnity n _).mpr ?_, ?_⟩
  · rw [← map_pow, ← map_pow, hy, map_one, map_one]
  · change tensorNormUnits F B R (affineUnitsEquiv A B R (j y)) = 1
    rw [← norm_affineUnits]
    have hker := (kernelPointsEquiv (norm A B) (affineTest R) y).property
    change j y ≫ (norm A B).hom.hom = 1 at hker
    rw [hker, map_one]

/-- On affine tests the actual norm-one torsion is the corresponding subgroup of tensor units. -/
def normOneTorsionAffineEquiv (n : ℕ) (R : CommAlgCat.{u} A) :
    (normOneTorsion F B n).affinePoints R ≃* normOneTorsionUnits (B := B) n R := by
  letI := (normOneCommGroupScheme A B).comm
  let f := (normOneTorsionUnitMap (B := B) n R).codRestrict _ (normOneTorsionUnitMap_mem n R)
  apply MulEquiv.ofBijective f
  refine ⟨fun x y h => normOneTorsionUnitMap_injective n R (congrArg Subtype.val h), ?_⟩
  intro t
  let q := affineUnitsEquiv A B R
  let v := q.symm t.val
  have hvN : tensorNormUnits F B R (q v) = 1 := by
    rw [show q v = t.val from q.apply_symm_apply _]
    exact t.property.2
  have hv : v ≫ (norm A B).hom.hom = 1 := by
    apply (Gm.affinePointsEquiv (affineTest R).hom).injective
    rw [norm_affineUnits, map_one]
    exact hvN
  let k := kernelPointsEquiv (norm A B) (affineTest R)
  let y := k.symm ⟨v, hv⟩
  have hy : y ≫ (kernelι (norm A B)).hom.hom = v :=
    congrArg Subtype.val (k.apply_symm_apply ⟨v, hv⟩)
  have hyPow : y ^ n = 1 := by
    apply (cancel_mono (kernelι (norm A B)).hom.hom).mp
    simp only [MonObj.pow_comp, MonObj.one_comp]
    change (y ≫ (kernelι (norm A B)).hom.hom) ^ n = 1
    rw [hy]
    apply q.injective
    rw [map_pow, map_one, show q v = t.val from q.apply_symm_apply _]
    exact (mem_rootsOfUnity n _).mp t.property.1
  obtain ⟨x, hx, _⟩ := (existsUnique_torsion_lift_iff N (n : ℤ) (affineTest R) y).mpr
    (by simpa only [zpow_natCast] using hyPow)
  refine ⟨x, Subtype.ext ?_⟩
  change q (x ≫ (normOneTorsionInclusion (F := F) (B := B) n).hom.hom) = t.val
  rw [normOneTorsionInclusion, Grp.comp_hom_hom, ← Category.assoc, hx]
  change q (y ≫ (kernelι (norm A B)).hom.hom) = t.val
  rw [hy]
  exact q.apply_symm_apply _

@[simp]
theorem normOneTorsionAffineEquiv_val (n : ℕ) (R : CommAlgCat.{u} A)
    (x : (normOneTorsion F B n).affinePoints R) :
    (normOneTorsionAffineEquiv n R x).val = normOneTorsionUnitMap n R x := rfl

/-- The tensor-unit map is compatible with every change of affine coefficients. -/
theorem normOneTorsionUnitMap_naturality (n : ℕ) {R R' : CommAlgCat.{u} A} (g : R ⟶ R')
    (x : (normOneTorsion F B n).affinePoints R) :
    normOneTorsionUnitMap n R' ((normOneTorsion F B n).affinePointMap g x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B g.hom).toMonoidHom
        (normOneTorsionUnitMap n R x) := by
  change affineUnitsEquiv A B R' (((algSpec A).map g.op ≫ x) ≫
    (normOneTorsionInclusion (F := F) (B := B) n).hom.hom) = _
  rw [Category.assoc, affineUnitsEquiv_naturality]
  rfl

end Langlands.GroupScheme.WeilGm
