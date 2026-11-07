import Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Rational conjugation of actual additive coefficient operators -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme

namespace VectorGroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Conjugate an actual additive map by an actual rational point of its target. -/
def conjugateMap (x : groupScheme (CommRingCat.of k) 1 ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    groupScheme (CommRingCat.of k) 1 ⟶ G :=
  x ≫ (G.innerIso g).hom

/-- The conjugated map has the literal conjugation formula on every test scheme. -/
theorem comp_conjugateMap
    (x : groupScheme (CommRingCat.of k) 1 ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (Z : Over (Spec (CommRingCat.of k))) (a : Z ⟶ (groupScheme (CommRingCat.of k) 1).X) :
    a ≫ (conjugateMap x g).hom.hom =
      G.constantPoint g Z * (a ≫ x.hom.hom) * (G.constantPoint g Z)⁻¹ := by
  rw [conjugateMap, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G}
    {x : groupScheme (CommRingCat.of k) 1 ⟶ G}
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : T ≅ T} {α : characterLattice T}

/-- Actual rational normalizer conjugation transports the full all-test
equivariance law by its contravariant character action. -/
theorem IsTorusEquivariant.conjugateMap
    (hx : IsTorusEquivariant i x α) (hg : IsNormalizingPoint i g σ) :
    IsTorusEquivariant i (conjugateMap x g) (characterAut σ α) := by
  intro Z t c
  let t' := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hσ : (CommGroupScheme.groupHom σ.inv).hom.hom ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom]
    exact (congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) σ.inv_hom_id).trans
      (Grp.id_hom_hom _)
  have ht := hg.conj_comp Z t'
  have hcomp : (t' ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom =
      t ≫ i.hom.hom := by
    simp only [t', Category.assoc, hσ, Category.id_comp]
  rw [hcomp] at ht
  have hchar : charValue (characterAut σ α) Z t = charValue α Z t' := by
    simp only [charValue, characterAut_apply, comp_groupHom_comp,
      Category.assoc, t']
  rw [comp_conjugateMap, comp_conjugateMap, hchar, ← ht, ← hx Z t' c]
  group

end VectorGroup

namespace MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)
    (x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- The actual universal additive matrices intertwine through the constant
matrix of the same rational point, over every test algebra. -/
theorem affineMatrix_conjugateMap_commutation (A : CommAlgCat.{u} k)
    (a : GroupScheme.affinePoints
      (VectorGroup.groupScheme (CommRingCat.of k) 1) A) :
    (ρ.restrict (VectorGroup.conjugateMap x g)).affineMatrix A a *
        Matrix.GeneralLinearGroup.map (algebraMap k A) (ρ.rationalMatrix g) =
      Matrix.GeneralLinearGroup.map (algebraMap k A) (ρ.rationalMatrix g) *
        (ρ.restrict x).affineMatrix A a := by
  have h := congrArg (ρ.affineMatrix A)
    (VectorGroup.comp_conjugateMap x g ((algSpec (CommRingCat.of k)).obj (op A)) a)
  rw [map_mul, map_mul, map_inv, ρ.affineMatrix_constantPoint] at h
  exact (eq_mul_inv_iff_mul_eq).mp h

/-- Every actual divided-power coefficient matrix intertwines under rational
conjugation, over arbitrary fields. -/
theorem coefficientMatrix_conjugateMap_commutation (m : ℕ) :
    coefficientMatrix (ρ.restrict (VectorGroup.conjugateMap x g)) m *
        (ρ.rationalMatrix g : Matrix n n k) =
      (ρ.rationalMatrix g : Matrix n n k) * coefficientMatrix (ρ.restrict x) m := by
  let A := CommAlgCat.of k k[X]
  have h := congrArg Units.val (affineMatrix_conjugateMap_commutation ρ x g A
    (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => Polynomial.X)))
  simp only [Units.val_mul] at h
  rw [← univariateMatrix_aeval, ← univariateMatrix_aeval] at h
  dsimp only [A] at h
  ext a b
  have hab := congrArg (fun M : Matrix n n k[X] => (M a b).coeff m) h
  change (∑ c, Polynomial.aeval Polynomial.X
      (univariateMatrix (ρ.restrict (VectorGroup.conjugateMap x g)) a c) *
        Polynomial.C ((ρ.rationalMatrix g : Matrix n n k) c b)).coeff m =
    (∑ c, Polynomial.C ((ρ.rationalMatrix g : Matrix n n k) a c) *
      Polynomial.aeval Polynomial.X (univariateMatrix (ρ.restrict x) c b)).coeff m at hab
  simp only [Polynomial.finsetSum_coeff,
    Polynomial.aeval_X_left_apply,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C] at hab
  exact hab

/-- Conjugating an actual additive subgroup conjugates its original coefficient
operators. In particular the action on a transported vector is transported too. -/
theorem dividedPower_conjugateMap_apply (m : ℕ) (v : n → k) :
    dividedPower (ρ.restrict (VectorGroup.conjugateMap x g)) m
        ((ρ.rationalMatrix g : Matrix n n k) *ᵥ v) =
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ dividedPower (ρ.restrict x) m v := by
  simp only [dividedPower_eq_toLin, Matrix.toLin'_apply]
  rw [Matrix.mulVec_mulVec, coefficientMatrix_conjugateMap_commutation,
    ← Matrix.mulVec_mulVec]

end MatrixRepresentation.AdditiveDividedPowers
end Langlands.GroupScheme
