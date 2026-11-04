import Langlands.GroupScheme.Torus.RepresentationWeightWeylFinite
import Langlands.GroupScheme.Torus.Maximal

/-! # Normalizer action on faithful representation weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.NormalizerRepresentationWeights

open splitTorus CharacterRestrictionFiniteIndex
open RepresentationWeightWeylFinite (exponentAut)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]

/-- Pulling the universal point through the inverse automorphism evaluates a
character as the monomial of its transformed exponent. -/
theorem exponentValue_inv_universalPoint
    (σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I) (m : I → ℤ) :
    exponentValue I
      (algebraPointsEquiv I _
        (universalPoint (R := CommRingCat.of k) I ≫
          (CommGroupScheme.groupHom σ.inv).hom.hom))
      (Multiplicative.ofAdd m) =
        exponentUnit (R := CommRingCat.of k) I (exponentAut I σ m) := by
  rw [← characterValue_characterLatticeEquiv_symm k I]
  rw [← Lie.characterValue_comp (R := CommRingCat.of k)
    (A := AddMonoidAlgebra k (I → ℤ)) σ.inv
    ((characterLatticeEquiv k I).symm m)
    (universalPoint (R := CommRingCat.of k) I)]
  have hχ : σ.inv ≫ (characterLatticeEquiv k I).symm m =
      (characterLatticeEquiv k I).symm (exponentAut I σ m) :=
    ((characterLatticeEquiv k I).symm_apply_apply _).symm
  rw [hχ, characterValue_characterLatticeEquiv_symm, exponentValue_universalPoint]

variable {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- The transformed universal matrix has the original coefficient at the
transformed exponent. -/
theorem coeff_inv_universalPoint
    (σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I)
    (m : I → ℤ) (a b : Fin N) :
    ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ)))
      ((universalPoint (R := CommRingCat.of k) I ≫
        (CommGroupScheme.groupHom σ.inv).hom.hom) ≫ j.hom.hom ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b).coeff
          (exponentAut I σ m) = weight ρ I j m a b := by
  classical
  rw [← (algebraPointsEquiv I _).symm_apply_apply
    (universalPoint (R := CommRingCat.of k) I ≫
      (CommGroupScheme.groupHom σ.inv).hom.hom), affinePointsEquiv_eval]
  simp_rw [exponentValue_inv_universalPoint (k := k) I σ]
  simp only [
    exponentUnit_val, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    coeff_smul_single_one, (exponentAut I σ).injective.eq_iff]
  exact sum_ite_eq_of_weightSupport ρ I j (fun n => weight ρ I j n a b)
    (fun n hn => weight_apply_eq_zero ρ I j hn a b) m

/-- The invertible representation matrix of a point over the base, measured on
the canonical affine test algebra `k`. -/
def baseMatrix (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    Matrix.GeneralLinearGroup (Fin N) k :=
  GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) k)
      (G.constantPoint n ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) k))) ≫ ρ.hom.hom)

omit [Fintype I] [DecidableEq I] in
/-- A constant base point has constant monomial coefficients on the universal
torus test algebra. -/
theorem constantPoint_matrix_apply
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (a b : Fin N) :
    (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ)))
      (G.constantPoint n ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ))))) ≫
          ρ.hom.hom) : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b =
        AddMonoidAlgebra.single 0 (baseMatrix ρ n a b) := by
  rw [← G.constantPoint_naturality n
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (AddMonoidAlgebra.singleZeroAlgHom
        (R := k) (A := k) (M := I → ℤ))).op),
    Category.assoc, GeneralLinear.affinePointsEquiv_naturality,
    Matrix.GeneralLinearGroup.map_apply]
  exact AddMonoidAlgebra.singleZeroAlgHom_apply
    (R := k) (A := k) (M := I → ℤ) _

/-- The normalizing matrix intertwines the original weight matrix with the one
at the transformed exponent. -/
theorem weight_mul_baseMatrix
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I}
    (hn : IsNormalizingPoint j n σ) (m : I → ℤ) :
    weight ρ I j (exponentAut I σ m) * (baseMatrix ρ n : Matrix (Fin N) (Fin N) k) =
      (baseMatrix ρ n : Matrix (Fin N) (Fin N) k) * weight ρ I j m := by
  classical
  let U := (algSpec (CommRingCat.of k)).obj
    (op (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ))))
  let t := universalPoint (R := CommRingCat.of k) I
  let t' := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  let nA := G.constantPoint n U
  have hσ : (CommGroupScheme.groupHom σ.inv).hom.hom ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom]
    exact (congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) σ.inv_hom_id).trans
      (Grp.id_hom_hom _)
  have hpt : t ≫ j.hom.hom = nA * (t' ≫ j.hom.hom) * nA⁻¹ := by
    have h1 := congrArg (fun f => t' ≫ f.hom.hom) hn
    simp only [Grp.comp_hom_hom] at h1
    rw [← Category.assoc, comp_innerIso_hom] at h1
    rw [h1, ← Category.assoc]
    change t ≫ j.hom.hom = (t ≫
      ((CommGroupScheme.groupHom σ.inv).hom.hom ≫
        (CommGroupScheme.groupHom σ.hom).hom.hom)) ≫ j.hom.hom
    rw [hσ, Category.comp_id]
  have hρ : ((t ≫ j.hom.hom) ≫ ρ.hom.hom) * (nA ≫ ρ.hom.hom) =
      (nA ≫ ρ.hom.hom) * ((t' ≫ j.hom.hom) ≫ ρ.hom.hom) := by
    rw [← MonObj.mul_comp, hpt, mul_assoc, inv_mul_cancel, mul_one, MonObj.mul_comp]
  let E := GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ)))
  have hmat : (E ((t ≫ j.hom.hom) ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) *
      (E (nA ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) =
      (E (nA ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) *
      (E ((t' ≫ j.hom.hom) ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) := by
    simpa only [map_mul, Units.val_mul] using
      congrArg (fun x => (E x : Matrix (Fin N) (Fin N)
        (AddMonoidAlgebra k (I → ℤ)))) hρ
  ext a b
  have h := congrArg (fun z : AddMonoidAlgebra k (I → ℤ) =>
      z.coeff (exponentAut I σ m)) (congrFun (congrFun hmat a) b)
  simp only [Matrix.mul_apply, E, nA, U,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h
  simp_rw [constantPoint_matrix_apply (k := k) I ρ n] at h
  simp only [
    AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_single_zero_mul] at h
  simp only [t', t, Category.assoc] at h
  simp_rw [← Category.assoc (universalPoint (R := CommRingCat.of k) I)
    (CommGroupScheme.groupHom σ.inv).hom.hom] at h
  simp_rw [coeff_inv_universalPoint (k := k) I ρ j σ] at h
  exact h

/-- Normalizing points preserve the finite set of nonzero representation
weights; invertibility of their representation matrix detects nonvanishing. -/
theorem weight_ne_zero_exponentAut
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I}
    (hn : IsNormalizingPoint j n σ) {m : I → ℤ}
    (hm : weight ρ I j m ≠ 0) :
    weight ρ I j (exponentAut I σ m) ≠ 0 := by
  intro hzero
  apply hm
  have h := weight_mul_baseMatrix I ρ j hn m
  rw [hzero, zero_mul] at h
  have h' := congrArg
    (fun z : Matrix (Fin N) (Fin N) k =>
      (↑((baseMatrix ρ n)⁻¹) : Matrix (Fin N) (Fin N) k) * z) h.symm
  simpa only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul, mul_zero] using h'

/-- The chosen normalizer automorphism preserves every nonzero representation
weight in exponent coordinates. -/
theorem weight_ne_zero_normalizingAut
    (n : normalizerPoints (T := commGroupScheme (Spec (CommRingCat.of k)) I) j)
    {m : I → ℤ} (hm : weight ρ I j m ≠ 0) :
    weight ρ I j (exponentAut I
      (normalizingAut (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n) m) ≠ 0 :=
  weight_ne_zero_exponentAut I ρ j
    (isNormalizingPoint_normalizingAut
      (T := commGroupScheme (Spec (CommRingCat.of k)) I) j n) hm

end Langlands.GroupScheme.NormalizerRepresentationWeights
