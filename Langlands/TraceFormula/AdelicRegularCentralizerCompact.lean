import Langlands.BaseChange.RegularNormCentralizerAlgebra
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Global.AdelicGLDeterminantNormOne
import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.Global.NumberFieldAdeleModuleTopology
import Langlands.Global.NumberFieldAdeleTensorNorm
import Langlands.TraceFormula.GeneralLinearWeilTwistedGeometry

/-! # Compact rational quotients of regular elliptic adelic matrix centralizers -/

noncomputable section

open Matrix Module NumberField Polynomial
open scoped TensorProduct
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.QuotientIntegration

namespace Langlands.TraceFormula

universe u

section RegularRepresentation

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] {n : ℕ} (b : Basis (Fin n) F E)

local notation "R" => Adeles F
local notation "A" => R ⊗[F] E

private def tensorAdeles : A ≃+* Adeles E :=
  (Algebra.TensorProduct.comm F R E).toRingEquiv.trans
    (numberFieldAdeleTensorEquiv F E).toRingEquiv

private theorem tensorAdeles_tmul (s : R) (x : E) :
    tensorAdeles F E (s ⊗ₜ[F] x) = diagonal E x * adeleInclusion s := by
  change numberFieldAdeleTensorEquiv F E (x ⊗ₜ[F] s) = _
  exact numberFieldAdeleTensorEquiv_tmul F E x s

private theorem tensorAdeles_repr (z : A) (i : Fin n) :
    (b.baseChange R).repr z i = adeleBasisEquiv F E b (tensorAdeles F E z) i := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      rw [Basis.baseChange_repr_tmul]
      exact (adeleBasisEquiv_tensor F E b x s i).symm
  | add z w hz hw => simp [hz, hw]

private def adeleRegularRepresentation : Adeles E →+* Matrix (Fin n) (Fin n) R :=
  (Algebra.leftMulMatrix (b.baseChange R)).toRingHom.comp (tensorAdeles F E).symm.toRingHom

private theorem adeleRegularRepresentation_apply (x : Adeles E) (i j : Fin n) :
    adeleRegularRepresentation F E b x i j =
      adeleBasisEquiv F E b (x * diagonal E (b j)) i := by
  change Algebra.leftMulMatrix (b.baseChange R) ((tensorAdeles F E).symm x) i j = _
  rw [Algebra.leftMulMatrix_eq_repr_mul, tensorAdeles_repr, map_mul,
    RingEquiv.apply_symm_apply, Basis.baseChange_apply, tensorAdeles_tmul, map_one, mul_one]

private theorem continuous_adeleRegularRepresentation :
    Continuous (adeleRegularRepresentation F E b) := by
  apply continuous_matrix
  intro i j
  simp only [adeleRegularRepresentation_apply]
  exact (continuous_apply i).comp ((continuous_adeleBasisEquiv F E b).comp
    (continuous_id.mul continuous_const))

private theorem adeleRegularRepresentation_diagonal (x : E) :
    adeleRegularRepresentation F E b (diagonal E x) =
      (Algebra.leftMulMatrix b x).map (diagonal F) := by
  have h : (tensorAdeles F E).symm (diagonal E x) = (1 : R) ⊗ₜ[F] x := by
    apply (tensorAdeles F E).injective
    rw [RingEquiv.apply_symm_apply, tensorAdeles_tmul, map_one, mul_one]
  ext i j
  change Algebra.leftMulMatrix (b.baseChange R) ((tensorAdeles F E).symm (diagonal E x)) i j =
    diagonal F (Algebra.leftMulMatrix b x i j)
  rw [h, Algebra.leftMulMatrix_eq_repr_mul, Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one, Algebra.leftMulMatrix_eq_repr_mul]

private theorem adeleRegularRepresentation_scalar (s : R) :
    adeleRegularRepresentation F E b (adeleInclusion s) =
      algebraMap R (Matrix (Fin n) (Fin n) R) s := by
  have h : (tensorAdeles F E).symm (adeleInclusion s) = algebraMap R A s := by
    apply (tensorAdeles F E).injective
    rw [RingEquiv.apply_symm_apply]
    change adeleInclusion s = tensorAdeles F E (s ⊗ₜ[F] (1 : E))
    rw [tensorAdeles_tmul, map_one, one_mul]
  change Algebra.leftMulMatrix (b.baseChange R) ((tensorAdeles F E).symm (adeleInclusion s)) = _
  rw [h, AlgHom.commutes]

private theorem adeleRegularRepresentation_injective :
    Function.Injective (adeleRegularRepresentation F E b) :=
  (Algebra.leftMulMatrix_injective (b.baseChange R)).comp (tensorAdeles F E).symm.injective

private def ideleRegularRepresentation : Ideles E →ₜ* AdelicGL F n where
  toMonoidHom := Units.map (adeleRegularRepresentation F E b).toMonoidHom
  continuous_toFun := (continuous_adeleRegularRepresentation F E b).units_map

private theorem ideleRegularRepresentation_diagonal (x : Eˣ) :
    ideleRegularRepresentation F E b (diagonalUnits E x) =
      AdelicGL.rational F n (Units.map (Algebra.leftMulMatrix b).toMonoidHom x) :=
  Units.ext (adeleRegularRepresentation_diagonal F E b x.val)

private theorem ideleRegularRepresentation_det (x : Ideles E) :
    Matrix.GeneralLinearGroup.det (ideleRegularRepresentation F E b x) =
      ideleNorm (K := F) (L := E) x := by
  obtain ⟨z, rfl⟩ := (Units.mapEquiv
    (numberFieldAdeleTensorEquiv F E).toMulEquiv).surjective x
  apply Units.ext
  change _ = (ideleNorm (K := F) (L := E)
    (Units.map (numberFieldAdeleTensorEquiv F E).toMonoidHom z)).val
  have h := congrArg Units.val (numberFieldAdeleTensorNormUnits_eq F E z)
  change Langlands.Algebra.tensorNorm F E R z.val = _ at h
  rw [← h]
  change (Algebra.leftMulMatrix (b.baseChange R) ((tensorAdeles F E).symm
    (numberFieldAdeleTensorEquiv F E z.val))).det =
      Algebra.norm R ((Algebra.TensorProduct.comm F E R) z.val)
  rw [← Algebra.norm_eq_matrix_det (b.baseChange R)]
  congr 1
  apply (tensorAdeles F E).injective
  rw [RingEquiv.apply_symm_apply]
  change numberFieldAdeleTensorEquiv F E z.val = numberFieldAdeleTensorEquiv F E
    ((Algebra.TensorProduct.comm F R E) ((Algebra.TensorProduct.comm F E R) z.val))
  rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]

private theorem determinantNorm_ideleRegularRepresentation (x : Ideles E) :
    AdelicBlockDeterminantCharacter.determinantNorm F n (ideleRegularRepresentation F E b x) =
      IdeleAbsoluteValue.full E x := by
  change IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det
    (ideleRegularRepresentation F E b x)) = _
  rw [ideleRegularRepresentation_det, full_ideleNorm]

end RegularRepresentation

section CharacteristicField

variable {F : Type u} [Field F] {n : ℕ} (g : Matrix (Fin n) (Fin n) F)

private def evaluationOnVector (v : Fin n → F) : AdjoinRoot g.charpoly →ₗ[F] Fin n → F where
  toFun x := charpolyRootEvaluation g x *ᵥ v
  map_add' x y := by rw [map_add, add_mulVec]
  map_smul' a x := by rw [map_smul, smul_mulVec]; rfl

private theorem exists_basis_leftMulMatrix_root (hsep : g.charpoly.Separable) :
    ∃ b : Basis (Fin n) F (AdjoinRoot g.charpoly),
      Algebra.leftMulMatrix b (AdjoinRoot.root g.charpoly) = g := by
  obtain ⟨v, hv⟩ := regularCyclicBasis F n g hsep
  let pb := AdjoinRoot.powerBasis' g.charpoly_monic
  have hn : g.charpoly.natDegree = n := by simp
  let c := pb.basis.reindex (finCongr hn)
  let W := (Matrix.GeneralLinearGroup.toLin hv.unit).toLinearEquiv
  let e : AdjoinRoot g.charpoly ≃ₗ[F] (Fin n → F) := c.equivFun.trans W
  have he : e.toLinearMap = evaluationOnVector g v := by
    apply c.ext
    intro j
    have hc : c j = AdjoinRoot.root g.charpoly ^ (j : ℕ) := by
      simp only [c, Basis.reindex_apply, PowerBasis.basis_eq_pow]
      rfl
    have hvj : c.equivFun (c j) = Pi.single j 1 := by
      funext i
      simp only [Basis.equivFun_self, Pi.single_apply, eq_comm (a := j) (b := i)]
    change W (c.equivFun (c j)) = charpolyRootEvaluation g (c j) *ᵥ v
    rw [hvj, hc, map_pow, charpolyRootEvaluation_root]
    change (↑hv.unit : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single j 1 = _
    rw [hv.unit_spec, Matrix.mulVec_single_one, cyclicBasisMatrix_col]
  let b := (Pi.basisFun F (Fin n)).map e.symm
  have hcoord (x : AdjoinRoot g.charpoly) (i : Fin n) : b.repr x i = e x i := by
    simp [b]
  refine ⟨b, ?_⟩
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hcoord]
  have hroot (x : AdjoinRoot g.charpoly) : e (AdjoinRoot.root g.charpoly * x) = g *ᵥ e x := by
    change e.toLinearMap _ = g *ᵥ e.toLinearMap x
    rw [he]
    change charpolyRootEvaluation g (AdjoinRoot.root g.charpoly * x) *ᵥ v = _
    rw [map_mul, charpolyRootEvaluation_root, ← mulVec_mulVec]
    rfl
  rw [hroot]
  have hj : e (b j) = Pi.single j 1 := by simp [b]
  rw [hj, Matrix.mulVec_single_one, Matrix.col_apply]

end CharacteristicField

section CompactQuotient

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The rational matrix group inside the determinant-norm-one adelic matrix group. -/
abbrev adelicDeterminantNormOneRational : Subgroup (AdelicGL.determinantNormOne F n) :=
  (AdelicGL.rational F n).range.subgroupOf (AdelicGL.determinantNormOne F n)

/-- The diagonal image of a rational matrix lies in the determinant-norm-one group. -/
def adelicDeterminantNormOnePoint (g : RationalGL F n) : AdelicGL.determinantNormOne F n :=
  ⟨AdelicGL.rational F n g, AdelicBlockDeterminantCharacter.determinantNorm_rational F n g⟩

/-- An irreducible separable rational characteristic polynomial gives a compact rational
left quotient of the centralizer inside the determinant-norm-one adelic group. -/
theorem adelicRegularCentralizerCompactQuotient (g : RationalGL F n)
    (hirr : Irreducible g.val.charpoly) (hsep : g.val.charpoly.Separable) :
    IsCompactTwistedCentralizerQuotient (adelicDeterminantNormOneRational F n)
      (ContinuousMulEquiv.refl _) (adelicDeterminantNormOnePoint F n g) := by
  classical
  let p := g.val.charpoly
  let E := AdjoinRoot p
  let : Fact (Irreducible p) := ⟨hirr⟩
  let : Field E := inferInstanceAs (Field (AdjoinRoot p))
  let : Module.Finite F E := (AdjoinRoot.powerBasis' g.val.charpoly_monic).finite
  let : NumberField E := NumberField.of_module_finite F E
  obtain ⟨b, hb⟩ := exists_basis_leftMulMatrix_root g.val hsep
  let m := adeleRegularRepresentation F E b
  let a := AdelicGL.rational F n g
  let H := AdelicGL.determinantNormOne F n
  let r := adelicDeterminantNormOnePoint F n g
  let Γ := adelicDeterminantNormOneRational F n
  let C := twistedCentralizer (MonoidHom.id H) r
  have hroot : m (diagonal E (AdjoinRoot.root p)) = a.val := by
    change adeleRegularRepresentation F E b (diagonal E (AdjoinRoot.root p)) = _
    rw [adeleRegularRepresentation_diagonal, hb]
    rfl
  obtain ⟨v, hv⟩ := regularCyclicBasis F n g.val hsep
  have hvA : IsUnit (cyclicBasisMatrix a.val (diagonal F ∘ v)) := by
    change IsUnit (cyclicBasisMatrix (g.val.map (diagonal F)) (diagonal F ∘ v))
    rw [← cyclicBasisMatrix_map]
    exact hv.map (diagonal F).mapMatrix
  have hmatrix (z : Matrix (Fin n) (Fin n) (Adeles F)) (hz : Commute z a.val) :
      ∃ x : Adeles E, m x = z := by
    obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hvA hz
    refine ⟨∑ j : Fin n, adeleInclusion (c j) * (Global.diagonal E (AdjoinRoot.root p)) ^ (j : ℕ), ?_⟩
    rw [map_sum, hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hroot, show m (adeleInclusion (c j)) = algebraMap _ _ (c j) from
      adeleRegularRepresentation_scalar F E b (c j), ← Algebra.smul_def]
  let f := ideleRegularRepresentation F E b
  have hcomm (x : Ideles E) : Commute (f x) a := by
    apply Units.ext
    change m x.val * a.val = a.val * m x.val
    rw [← hroot, ← map_mul, ← map_mul, mul_comm]
  let lift : NormOneIdeleClass.normOneIdeles E →ₜ* C := {
    toFun x := ⟨⟨f x.val, by
      change AdelicBlockDeterminantCharacter.determinantNorm F n (f x.val) = 1
      rw [determinantNorm_ideleRegularRepresentation F E b x.val]
      exact x.property⟩, by
      change _ ∈ twistedCentralizer (MonoidHom.id H) r
      rw [twistedCentralizer_id, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hcomm x.val).eq⟩
    map_one' := Subtype.ext (Subtype.ext (map_one f))
    map_mul' x y := Subtype.ext (Subtype.ext (map_mul f x.val y.val))
    continuous_toFun := by
      apply continuous_induced_rng.mpr
      apply continuous_induced_rng.mpr
      exact f.continuous.comp continuous_subtype_val }
  have hsurj : Function.Surjective lift := by
    intro x
    have h : Commute x.val.val a := by
      have hx := x.property
      change x.val ∈ twistedCentralizer (MonoidHom.id H) r at hx
      rw [twistedCentralizer_id, Subgroup.mem_centralizer_singleton_iff] at hx
      change Commute x.val r at hx
      exact hx.map H.subtype
    have hh := h.map (Units.coeHom _)
    have hh' := h.inv_left.map (Units.coeHom _)
    obtain ⟨z, hz⟩ := hmatrix x.val.val.val hh
    obtain ⟨w, hw⟩ := hmatrix (x.val.val⁻¹).val hh'
    have hm := adeleRegularRepresentation_injective F E b
    let zUnit : Ideles E := ⟨z, w,
      hm (by rw [map_mul, map_one, hz, hw]; exact x.val.val.val_inv),
      hm (by rw [map_mul, map_one, hz, hw]; exact x.val.val.inv_val)⟩
    have hzUnit : f zUnit = x.val.val := Units.ext hz
    have hnorm : zUnit ∈ NormOneIdeleClass.normOneIdeles E := by
      change IdeleAbsoluteValue.full E zUnit = 1
      rw [← determinantNorm_ideleRegularRepresentation F E b zUnit, hzUnit]
      exact x.val.property
    exact ⟨⟨zUnit, hnorm⟩, Subtype.ext (Subtype.ext hzUnit)⟩
  obtain ⟨D, hD, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet E
  let D' : Set (NormOneIdeleClass.normOneIdeles E) := Subtype.val ⁻¹' D
  have hD' : IsCompact D' :=
    (isClosed_singleton.preimage (IdeleAbsoluteValue.full E).continuous : IsClosed
      (NormOneIdeleClass.normOneIdeles E : Set (Ideles E))).isClosedEmbedding_subtypeVal
        |>.isCompact_preimage hD
  let Q := leftQuotientMap (Γ.subgroupOf C)
  change CompactSpace (LeftQuotient (Γ.subgroupOf C))
  have himage : (Q ∘ lift) '' D' = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := (leftQuotient_isOpenQuotientMap (Γ.subgroupOf C)).surjective q
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := hcover y.val y.property
    let c' : NormOneIdeleClass.normOneIdeles E :=
      ⟨diagonalUnits E c, IdeleAbsoluteValue.full_diagonalUnits E c⟩
    have hprincipal : lift c' ∈ Γ.subgroupOf C := by
      change f (diagonalUnits E c) ∈ (AdelicGL.rational F n).range
      exact ⟨_, (ideleRegularRepresentation_diagonal F E b c).symm⟩
    refine ⟨c' * y, hc, ?_⟩
    change Q (lift (c' * y)) = Q (lift y)
    rw [map_mul]
    exact leftQuotientMap_subgroup_mul _ ⟨lift c', hprincipal⟩ (lift y)
  exact isCompact_univ_iff.mp (himage ▸ hD'.image
    ((leftQuotient_isOpenQuotientMap (Γ.subgroupOf C)).continuous.comp lift.continuous))

end CompactQuotient

end Langlands.TraceFormula
