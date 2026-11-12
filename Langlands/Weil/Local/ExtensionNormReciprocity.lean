import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.NormExistenceProof
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityNormBridges
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.LocalFactor.RankOne
import Langlands.LocalField.Normalization.Proof
import Langlands.Weil.Local.ExtensionWeil

/-! # Norm compatibility of geometric Weil reciprocity along a field embedding -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Two units of the same nonzero order agree if every open finite-index subgroup
containing the first also contains the second. -/
theorem eq_of_forall_openFiniteIndex (a b : F.Carrierˣ)
    (hord : T.ord (b : F.Carrier) = T.ord (a : F.Carrier)) (ha : T.ord (a : F.Carrier) ≠ 0)
    (h : letI := T.topology
      ∀ V : Subgroup F.Carrierˣ, IsOpen (V : Set F.Carrierˣ) → V.FiniteIndex → a ∈ V → b ∈ V) :
    a = b := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_contra hab
  set z := b / a with hz
  have hz1 : z ≠ 1 := fun h1 => hab (div_eq_one.mp h1).symm
  have hzU : z ∈ T.unitSubgroup := by
    rw [T.mem_unitSubgroup_iff_orderHom, hz, map_div, div_eq_one]
    exact congrArg Multiplicative.ofAdd hord
  obtain ⟨V0, hV0, hV0f, hzV0⟩ := T.exists_open_finiteIndex_excluding z hz1
  let n : ℕ := (T.ord (a : F.Carrier)).natAbs * V0.index
  have hn : n ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr ha) hV0f.index_ne_zero
  have : NeZero n := ⟨hn⟩
  let χ : F.Carrierˣ →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative.comp T.orderHom
  let V : Subgroup F.Carrierˣ := Subgroup.zpowers a ⊔ (V0 ⊓ T.unitSubgroup)
  have hle : V0 ⊓ χ.ker ≤ V := by
    rintro y ⟨hyV0, hyχ⟩
    have hd : (n : ℤ) ∣ T.ord (y : F.Carrier) := by
      have h0 : ((T.ord (y : F.Carrier) : ℤ) : ZMod n) = 0 := ofAdd_eq_one.mp hyχ
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h0
    obtain ⟨k, hk⟩ := hd
    let m : ℤ := (T.ord (a : F.Carrier)).sign * ((V0.index : ℤ) * k)
    have hm : T.ord (a : F.Carrier) * m = T.ord (y : F.Carrier) := by
      rw [hk]
      change T.ord (a : F.Carrier) * ((T.ord (a : F.Carrier)).sign * ((V0.index : ℤ) * k)) =
        (((T.ord (a : F.Carrier)).natAbs * V0.index : ℕ) : ℤ) * k
      rw [← mul_assoc, Int.mul_sign_self, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
    have ham : a ^ m ∈ V0 := by
      change a ^ ((T.ord (a : F.Carrier)).sign * ((V0.index : ℤ) * k)) ∈ V0
      rw [mul_comm, zpow_mul, zpow_mul, zpow_natCast]
      exact V0.zpow_mem (V0.zpow_mem (V0.pow_index_mem a) _) _
    have hw : y * (a ^ m)⁻¹ ∈ V0 ⊓ T.unitSubgroup := by
      refine ⟨V0.mul_mem hyV0 (V0.inv_mem ham), ?_⟩
      show y * (a ^ m)⁻¹ ∈ T.unitSubgroup
      rw [T.mem_unitSubgroup_iff_orderHom, map_mul, map_inv, map_zpow]
      change Multiplicative.ofAdd (T.ord (y : F.Carrier)) *
        (Multiplicative.ofAdd (T.ord (a : F.Carrier)) ^ m)⁻¹ = 1
      rw [← hm, ← ofAdd_zsmul, ← ofAdd_neg, ← ofAdd_add, smul_eq_mul, mul_comm m,
        add_neg_cancel, ofAdd_zero]
    have hy : y = a ^ m * (y * (a ^ m)⁻¹) := by
      rw [mul_comm y, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hy]
    exact V.mul_mem (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers a m))
      (Subgroup.mem_sup_right hw)
  have hVf : V.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hVo : IsOpen (V : Set F.Carrierˣ) :=
    Subgroup.isOpen_mono (le_sup_right : V0 ⊓ T.unitSubgroup ≤ V)
      (hV0.inter (Langlands.ClassFieldTheory.Local.isOpen_unitSubgroup F T))
  have haV : a ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hzV : z ∈ V := V.div_mem (h V hVo hVf haV) haV
  obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.mp hzV
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hwU : T.orderHom w = 1 := (T.mem_unitSubgroup_iff_orderHom w).mp hw.2
  have hzO : T.orderHom z = 1 := (T.mem_unitSubgroup_iff_orderHom z).mp hzU
  rw [← hyw, map_mul, hwU, mul_one, map_zpow] at hzO
  change (Multiplicative.ofAdd (T.ord (a : F.Carrier))) ^ k = 1 at hzO
  rw [← ofAdd_zsmul, ofAdd_eq_one, smul_eq_mul, mul_eq_zero] at hzO
  have hk : k = 0 := hzO.resolve_right ha
  apply hzV0
  rw [← hyw, hk, zpow_zero, one_mul]
  exact hw.1

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u v w x

/-- In a square of finite field extensions `E ⊂ L ⊂ K'` and `E ⊂ K → K'` agreeing on `E`,
the norm to `E` of a norm from `K'` to `L` is a norm from `K`. -/
theorem normUnits_normUnits_mem_normSubgroup {E : Type u} {L : Type v} {K : Type w}
    {K' : Type x} [Field E] [Field L] [Field K] [Field K'] [Algebra E L] [Algebra L K']
    [Algebra E K] [FiniteDimensional E L] [FiniteDimensional L K'] [FiniteDimensional E K]
    (φ : K →+* K') (hφ : ∀ a : E, φ (algebraMap E K a) = algebraMap L K' (algebraMap E L a))
    (z : K'ˣ) :
    normUnits E L (normUnits L K' z) ∈ normSubgroup E K := by
  let : Algebra E K' := ((algebraMap L K').comp (algebraMap E L)).toAlgebra
  have : IsScalarTower E L K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra K K' := φ.toAlgebra
  have : IsScalarTower E K K' := IsScalarTower.of_algebraMap_eq fun a => (hφ a).symm
  have : FiniteDimensional E K' := FiniteDimensional.trans E L K'
  have : FiniteDimensional K K' := FiniteDimensional.right E K K'
  refine ⟨normUnits K K' z, ?_⟩
  apply Units.ext
  change Algebra.norm E (Algebra.norm K (z : K')) = Algebra.norm E (Algebra.norm L (z : K'))
  rw [Algebra.norm_norm, Algebra.norm_norm]

namespace FiniteAbelianExtension

/-- Restriction to a finite abelian extension is trivial exactly on its fixing subgroup. -/
theorem restriction_eq_one_iff {K : Type u} [Field K] (A : FiniteAbelianExtension K)
    (σ : Field.absoluteGaloisGroup K) :
    A.restriction σ = 1 ↔
      (σ : Gal(AlgebraicClosure K/K)) ∈ A.field.toIntermediateField.fixingSubgroup :=
  MonoidHom.mem_ker.symm.trans
    (SetLike.ext_iff.mp (IntermediateField.restrictNormalHom_ker A.field.toIntermediateField) σ)

/-- The fixed field of an open normal subgroup `V` of the absolute Galois group containing every
commutator, packaged as a finite abelian extension. It is finite because `V` is open, Galois
because `V` is normal, and abelian because `V` contains all commutators. -/
def ofOpenNormal {K : Type u} [Field K] [PerfectField K]
    (V : Subgroup Gal(AlgebraicClosure K/K)) [V.Normal]
    (hV : IsOpen (V : Set Gal(AlgebraicClosure K/K)))
    (hcomm : ∀ s t : Gal(AlgebraicClosure K/K), s * t * (t * s)⁻¹ ∈ V) :
    FiniteAbelianExtension K := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let M := IntermediateField.fixedField V
  have hfix : M.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, Subgroup.isClosed_of_isOpen V hV⟩
  let : FiniteDimensional K M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfix]; exact hV)
  let : IsGalois K M := IsGalois.of_fixedField_normal_subgroup V
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) M
  have hker : r.ker = V := M.restrictNormalHom_ker.trans hfix
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  have hc : IsMulCommutative Gal(M/K) := .of_comm fun a b => by
    obtain ⟨s, rfl⟩ := hr a
    obtain ⟨t, rfl⟩ := hr b
    apply mul_inv_eq_one.mp
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul]
    exact show s * t * (t * s)⁻¹ ∈ r.ker from hker.symm ▸ hcomm s t
  exact ⟨{ toIntermediateField := M }, hc⟩

/-- The field of `ofOpenNormal V` is the fixed field of `V`. -/
theorem ofOpenNormal_toIntermediateField {K : Type u} [Field K] [PerfectField K]
    (V : Subgroup Gal(AlgebraicClosure K/K)) [V.Normal]
    (hV : IsOpen (V : Set Gal(AlgebraicClosure K/K)))
    (hcomm : ∀ s t : Gal(AlgebraicClosure K/K), s * t * (t * s)⁻¹ ∈ V) :
    (ofOpenNormal V hV hcomm).field.toIntermediateField = IntermediateField.fixedField V :=
  rfl

/-- The fixing subgroup of `ofOpenNormal V` is `V`. -/
theorem ofOpenNormal_fixingSubgroup {K : Type u} [Field K] [PerfectField K]
    (V : Subgroup Gal(AlgebraicClosure K/K)) [V.Normal]
    (hV : IsOpen (V : Set Gal(AlgebraicClosure K/K)))
    (hcomm : ∀ s t : Gal(AlgebraicClosure K/K), s * t * (t * s)⁻¹ ∈ V) :
    (ofOpenNormal V hV hcomm).field.toIntermediateField.fixingSubgroup = V := by
  have : IsGalois K (AlgebraicClosure K) := ⟨⟩
  rw [ofOpenNormal_toIntermediateField]
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨V, Subgroup.isClosed_of_isOpen V hV⟩

end FiniteAbelianExtension

end Langlands.LocalClassField

namespace Langlands.Weil.Local

universe u v

open LocalClassField LocalFactor.RankOne

variable {p : ℕ} [Fact p.Prime]

section Membership

variable (E : PadicField.{u} p) (e : ReciprocityCandidate E)
  (he : GeometricWeilReciprocityRelation E E.canonicalTopologicalData e)

include he in
/-- Under geometric reciprocity, the image of a Weil element is a norm from a finite abelian
extension exactly when its Galois projection fixes that extension. -/
theorem reciprocityUnits_mem_normSubgroup_iff (K : FiniteAbelianExtension E.Carrier)
    (y : localWeilGroup E) :
    reciprocityUnits E e y ∈ normSubgroup E.Carrier K.field ↔
      localProjection E y ∈ K.field.toIntermediateField.fixingSubgroup := by
  let := E.canonicalTopologicalData.topology
  have hker := (he.2.1.2.1 K).1
  have hval : finiteFamilyOfHom
      (candidateGaloisHom E.canonicalTopologicalData (localResidueDegree E) e) K
        (reciprocityUnits E e y) = K.restriction (localProjection E y) := by
    change K.abelianRestriction (WeilQuotients.toGroupAbelianization (localResidueDegree E)
      (e.symm (e (WeilQuotients.projection (localResidueDegree E) y)))) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  rw [← hker, MonoidHom.mem_ker]
  change finiteFamilyOfHom _ K (reciprocityUnits E e y) = 1 ↔ _
  rw [hval]
  exact K.restriction_eq_one_iff _

end Membership

section NormSquare

variable (E : PadicField.{u} p) (L : PadicField.{v} p) (g : E.Carrier →ₐ[Padic p] L.Carrier)

/-- If the Galois projection of the image of `y` fixes a finite abelian extension `K` of `E`,
then the norm of the `L`-reciprocity value of `y` is a norm from `K`. The comparison field is
the fixed field of the pullback of the fixing subgroup of `K`. -/
theorem normUnits_reciprocityUnits_mem_normSubgroup (eL : ReciprocityCandidate L)
    (heL : GeometricWeilReciprocityRelation L L.canonicalTopologicalData eL)
    (K : FiniteAbelianExtension E.Carrier) (y : localWeilGroup L)
    (hy : localProjection E (extensionWeilMap E L g y) ∈
      K.field.toIntermediateField.fixingSubgroup) :
    letI := extensionAlgebra E L g
    haveI := extensionAlgebra_finiteDimensional E L g
    normUnits E.Carrier L.Carrier (reciprocityUnits L eL y) ∈
      normSubgroup E.Carrier K.field := by
  let := extensionAlgebra E L g
  have := extensionAlgebra_finiteDimensional E L g
  let ψ : Gal(AlgebraicClosure L.Carrier/L.Carrier) →*
      Gal(AlgebraicClosure E.Carrier/E.Carrier) :=
    (extensionGaloisMap E L g).toMonoidHom
  have : CharZero L.Carrier := Algebra.charZero_of_charZero (Padic p) L.Carrier
  let r := AlgEquiv.restrictNormalHom (F := E.Carrier) (K₁ := AlgebraicClosure E.Carrier)
    K.field.toIntermediateField
  let S := K.field.toIntermediateField.fixingSubgroup
  have hS : S = r.ker := (IntermediateField.restrictNormalHom_ker _).symm
  have : S.Normal := hS ▸ MonoidHom.normal_ker r
  let V := S.comap ψ
  have hV : IsOpen (V : Set Gal(AlgebraicClosure L.Carrier/L.Carrier)) :=
    K.field.toIntermediateField.fixingSubgroup_isOpen.preimage
      (extensionGaloisMap E L g).continuous
  have hcomm : ∀ s t : Gal(AlgebraicClosure L.Carrier/L.Carrier), s * t * (t * s)⁻¹ ∈ V := by
    intro s t
    change ψ (s * t * (t * s)⁻¹) ∈ S
    rw [hS, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, map_mul,
      map_mul, K.2.is_comm.comm (r (ψ s)), mul_inv_cancel]
  let K' := FiniteAbelianExtension.ofOpenNormal V hV hcomm
  have hK'f := FiniteAbelianExtension.ofOpenNormal_toIntermediateField V hV hcomm
  have hK'V := FiniteAbelianExtension.ofOpenNormal_fixingSubgroup V hV hcomm
  have hyK' : localProjection L y ∈ K'.field.toIntermediateField.fixingSubgroup := by
    rw [hK'V]
    exact hy
  obtain ⟨z, hz⟩ := (reciprocityUnits_mem_normSubgroup_iff L eL heL K' y).mpr hyK'
  rw [← hz]
  have hlift : ∀ x : K.field, extensionClosureLift E L g (x : AlgebraicClosure E.Carrier) ∈
      K'.field.toIntermediateField := by
    intro x
    rw [hK'f]
    rintro ⟨σ, hσ⟩
    change σ (extensionClosureLift E L g x) = extensionClosureLift E L g x
    have h := extensionClosureLift_galoisMap E L g σ x
    change extensionClosureLift E L g ((ψ σ) x) = σ (extensionClosureLift E L g x) at h
    rw [← h]
    exact congrArg (extensionClosureLift E L g) (hσ x)
  let φ : K.field →+* K'.field :=
    ((extensionClosureLift E L g).comp
      (K.field.toIntermediateField.val : K.field →ₐ[E.Carrier] AlgebraicClosure E.Carrier)
        ).codRestrict K'.field.toIntermediateField hlift
  refine normUnits_normUnits_mem_normSubgroup φ (fun a => ?_) z
  apply Subtype.ext
  exact extensionClosureLift_algebraMap E L g a

/-- Norm compatibility of geometric Weil reciprocity: along `g : E → L`, reciprocity for `E`
of the image of a Weil element of `L` is the norm of its reciprocity value for `L`. -/
theorem reciprocityUnits_extensionWeilMap (eE : ReciprocityCandidate E)
    (heE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (eL : ReciprocityCandidate L)
    (heL : GeometricWeilReciprocityRelation L L.canonicalTopologicalData eL)
    (y : localWeilGroup L) :
    letI := extensionAlgebra E L g
    reciprocityUnits E eE (extensionWeilMap E L g y) =
      Units.map (Algebra.norm E.Carrier) (reciprocityUnits L eL y) := by
  let := extensionAlgebra E L g
  have := extensionAlgebra_isScalarTower E L g
  have := extensionAlgebra_finiteDimensional E L g
  let TE := E.canonicalTopologicalData
  let TL := L.canonicalTopologicalData
  have hordE : ∀ w, TE.ord (reciprocityUnits E eE w : E.Carrier) = localDegreeInt E w :=
    fun w => congrArg Multiplicative.toAdd
      (DFunLike.congr_fun heE.1 (WeilQuotients.projection (localResidueDegree E) w))
  have hordL : ∀ w, TL.ord (reciprocityUnits L eL w : L.Carrier) = localDegreeInt L w :=
    fun w => congrArg Multiplicative.toAdd
      (DFunLike.congr_fun heL.1 (WeilQuotients.projection (localResidueDegree L) w))
  have hres : TL.residueDegree = TE.residueDegree * extensionResidueDegree E L g := by
    have hcard := extensionResidueCardinality E L g
    rw [PadicField.TopologicalData.residueCardinality_eq_pow,
      PadicField.TopologicalData.residueCardinality_eq_pow,
      ← pow_mul] at hcard
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
  have hnorm : ∀ x : L.Carrierˣ,
      TE.ord (Units.map (Algebra.norm E.Carrier) x : E.Carrier) =
        extensionResidueDegree E L g * TL.ord (x : L.Carrier) := by
    intro x
    have h := (relativeNormOrderLaws p E L TE TL).1 x
    rw [hres, Nat.cast_mul, mul_assoc] at h
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast TE.residueDegree_pos.ne') h
  have key : ∀ y, localDegreeInt L y ≠ 0 →
      reciprocityUnits E eE (extensionWeilMap E L g y) =
        Units.map (Algebra.norm E.Carrier) (reciprocityUnits L eL y) := by
    intro y hy
    apply TE.eq_of_forall_openFiniteIndex
    · rw [hnorm, hordL, hordE, localDegreeInt_extensionWeilMap]
    · rw [hordE, localDegreeInt_extensionWeilMap]
      exact mul_ne_zero (by exact_mod_cast (extensionResidueDegree_pos E L g).ne') hy
    · intro V hVo hVf haV
      obtain ⟨M, ⟨hMfd, hMab, hMV⟩, -⟩ :=
        ClassFieldTheory.Local.normSubgroupExistence p E V hVo hVf
      let A := FiniteAbelianExtension.ofIntermediateField M
      have hA : normSubgroup E.Carrier A.field = V := hMV
      rw [← hA] at haV ⊢
      exact normUnits_reciprocityUnits_mem_normSubgroup E L g eL heL A y
        ((reciprocityUnits_mem_normSubgroup_iff E eE heE A _).mp haV)
  by_cases hy : localDegreeInt L y = 0
  · let Φ := localGeometricFrobenius L
    have hΦ : localDegreeInt L Φ = 1 := by
      change (localDegree L (localGeometricFrobenius L)).toAdd = 1
      rw [localGeometricFrobenius_degree]
      rfl
    have h1 : localDegreeInt L (y * Φ) ≠ 0 := by
      change (localDegree L (y * Φ)).toAdd ≠ 0
      rw [map_mul, toAdd_mul]
      change localDegreeInt L y + localDegreeInt L Φ ≠ 0
      rw [hy, hΦ]
      decide
    have h2 : localDegreeInt L Φ⁻¹ ≠ 0 := by
      change (localDegree L Φ⁻¹).toAdd ≠ 0
      rw [map_inv, toAdd_inv]
      change -localDegreeInt L Φ ≠ 0
      rw [hΦ]
      decide
    have hdec : y = y * Φ * Φ⁻¹ := (mul_inv_cancel_right y Φ).symm
    rw [hdec, map_mul, map_mul, key _ h1, key _ h2, ← map_mul, ← map_mul]
  · exact key y hy

end NormSquare

end Langlands.Weil.Local
