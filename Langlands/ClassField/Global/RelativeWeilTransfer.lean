import Langlands.ClassField.Global.RelativeWeilGroup
import Langlands.ClassFieldTheory.Local.Transfer
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.ClassField.Global.IdeleClassNormGaloisProductProof

/-! # The transfer from a relative global Weil group to the base idele classes

For an arbitrary class family `c` and a Galois extension `E / F` of number fields,
the actual group-theoretic transfer from `W = RelativeWeilGroup c F E` to its
finite-index idele-class subgroup `C_E` has Galois-fixed values and therefore descends
to `C_F`. No fundamental-class hypothesis is used. -/

noncomputable section

namespace Langlands.GroupTheory.Transfer

open Subgroup Subgroup.leftTransversals MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G} {A B : Type*} [CommGroup A] [CommGroup B]

/-- Post-composition with a homomorphism of abelian groups commutes with the transfer. -/
theorem transfer_comp [H.FiniteIndex] (ϕ : H →* A) (f : A →* B) (g : G) :
    MonoidHom.transfer (f.comp ϕ) g = f (MonoidHom.transfer ϕ g) := by
  let T : H.LeftTransversal := default
  rw [MonoidHom.transfer_def _ T, MonoidHom.transfer_def ϕ T]
  simp only [diff, MonoidHom.comp_apply, map_prod]

/-- Conjugation `h ↦ v⁻¹ * h * v` of a normal subgroup. -/
def conjInv [hH : H.Normal] (v : G) : H →* H where
  toFun h := ⟨v⁻¹ * h * v, by simpa using hH.conj_mem h h.2 v⁻¹⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem coe_conjInv [H.Normal] (v : G) (h : H) :
    (conjInv v h : G) = v⁻¹ * h * v := rfl

/-- Right translation by `v` of two left transversals of a normal subgroup turns their
difference into the difference for the conjugated homomorphism. -/
theorem diff_op_smul [H.Normal] [H.FiniteIndex] (ϕ : H →* A) (v : G)
    (S T : H.LeftTransversal) :
    diff ϕ (MulOpposite.op v • S) (MulOpposite.op v • T) = diff (ϕ.comp (conjInv v)) S T := by
  let _ := H.fintypeQuotientOfFiniteIndex
  simp only [diff]
  refine (Fintype.prod_equiv (MulAction.toPerm (MulOpposite.op v) : G ⧸ H ≃ G ⧸ H)
    _ _ fun q => ?_).symm
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  simp only [coe_conjInv, MulAction.toPerm_apply]
  rw [← smul_leftQuotientEquiv, ← smul_leftQuotientEquiv]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, mul_assoc]

/-- The transfer is invariant under conjugating its homomorphism by an element of the
ambient group. -/
theorem transfer_comp_conjInv [H.Normal] [H.FiniteIndex] (ϕ : H →* A) (v g : G) :
    MonoidHom.transfer (ϕ.comp (conjInv v)) g = MonoidHom.transfer ϕ g := by
  let T : H.LeftTransversal := default
  rw [MonoidHom.transfer_def _ T, MonoidHom.transfer_def ϕ (MulOpposite.op v • T),
    ← diff_op_smul]
  congr 1
  apply Subtype.ext
  exact smul_comm (MulOpposite.op v) g (T : Set G)

/-- An element of a normal subgroup fixes every coset. -/
theorem smul_quotient_of_mem [hH : H.Normal] {h : G} (hh : h ∈ H) (q : G ⧸ H) :
    h • q = q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa [mul_assoc] using hH.conj_mem _ (H.inv_mem hh) g⁻¹

/-- On a normal subgroup of finite index, the transfer is the product of the conjugates
by the elements of any left transversal. -/
theorem transfer_of_mem [H.Normal] [H.FiniteIndex] (ϕ : H →* A)
    (T : H.LeftTransversal) (h : H) :
    letI := H.fintypeQuotientOfFiniteIndex
    MonoidHom.transfer ϕ h = ∏ q : G ⧸ H, ϕ (conjInv (T.2.leftQuotientEquiv q : G) h) := by
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def ϕ T]
  simp only [diff]
  refine Fintype.prod_equiv (Equiv.refl _) _ _ fun q => ?_
  congr 1
  apply Subtype.ext
  simp only [coe_conjInv, Equiv.refl_apply]
  rw [smul_apply_eq_smul_apply_inv_smul,
    smul_quotient_of_mem (H.inv_mem h.2) q, smul_eq_mul, mul_assoc]

end Langlands.GroupTheory.Transfer

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField
open Langlands.Global.AdelicFunctoriality
open Langlands.GroupTheory.Transfer

universe u

namespace RelativeWeilGroup

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

/-- The idele-class subgroup of `W_{E/F}`: the range of the actual inclusion of `C_E`. -/
abbrev ideleClassSubgroup : Subgroup (RelativeWeilGroup c F E) :=
  (inclusion c F E).range

instance ideleClassSubgroup_finiteIndex : (ideleClassSubgroup c F E).FiniteIndex :=
  ⟨by rw [index_range_inclusion]; exact Module.finrank_pos.ne'⟩

instance ideleClassSubgroup_normal : (ideleClassSubgroup c F E).Normal := by
  rw [ideleClassSubgroup, exact]
  exact MonoidHom.normal_ker _

theorem isOpen_ideleClassSubgroup :
    IsOpen (ideleClassSubgroup c F E : Set (RelativeWeilGroup c F E)) := by
  rw [MonoidHom.coe_range]
  exact (isOpenEmbedding_inclusion c F E).isOpen_range

/-- The continuous multiplicative equivalence from the idele-class subgroup to `C_E`
inverting the inclusion; the open embedding gives continuity of this direction. -/
def ideleClassSubgroupEquiv :
    ideleClassSubgroup c F E ≃ₜ* IdeleClassGroup (𝓞 E) E where
  toMulEquiv := (MonoidHom.ofInjective (inclusion_injective c F E)).symm
  continuous_toFun := by
    apply (isOpenEmbedding_inclusion c F E).isEmbedding.continuous_iff.mpr
    have h : (inclusion c F E) ∘ (MonoidHom.ofInjective (inclusion_injective c F E)).symm =
        Subtype.val :=
      funext fun x => MonoidHom.apply_ofInjective_symm (inclusion_injective c F E) x
    change Continuous ((inclusion c F E) ∘
      (MonoidHom.ofInjective (inclusion_injective c F E)).symm)
    rw [h]
    exact continuous_subtype_val
  continuous_invFun :=
    continuous_induced_rng.2 (ClassExtension.continuous_inclusion (c F E))

@[simp]
theorem inclusion_ideleClassSubgroupEquiv (x : ideleClassSubgroup c F E) :
    inclusion c F E (ideleClassSubgroupEquiv c F E x) = x :=
  MonoidHom.apply_ofInjective_symm (inclusion_injective c F E) x

@[simp]
theorem ideleClassSubgroupEquiv_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    ideleClassSubgroupEquiv c F E ⟨inclusion c F E a, a, rfl⟩ = a :=
  (MonoidHom.ofInjective (inclusion_injective c F E)).symm_apply_apply a

/-- The transfer `W_{E/F} → C_E`: the published continuous transfer to the open
finite-index idele-class subgroup, composed with its identification with `C_E`. -/
def ideleTransfer : RelativeWeilGroup c F E →ₜ* IdeleClassGroup (𝓞 E) E :=
  Langlands.LocalClassField.continuousTransfer (A := IdeleClassGroup (𝓞 E) E)
    (ideleClassSubgroup c F E) (isOpen_ideleClassSubgroup c F E)
    { toMonoidHom := (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom
      continuous_toFun := (ideleClassSubgroupEquiv c F E).continuous_toFun }

/-- The underlying homomorphism of `ideleTransfer` is Mathlib's coset-product transfer. -/
theorem ideleTransfer_apply (t : RelativeWeilGroup c F E) :
    ideleTransfer c F E t =
      MonoidHom.transfer (A := IdeleClassGroup (𝓞 E) E)
        (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom t :=
  rfl

/-- The values of the transfer are fixed by every relative automorphism. -/
theorem relativeIdeleClassAut_ideleTransfer (σ : E ≃ₐ[F] E) (t : RelativeWeilGroup c F E) :
    relativeIdeleClassAut F E σ (ideleTransfer c F E t) = ideleTransfer c F E t := by
  obtain ⟨u, hu⟩ := projection_surjective c F E σ
  set ψ := (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom
  have hconj : ψ.comp (conjInv u⁻¹) = (relativeIdeleClassAut F E σ).toMonoidHom.comp ψ := by
    refine MonoidHom.ext fun x => ?_
    rcases x with ⟨_, a, rfl⟩
    have hx : conjInv u⁻¹ (⟨inclusion c F E a, a, rfl⟩ : ideleClassSubgroup c F E) =
        ⟨inclusion c F E (relativeIdeleClassAut F E σ a), _, rfl⟩ := by
      apply Subtype.ext
      rw [coe_conjInv, inv_inv, conjugation, hu]
      rfl
    rw [MonoidHom.comp_apply, hx, MonoidHom.comp_apply]
    exact (ideleClassSubgroupEquiv_inclusion c F E _).trans
      (congrArg (relativeIdeleClassAut F E σ)
        (ideleClassSubgroupEquiv_inclusion c F E a).symm)
  have h := transfer_comp_conjInv (A := IdeleClassGroup (𝓞 E) E) ψ u⁻¹ t
  rw [hconj, transfer_comp (A := IdeleClassGroup (𝓞 E) E)] at h
  exact h

/-- On `C_E`, the transfer is the product of the Galois conjugates. -/
theorem ideleTransfer_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite (E ≃ₐ[F] E)
    ideleTransfer c F E (inclusion c F E a) =
      ∏ σ : E ≃ₐ[F] E, relativeIdeleClassAut F E σ a := by
  let _ : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite (E ≃ₐ[F] E)
  let _ := (ideleClassSubgroup c F E).fintypeQuotientOfFiniteIndex
  let T : (ideleClassSubgroup c F E).LeftTransversal := default
  set ψ := (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom
  let e : RelativeWeilGroup c F E ⧸ ideleClassSubgroup c F E → (E ≃ₐ[F] E) :=
    fun q => projection c F E ((T.2.leftQuotientEquiv q : RelativeWeilGroup c F E)⁻¹)
  have hmk : ∀ q, (QuotientGroup.mk (T.2.leftQuotientEquiv q : RelativeWeilGroup c F E) :
      RelativeWeilGroup c F E ⧸ ideleClassSubgroup c F E) = q :=
    T.2.quotientGroupMk_leftQuotientEquiv
  have hker : ∀ x y : RelativeWeilGroup c F E,
      (QuotientGroup.mk x : RelativeWeilGroup c F E ⧸ ideleClassSubgroup c F E) =
        QuotientGroup.mk y ↔ projection c F E x = projection c F E y := by
    intro x y
    rw [QuotientGroup.eq, ideleClassSubgroup, exact, MonoidHom.mem_ker, map_mul, map_inv,
      inv_mul_eq_one]
  have he : Function.Bijective e := by
    constructor
    · intro q₁ q₂ h
      rw [← hmk q₁, ← hmk q₂, hker]
      simpa [e] using h
    · intro σ
      obtain ⟨g, hg⟩ := projection_surjective c F E σ⁻¹
      refine ⟨QuotientGroup.mk g, ?_⟩
      have h := (hker _ g).mp (hmk (QuotientGroup.mk g))
      show projection c F E
        ((T.2.leftQuotientEquiv (QuotientGroup.mk g) : RelativeWeilGroup c F E))⁻¹ = σ
      rw [map_inv, h, hg, inv_inv]
  change MonoidHom.transfer (A := IdeleClassGroup (𝓞 E) E) ψ
    ((⟨inclusion c F E a, a, rfl⟩ : ideleClassSubgroup c F E) : RelativeWeilGroup c F E) = _
  rw [transfer_of_mem (A := IdeleClassGroup (𝓞 E) E) ψ T]
  refine Fintype.prod_bijective e he _ _ fun q => ?_
  have hq : conjInv (T.2.leftQuotientEquiv q : RelativeWeilGroup c F E)
      (⟨inclusion c F E a, a, rfl⟩ : ideleClassSubgroup c F E) =
        ⟨inclusion c F E (relativeIdeleClassAut F E (e q) a), _, rfl⟩ := by
    apply Subtype.ext
    rw [coe_conjInv]
    conv_lhs => rw [← inv_inv (T.2.leftQuotientEquiv q : RelativeWeilGroup c F E)]
    rw [inv_inv, conjugation]
    rfl
  rw [hq]
  exact ideleClassSubgroupEquiv_inclusion c F E _

/-- The transfer lands in the image of `C_F`, by the published Galois descent. -/
theorem ideleTransfer_mem_range (t : RelativeWeilGroup c F E) :
    ideleTransfer c F E t ∈ (ideleClassInclusion (K := F) (L := E)).toMonoidHom.range :=
  ((ideleClassGaloisDescent.{u, u} F E).2 _).mp
    fun σ => relativeIdeleClassAut_ideleTransfer c F E σ t

/-- The transfer `W_{E/F} → C_F`, obtained from `ideleTransfer` by the published algebraic
idele-class Galois descent. -/
def transfer : RelativeWeilGroup c F E →* IdeleClassGroup (𝓞 F) F :=
  (MonoidHom.ofInjective (f := (ideleClassInclusion (K := F) (L := E)).toMonoidHom)
      (ideleClassGaloisDescent.{u, u} F E).1).symm.toMonoidHom.comp
    ((ideleTransfer c F E).toMonoidHom.codRestrict _ (ideleTransfer_mem_range c F E))

/-- Characterization of `transfer` through the inclusion `C_F → C_E`. -/
theorem ideleClassInclusion_transfer (t : RelativeWeilGroup c F E) :
    ideleClassInclusion (K := F) (L := E) (transfer c F E t) = ideleTransfer c F E t :=
  MonoidHom.apply_ofInjective_symm (f := (ideleClassInclusion (K := F) (L := E)).toMonoidHom)
    (ideleClassGaloisDescent.{u, u} F E).1 _

/-- Uniqueness: an idele class of `F` included to `ideleTransfer c F E t` equals the
transfer of `t`. -/
theorem eq_transfer_of_ideleClassInclusion_eq {t : RelativeWeilGroup c F E}
    {x : IdeleClassGroup (𝓞 F) F}
    (hx : ideleClassInclusion (K := F) (L := E) x = ideleTransfer c F E t) :
    x = transfer c F E t :=
  (ideleClassGaloisDescent.{u, u} F E).1 (hx.trans (ideleClassInclusion_transfer c F E t).symm)

/-- On `C_E`, the transfer is the idele-class norm. -/
theorem transfer_inclusion (a : IdeleClassGroup (𝓞 E) E) :
    transfer c F E (inclusion c F E a) = ideleClassNorm (K := F) (L := E) a := by
  apply (ideleClassGaloisDescent.{u, u} F E).1
  rw [ideleClassInclusion_transfer, ideleTransfer_inclusion]
  exact (ideleClassNormGaloisProduct.{u, u} F E a).symm

/-- The commutator subgroup lies in the kernel of the transfer. -/
theorem commutator_le_ker_transfer :
    commutator (RelativeWeilGroup c F E) ≤ (transfer c F E).ker := by
  have : IsMulCommutative (IdeleClassGroup (𝓞 F) F) :=
    ⟨⟨fun a b : IdeleClassGroup (𝓞 F) F => mul_comm a b⟩⟩
  exact Abelianization.commutator_subset_ker _

/-- If the inclusion `C_F → C_E` is a topological embedding, the transfer is continuous. -/
theorem continuous_transfer
    (hemb : IsEmbedding (ideleClassInclusion (K := F) (L := E))) :
    Continuous (transfer c F E) := by
  rw [hemb.continuous_iff]
  have h : (ideleClassInclusion (K := F) (L := E)) ∘ (transfer c F E) =
      ideleTransfer c F E :=
    funext (ideleClassInclusion_transfer c F E)
  rw [h]
  exact (ideleTransfer c F E).continuous

/-- The transfer as a continuous homomorphism, under the embedding hypothesis. -/
def continuousTransferOfEmbedding
    (hemb : IsEmbedding (ideleClassInclusion (K := F) (L := E))) :
    RelativeWeilGroup c F E →ₜ* IdeleClassGroup (𝓞 F) F where
  toMonoidHom := transfer c F E
  continuous_toFun := continuous_transfer c F E hemb

end RelativeWeilGroup

end Langlands.ClassField.Global
