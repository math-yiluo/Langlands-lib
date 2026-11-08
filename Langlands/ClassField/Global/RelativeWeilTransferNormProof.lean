import Langlands.ClassField.Global.RelativeWeilTransferNormStatement
import Langlands.ClassField.Global.IdeleClassNormEmbeddingProduct
import Langlands.GroupTheory.TransferRestriction

/-! # Proof of transfer and idele-class norm compatibility

For a tower `F ⊆ K ⊆ E` of number fields with `E / F` Galois, the transfer
`W_{E/F} → C_F` restricted along the inclusion `W_{E/K} → W_{E/F}` is the transfer
`W_{E/K} → C_K` followed by the idele-class norm `C_K → C_F`.

The proof has three steps.

1. A group-theoretic restriction formula for the transfer
   (`Langlands.GroupTheory.Transfer.transfer_apply_eq_prod`).
2. Conjugation on `C_E` inside `W_{E/F}` is the Galois action.
3. The idele-class norm as a product over automorphisms restricting to the embeddings
   `K → E` (`ideleClassInclusion_ideleClassNorm_eq_prod`). -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality
open Langlands.GroupTheory.Transfer

universe u

namespace RelativeWeilGroup

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

/-- Tate (1979), (1.2.2), for relative Weil groups: for every class family with the
restriction compatibility and every tower `F ⊆ K ⊆ E` of number fields with `E / F` Galois,
the transfer of the image of `t ∈ W_{E/K}` in `W_{E/F}` is the idele-class norm of the
transfer of `t` to `C_K`. -/
theorem transferNormCompatibility (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] [IsGalois F E]
    (h : FundamentalClass.Restriction c) : TransferNormCompatibility c F K E h := by
  have : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  intro t
  let ι : RelativeWeilGroup c K E →* RelativeWeilGroup c F E :=
    (restrictionInclusion c F E K h).toMonoidHom
  have hιinc : ∀ a, ι (inclusion c K E a) = inclusion c F E a :=
    restrictionInclusion_inclusion c F E K h
  have hι : ∀ x, x ∈ ideleClassSubgroup c K E ↔ ι x ∈ ideleClassSubgroup c F E := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hιinc a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, restrictionInclusion_injective c F E K h ?_⟩
      exact (hιinc a).trans ha
  have hAι : ideleClassSubgroup c F E ≤ ι.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨inclusion c K E a, hιinc a⟩
  have : ι.range.FiniteIndex := Subgroup.finiteIndex_of_le hAι
  let _ := ι.range.fintypeQuotientOfFiniteIndex
  let ψF := (ideleClassSubgroupEquiv c F E).toMulEquiv.toMonoidHom
  let ψK := (ideleClassSubgroupEquiv c K E).toMulEquiv.toMonoidHom
  let s : RelativeWeilGroup c F E ⧸ ι.range → (E ≃ₐ[F] E) := fun q => projection c F E q.out
  -- Step 2: conjugation by `q.out` on `C_E` is the Galois action of `s q`.
  have hconj : ∀ q : RelativeWeilGroup c F E ⧸ ι.range,
      ψF.comp (conjComap ι (fun x => (hι x).mp) q.out) =
        (relativeIdeleClassAut F E (s q)).toMonoidHom.comp ψK := by
    intro q
    refine MonoidHom.ext fun x => ?_
    rcases x with ⟨_, a, rfl⟩
    have hx : conjComap ι (fun x => (hι x).mp) q.out
        (⟨inclusion c K E a, a, rfl⟩ : ideleClassSubgroup c K E) =
          ⟨inclusion c F E (relativeIdeleClassAut F E (s q) a), _, rfl⟩ := by
      apply Subtype.ext
      rw [coe_conjComap, hιinc, conjugation]
      rfl
    rw [MonoidHom.comp_apply, hx, MonoidHom.comp_apply]
    exact (ideleClassSubgroupEquiv_inclusion c F E _).trans
      (congrArg (relativeIdeleClassAut F E (s q))
        (ideleClassSubgroupEquiv_inclusion c K E a).symm)
  -- The restrictions of the `s q` to `K` are exactly the embeddings `K → E`.
  have hs : Function.Bijective
      fun q => (s q).toAlgHom.comp (IsScalarTower.toAlgHom F K E) := by
    have hrange : ∀ g : RelativeWeilGroup c F E,
        g ∈ ι.range ↔ ∀ x : K, projection c F E g (algebraMap K E x) = algebraMap K E x := by
      intro g
      have hr := congrArg (fun H : Subgroup (RelativeWeilGroup c F E) => g ∈ H)
        (range_restrictionInclusion c F E K h)
      change g ∈ ι.range ↔ _
      rw [show ι.range = (restrictionInclusion c F E K h).toMonoidHom.range from rfl, hr,
        Subgroup.mem_comap, MonoidHom.mem_range]
      constructor
      · rintro ⟨τ, hτ⟩ x
        rw [← hτ]
        exact τ.commutes x
      · intro hg
        exact ⟨AlgEquiv.ofRingEquiv (f := (projection c F E g).toRingEquiv) hg,
          AlgEquiv.ext fun _ => rfl⟩
    constructor
    · intro q₁ q₂ hq
      rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
      refine QuotientGroup.eq.mpr ((hrange _).mpr fun x => ?_)
      have hx := DFunLike.congr_fun hq x
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom, s] at hx
      rw [map_mul, map_inv, AlgEquiv.mul_apply, ← hx, AlgEquiv.aut_inv,
        AlgEquiv.symm_apply_apply]
    · intro τ
      let σ : E ≃ₐ[F] E := AlgEquiv.ofBijective (τ.liftNormal E) (AlgHom.normal_bijective F E E _)
      obtain ⟨g, hg⟩ := projection_surjective c F E σ
      refine ⟨QuotientGroup.mk g, AlgHom.ext fun x => ?_⟩
      have hmem : g⁻¹ * (QuotientGroup.mk g : RelativeWeilGroup c F E ⧸ ι.range).out ∈ ι.range :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
      have hfix := (hrange _).mp hmem x
      rw [map_mul, map_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hg] at hfix
      have hσ : σ (algebraMap K E x) = τ x := by
        change τ.liftNormal E (algebraMap K E x) = τ x
        rw [AlgHom.liftNormal_commutes, Algebra.algebraMap_self, RingHom.id_apply]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom, s]
      have hP := congrArg σ hfix
      rw [AlgEquiv.apply_symm_apply] at hP
      rw [hP, hσ]
  -- Assemble.
  apply (eq_transfer_of_ideleClassInclusion_eq c F E _).symm
  rw [ideleClassInclusion_ideleClassNorm_eq_prod s hs, ideleTransfer_apply]
  change _ = MonoidHom.transfer (A := IdeleClassGroup (𝓞 E) E) ψF (ι t)
  rw [transfer_apply_eq_prod (M := IdeleClassGroup (𝓞 E) E) ι hι hAι ψF t]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [hconj, transfer_comp (A := IdeleClassGroup (𝓞 E) E), ← ideleTransfer_apply, ideleClassInclusion_transfer]
  rfl

/-- The target statement `TransferNormCompatibilityStatement`. -/
theorem transferNormCompatibilityStatement :
    TransferNormCompatibilityStatement.{u} :=
  fun c F K E _ _ _ _ _ _ _ _ _ _ _ h => transferNormCompatibility c F K E h

end RelativeWeilGroup

end Langlands.ClassField.Global
