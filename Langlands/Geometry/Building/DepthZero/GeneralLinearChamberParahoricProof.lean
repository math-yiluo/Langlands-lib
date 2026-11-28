import Langlands.Geometry.Building.DepthZero.GeneralLinearStatement
import Langlands.Geometry.Building.DepthZero.GeneralLinear.ChamberPoint

/-!
# Chamber parahorics of `GL_N` are the conjugates of the standard Iwahori subgroup

Proof of `GeneralLinearChamberParahoricStatement`. Let `D` be building data of `GL_N` over a
nonarchimedean local field `F` satisfying the one-group axioms, and `C = h · C₀` a chamber of
the reduced building, `C₀` the facet of a point `x₀` of the apartment on no root hyperplane.

* `D.parahoric C = G(F)_C ∩ G(F)^0` (Axiom 4.1.20,
  `KPBuildingDatum.parahoric_eq_pointwiseFixer_inf`), which is `h (G(F)_{C₀} ∩ G(F)^0) h⁻¹`
  (`ParahoricBuildingData.pointwiseFixer_smul_image_inf_zeroSubgroup`); by Axiom 4.1.8 (2) the
  elements of `G(F)^0` fixing `C₀` are those fixing `x₀`
  (`ParahoricBuildingData.zeroFixer_facet_eq_nonnegativeRootSubgroup_singleton`).
* Transporting `D` to data `P'` whose maximal split torus is the diagonal torus, as in the
  vertex case, carries `G(F)_{x₀} ∩ G(F)^0` to `G(F)^0_{x₁}` for the image `x₁` of `x₀`, which
  is `(d m) I (d m)⁻¹` (`nonnegativeRootSubgroup_singleton_eq_of_chamber`,
  `exists_floor_perm_of_forall_ne_intCast`).

So `D.parahoric C = (h c) I (h c)⁻¹` with `c` depending only on `x₀`; a chamber point of the
apartment exists (`exists_forall_sub_ne_intCast`, `exists_rootValue_eq_sub_of`), and choosing
`h = g c⁻¹` gives every conjugate `g I g⁻¹`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels GeneralLinearParahoric

/-- Proof of `GeneralLinearChamberParahoricStatement`: the parahorics of the chambers of
building data of `GL_N` are exactly the conjugates of the standard Iwahori subgroup. -/
theorem generalLinearChamberParahoric : GeneralLinearChamberParahoricStatement.{u} := by
  intro F _ _ _ _ N D hD
  dsimp only
  -- Transport to data whose maximal split torus is the diagonal torus.
  obtain ⟨g₀, e, he⟩ := (maximalSplitTorusConjugacy F _ D.base.isConnectedReductive).1
    D.base.S (diagonalSplitTorus F N) D.base.i (diagTorus F N) D.base.isMaximalSplitTorus
    (GeneralLinear.isMaximalSplitTorus_diagonalTorus F)
  let σ : D.base.S ≅ diagonalSplitTorus F N :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hσ : D.base.i ≫ ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      CommGroupScheme.groupHom σ.hom ≫ diagTorus F N := he
  have hD' := hD.basedTransport σ _ hσ
  have hZ' : (D.base.basedTransport σ _ hσ).HasZeroFixerGenerators :=
    hD'.satisfiesPartialBuildingAxioms.hasZeroFixerGenerators
  have hZ : D.base.HasZeroFixerGenerators :=
    hD.satisfiesPartialBuildingAxioms.hasZeroFixerGenerators
  have hA : D.base.SatisfiesApartmentAxioms := hD.satisfiesPartialBuildingAxioms.apartmentAxioms
  have hφ : rationalPoints.map
      ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)).innerIso g₀).hom =
      (MulAut.conj g₀).toMonoidHom :=
    MonoidHom.ext fun x => by
      rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self]
      rfl
  -- The elements of `G(F)^0` fixing a point of the apartment on no root hyperplane.
  have key : ∀ x₀ : D.base.Apartment, (∀ ψ ∈ D.base.affineRoots, ψ x₀ ≠ 0) →
      ∃ c, D.base.pointwiseFixer {D.base.apartmentMap x₀} ⊓ D.base.zeroSubgroup =
        (generalLinearIwahoriPoints F N).map (MulAut.conj c).toMonoidHom := by
    intro x₀ hx₀
    let x₁ : (D.base.basedTransport σ _ hσ).Apartment :=
      D.base.toValuationBuildingData.basedApartmentEquiv σ _ hσ x₀
    have hx₁ : ∀ ψ ∈ (D.base.basedTransport σ _ hσ).affineRoots, ψ x₁ ≠ 0 := by
      change ∀ ψ ∈ (D.base.toValuationBuildingData.basedTransport σ _ hσ).affineRoots, ψ x₁ ≠ 0
      rw [← D.base.toValuationBuildingData.transportedRoots_basedApartmentEquiv σ _ hσ]
      rintro _ ⟨ψ, hψ, rfl⟩
      change ψ ((D.base.toValuationBuildingData.basedApartmentEquiv σ _ hσ).symm
        (D.base.toValuationBuildingData.basedApartmentEquiv σ _ hσ x₀)) ≠ 0
      rw [AffineEquiv.symm_apply_apply]
      exact hx₀ ψ hψ
    obtain ⟨y, hy⟩ := exists_rootValue_eq_sub (D.base.basedTransport σ _ hσ).apartment x₁
    have hnonint :=
      (forall_affineRoot_ne_zero_iff (D.base.basedTransport σ _ hσ).apartment x₁).1 hx₁
    obtain ⟨a, π, hπ⟩ := exists_floor_perm_of_forall_ne_intCast y
      (fun k l hkl m hm => hnonint k l hkl m (by rw [hy]; exact hm))
    have hQ := nonnegativeRootSubgroup_singleton_eq_of_chamber D.base σ _ hσ x₁ a π
      (fun k l hkl n => by rw [hy]; exact hπ k l hkl n)
    have hzf : (D.base.basedTransport σ _ hσ).pointwiseFixer
          {(D.base.basedTransport σ _ hσ).apartmentMap x₁} ⊓
          (D.base.basedTransport σ _ hσ).zeroSubgroup =
        (generalLinearIwahoriPoints F N).map
          (MulAut.conj (toMatrixGL.symm (diagGL (uniformizerDiag (F := F) a)) *
            toMatrixGL.symm (permGL π))).toMonoidHom := by
      rw [← hQ, ← hZ' {x₁} (Set.singleton_nonempty _) (fun f =>
          ⟨f x₁, by rintro _ ⟨z, hz, rfl⟩; exact le_of_eq (congrArg f hz)⟩),
        ParahoricBuildingData.zeroFixer, Set.image_singleton, inf_comm]
    refine ⟨g₀⁻¹ * (toMatrixGL.symm (diagGL (uniformizerDiag (F := F) a)) *
      toMatrixGL.symm (permGL π)), ?_⟩
    have hmap : (D.base.pointwiseFixer {D.base.apartmentMap x₀} ⊓ D.base.zeroSubgroup).map
        (MulAut.conj g₀).toMonoidHom =
        (generalLinearIwahoriPoints F N).map
          (MulAut.conj (toMatrixGL.symm (diagGL (uniformizerDiag (F := F) a)) *
            toMatrixGL.symm (permGL π))).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g₀).injective, ← hφ,
        D.base.toValuationBuildingData.map_pointwiseFixer_basedTransport σ _ hσ,
        ← ParahoricBuildingData.basedTransport_zeroSubgroup, Set.image_singleton,
        ValuationBuildingData.basedBuildingEquiv_apartmentMap]
      exact hzf
    have hback := congrArg (fun Q => Q.map (MulAut.conj g₀⁻¹).toMonoidHom) hmap
    rw [ParahoricBuildingData.map_conj_map_conj, inv_mul_cancel,
      ParahoricBuildingData.map_conj_one] at hback
    rw [hback, ParahoricBuildingData.map_conj_map_conj]
  -- The parahoric of a translated chamber of the apartment.
  have hchamber : ∀ (h : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
      (x₀ : D.base.Apartment), (∀ ψ ∈ D.base.affineRoots, ψ x₀ ≠ 0) →
      ∀ C : BuildingFacet D.base.toValuationBuildingData,
        C.val = (fun z => h • D.base.apartmentMap z) ''
          AffineRootSystem.facet D.base.affineRoots x₀ →
        D.parahoric C = (D.base.pointwiseFixer {D.base.apartmentMap x₀} ⊓
          D.base.zeroSubgroup).map (MulAut.conj h).toMonoidHom := by
    intro h x₀ hx₀ C hC
    have hzf0 := D.base.zeroFixer_facet_eq_nonnegativeRootSubgroup_singleton hA hZ hx₀
    rw [← hZ {x₀} (Set.singleton_nonempty _) (fun f =>
      ⟨f x₀, by rintro _ ⟨z, hz, rfl⟩; exact le_of_eq (congrArg f hz)⟩)] at hzf0
    unfold ParahoricBuildingData.zeroFixer at hzf0
    rw [Set.image_singleton] at hzf0
    rw [D.parahoric_eq_pointwiseFixer_inf hD C, hC, ← Set.image_image (fun w => h • w),
      D.base.pointwiseFixer_smul_image_inf_zeroSubgroup, inf_comm, hzf0, inf_comm]
  refine ⟨?_, ?_⟩
  · rintro C ⟨h, _, ⟨x₀, hx₀, rfl⟩, hC⟩
    obtain ⟨c, hc⟩ := key x₀ hx₀
    refine ⟨h * c, ?_⟩
    rw [hchamber h x₀ hx₀ C hC, hc, ParahoricBuildingData.map_conj_map_conj]
  · intro g
    -- A point of the apartment of `D` on no root hyperplane.
    obtain ⟨z, hz⟩ := exists_forall_sub_ne_intCast (N := N)
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : (D.base.basedTransport σ _ hσ).Apartment,
        ∀ k l, rootValue (D.base.basedTransport σ _ hσ).apartment x₁ k l = z k - z l :=
      exists_rootValue_eq_sub_of _ z
    have hx₁r : ∀ ψ ∈ (D.base.basedTransport σ _ hσ).affineRoots, ψ x₁ ≠ 0 :=
      (forall_affineRoot_ne_zero_iff (D.base.basedTransport σ _ hσ).apartment x₁).2
        fun k l hkl m => by rw [hx₁]; exact hz k l hkl m
    let x₀ := (D.base.toValuationBuildingData.basedApartmentEquiv σ _ hσ).symm x₁
    have hx₀ : ∀ ψ ∈ D.base.affineRoots, ψ x₀ ≠ 0 := by
      intro ψ hψ
      have hmem : AffineRootSystem.affineFunctionalTransport
          (D.base.toValuationBuildingData.basedApartmentEquiv σ _ hσ) ψ ∈
          (D.base.toValuationBuildingData.basedTransport σ _ hσ).affineRoots := by
        rw [← D.base.toValuationBuildingData.transportedRoots_basedApartmentEquiv σ _ hσ]
        exact ⟨ψ, hψ, rfl⟩
      exact hx₁r _ hmem
    obtain ⟨c, hc⟩ := key x₀ hx₀
    have hCa : AffineRootSystem.IsChamber D.base.affineRoots
        (AffineRootSystem.facet D.base.affineRoots x₀) := ⟨x₀, hx₀, rfl⟩
    let C : BuildingFacet D.base.toValuationBuildingData :=
      ⟨(fun z => (g * c⁻¹) • D.base.apartmentMap z) ''
        AffineRootSystem.facet D.base.affineRoots x₀, ⟨g * c⁻¹, _, hCa.isFacet, rfl⟩⟩
    refine ⟨C, ⟨g * c⁻¹, _, hCa, rfl⟩, ?_⟩
    rw [hchamber (g * c⁻¹) x₀ hx₀ C rfl, hc, ParahoricBuildingData.map_conj_map_conj,
      inv_mul_cancel_right]

end Langlands.Geometry.Building
