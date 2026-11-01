import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteStatement
import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso
import Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper

/-! # Proper coherent cohomology from actual alternating Čech complexes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open CechResolution

private def cechHomologySuccEquiv {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (𝒰 : X.OrderedAffineCover) (M : X.Modules) (n : ℕ) :
    (cechCochainComplex f 𝒰 M).homology (n + 1) ≃ₗ[R]
      (OModulePresheaf.ofModules f M).HSucc 𝒰 n := by
  let K := cechCochainComplex f 𝒰 M
  let F := OModulePresheaf.ofModules f M
  let S := ModuleCat.shortComplexOfCompEqZero (F.d 𝒰 n) (F.d 𝒰 (n + 1))
    (F.d_comp_d 𝒰 n)
  have h₀ : K.d n (n + 1) = ModuleCat.ofHom (F.d 𝒰 n) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R (F.cochain 𝒰 i))
      (fun i => ModuleCat.ofHom (F.d 𝒰 i)) n
  have h₁ : K.d (n + 1) (n + 1 + 1) = ModuleCat.ofHom (F.d 𝒰 (n + 1)) :=
    CochainComplex.of_d (V := ModuleCat.{u} R)
      (fun i => ModuleCat.of R (F.cochain 𝒰 i))
      (fun i => ModuleCat.ofHom (F.d 𝒰 i)) (n + 1)
  let e : K.sc' n (n + 1) (n + 1 + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom]; exact h₀.symm)
      (by simp only [Iso.refl_hom]; exact h₁.symm)
  exact (K.homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫ S.moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)

/-- Proper quasi-coherent modules with finite affine sections have finite,
bounded actual cohomology. -/
theorem properCoherentCohomologyFinite : ProperCoherentCohomologyFiniteStatement.{u} := by
  intro R _ _ X f hp M hq hc
  classical
  let := hp
  let := hq
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  let F := OModulePresheaf.ofModules f M
  let K := cechCochainComplex f 𝒰 M
  have hFq : F.IsQuasicoherent := by
    intro U a
    constructor
    · intro x
      obtain ⟨n, t, ht⟩ := AffineVanishing.exists_pow_smul_eq_res_aux U.2 M a x
      refine ⟨n, t, ?_⟩
      change M.presheaf.map (homOfLE (X.basicOpen_le a)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (a ^ n) • x
      rw [map_pow]
      exact ht
    · exact AffineVanishing.exists_pow_smul_eq_zero_aux U.2 M a
  have hFc : F.IsCoherent := hc
  have hfin : F.CechFinite 𝒰 := F.cechFinite_of_isProper hFc hFq 𝒰
  constructor
  · intro n
    have hK : Module.Finite R (K.homology n) := by
      cases n with
      | zero =>
          let S := K.sc' 0 0 1
          have h₀ : K.d 0 1 = ModuleCat.ofHom (F.d 𝒰 0) :=
            CochainComplex.of_d (V := ModuleCat.{u} R)
              (fun i => ModuleCat.of R (F.cochain 𝒰 i))
              (fun i => ModuleCat.ofHom (F.d 𝒰 i)) 0
          let : Module.Finite R (LinearMap.ker S.g.hom) := by
            change Module.Finite R (LinearMap.ker (K.d 0 1).hom)
            rw [h₀]
            exact hfin.1
          let : Module.Finite R S.moduleCatLeftHomologyData.H := by
            change Module.Finite R (LinearMap.ker S.g.hom ⧸
              LinearMap.range S.moduleCatToCycles)
            infer_instance
          exact Module.Finite.equiv
            ((K.homologyIsoSc' 0 0 1 (by simp) (by simp)) ≪≫
              S.moduleCatHomologyIso).toLinearEquiv.symm
      | succ n =>
          let : Module.Finite R (F.HSucc 𝒰 n) := hfin.2 n
          exact Module.Finite.equiv (cechHomologySuccEquiv f 𝒰 M n).symm
    exact Module.Finite.equiv (cechCohomologyIso f 𝒰 M n).toLinearEquiv
  · refine ⟨Fintype.card 𝒰.ι, fun n hn => ?_⟩
    have hz : IsZero (K.X n) := by
      let : IsEmpty (𝒰.Idx n) := ⟨fun s => by
        have hs := Fintype.card_le_of_injective s.1 s.2.injective
        simp only [Fintype.card_fin] at hs
        omega⟩
      change IsZero (ModuleCat.of R (F.cochain 𝒰 n))
      exact ModuleCat.isZero_of_subsingleton _
    exact IsZero.of_iso
      (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) hz)
      (cechCohomologyIso f 𝒰 M n).symm

end Langlands.AlgebraicGeometry.Modules
