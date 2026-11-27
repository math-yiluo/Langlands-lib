import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-! # Restriction of Galois groups along a scalar tower -/

open IntermediateField
open scoped Topology

namespace Langlands.FieldTheory

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  (N : IntermediateField K L)

local notation "ρ" =>
  MonoidHom.comp (AlgEquiv.restrictNormalHom N)
    (AlgEquiv.restrictScalarsHom K : Gal(L/F) →* Gal(L/K))

/-- Restriction to a normal intermediate field over the smaller base is continuous for
the Krull topologies when the ambient extension over the larger base is algebraic. -/
theorem continuous_restrictNormalHom_of_tower [Normal K N] [Algebra.IsAlgebraic F L] :
    Continuous ρ := by
  classical
  apply continuous_of_continuousAt_one ρ
  change Filter.Tendsto ρ (𝓝 1) (𝓝 (ρ 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K N U).mp hU
  let := hE
  obtain ⟨s, hs⟩ := (essFiniteType_iff (K := E)).mp inferInstance
  let M := adjoin F (↑(s.image N.val) : Set L)
  have hM : FiniteDimensional F M :=
    finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  apply (krullTopology_mem_nhds_one_iff F L _).mpr
  refine ⟨M, hM, fun σ hσ => hEU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff, ← hs]
  apply (forall_mem_adjoin_smul_eq_self_iff K (ρ σ)).mpr
  intro x hx
  apply Subtype.val_injective
  exact ((σ.restrictScalars K).restrictNormal_commutes N x).trans
    ((IntermediateField.mem_fixingSubgroup_iff M σ).mp hσ (x : L)
      (subset_adjoin F _ (Finset.mem_image_of_mem N.val hx)))

/-- If the smaller base is relatively separably closed in the larger base, restriction
to a Galois intermediate field over the smaller base is surjective. -/
theorem restrictNormalHom_surjective_of_separableClosure_eq_bot
    [IsGalois F L] [IsGalois K N] (hsep : separableClosure K F = ⊥) :
    Function.Surjective ρ := by
  let H : ClosedSubgroup Gal(N/K) :=
    ⟨MonoidHom.range ρ, (isCompact_range (continuous_restrictNormalHom_of_tower N)).isClosed⟩
  have hfixed : fixedField H.toSubgroup = ⊥ := by
    apply bot_unique
    intro x hx
    have h (σ : Gal(L/F)) : σ (x : L) = (x : L) := by
      have hx' := (mem_fixedField_iff H.toSubgroup x).mp hx (ρ σ) ⟨σ, rfl⟩
      exact ((σ.restrictScalars K).restrictNormal_commutes N x).symm.trans
        (congrArg Subtype.val hx')
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (x : L)).mpr h
    let ι := IsScalarTower.toAlgHom K F L
    have hysep : IsSeparable K y := by
      apply (isSeparable_map_iff ι ι.injective).mp
      change IsSeparable K (algebraMap F L y)
      rw [hy]
      exact (Algebra.IsSeparable.isSeparable K x).map N.val Subtype.val_injective
    obtain ⟨z, hz⟩ := mem_bot.mp (hsep.le (mem_separableClosure_iff.mpr hysep))
    exact mem_bot.mpr ⟨z, Subtype.val_injective <|
      (IsScalarTower.algebraMap_apply K F L z).trans
        ((congrArg (algebraMap F L) hz).trans hy)⟩
  apply MonoidHom.range_eq_top.mp
  change H.toSubgroup = ⊤
  rw [← InfiniteGalois.fixingSubgroup_fixedField H, hfixed, fixingSubgroup_bot]

/-- If the intermediate field generates the ambient field over the larger base,
restriction is injective. -/
theorem restrictNormalHom_injective_of_adjoin_eq_top [Normal K N]
    (hgen : adjoin F (N : Set L) = ⊤) : Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro σ hσ
  change ρ σ = 1 at hσ
  have hfix : ∀ x ∈ adjoin F (N : Set L), σ • x = x := by
    apply (forall_mem_adjoin_smul_eq_self_iff F σ).mpr
    intro x hx
    let y : N := ⟨x, hx⟩
    have hy : (ρ σ y : L) = x := congrArg (fun τ : Gal(N/K) => (τ y : L)) hσ
    exact ((σ.restrictScalars K).restrictNormal_commutes N y).symm.trans hy
  rw [hgen] at hfix
  exact AlgEquiv.ext fun x => hfix x mem_top

/-- Restriction is a homeomorphism if the smaller base is relatively separably closed
and the intermediate Galois field generates the ambient field over the larger base. -/
theorem isHomeomorph_restrictNormalHom_of_tower [IsGalois F L] [IsGalois K N]
    (hsep : separableClosure K F = ⊥) (hgen : adjoin F (N : Set L) = ⊤) :
    IsHomeomorph ρ :=
  isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_restrictNormalHom_of_tower N, restrictNormalHom_injective_of_adjoin_eq_top N hgen,
      restrictNormalHom_surjective_of_separableClosure_eq_bot N hsep⟩

end Langlands.FieldTheory
