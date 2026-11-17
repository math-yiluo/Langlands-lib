import Langlands.GroupScheme.Torus.DiscreteGaloisFiniteFactorizationStatement
import Langlands.Shimura.ContinuousGaloisAction

/-! # Finite Galois factorization of discrete integral representations -/

noncomputable section

universe u v

namespace Langlands.GroupScheme

/-- A smooth finitely generated integral absolute-Galois representation
descends through canonical restriction to a finite Galois subextension. -/
theorem discreteGaloisFiniteFactorization :
    DiscreteGaloisFiniteFactorizationStatement.{u, v} := by
  intro k _ M _ _ _ ρ hρ
  obtain ⟨U, hU⟩ :=
    Shimura.ContinuousGaloisAction.exists_openSubgroup_le_ker hρ
  obtain ⟨L, hfin, hnormal, hL⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k (SeparableClosure k)
      (U : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k))).mp
      (U.isOpen.mem_nhds U.one_mem)
  have : FiniteDimensional k L := hfin
  have : Normal k L := hnormal
  have : IsGalois k L := ⟨⟩
  refine ⟨L, hfin, inferInstance, ?_⟩
  let f : (SeparableClosure k ≃ₐ[k] SeparableClosure k) →* (L ≃ₐ[k] L) :=
    AlgEquiv.restrictNormalHom L
  have hf : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (SeparableClosure k)
  have hker : f.ker ≤ ρ.asGroupHom.ker := by
    intro σ hσ
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change ρ σ = (1 : Module.End ℤ M)
    apply MonoidHom.mem_ker.mp
    apply hU
    apply hL
    rwa [← IntermediateField.restrictNormalHom_ker L]
  let τ : (L ≃ₐ[k] L) →* Units (Module.End ℤ M) :=
    f.liftOfSurjective hf ⟨ρ.asGroupHom, hker⟩
  refine ⟨(Units.coeHom (Module.End ℤ M)).comp τ, ?_⟩
  apply MonoidHom.ext
  intro σ
  change ↑(τ (f σ)) = ρ σ
  simp only [τ, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, Representation.asGroupHom_apply]

end Langlands.GroupScheme
