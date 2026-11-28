import Langlands.Correspondence.HenniartLadicFiniteInertiaProof
import Langlands.Weil.Local.SepClosedTopology
import Langlands.Weil.Representation.AbsoluteIrreducibility
import Langlands.Weil.Representation.ContinuityProof

/-! # Transport of irreducible ℓ-adic Galois classes to the local Weil group -/

noncomputable section

open scoped MonoidAlgebra TensorProduct

namespace Langlands.Henniart

open FiniteRepresentation LocalNumerical
open LocalGalois.SepClosed (absoluteInertia)
open Weil.Local.SepClosed

universe uK uΩ uW

private theorem irreducible_comp_of_denseRange
    {E : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module E V]
    (j : H →* G) (hdense : DenseRange j) (ρ : Representation E G V)
    (hcont : letI : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
      Continuous ρ)
    (hirr : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp j) := by
  let : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
  let : IsModuleTopology E (Module.End E V) := ⟨rfl⟩
  let : Nontrivial V := by
    let := hirr
    exact IsSimpleModule.nontrivial E[G] ρ.asModule
  let : Nontrivial (Subrepresentation (ρ.comp j)) :=
    ⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule E V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ := ⟨S.toSubmodule, by
    intro g v hv
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro φ hφ
    have hc : Continuous (fun a => φ (ρ a v)) :=
      (IsModuleTopology.continuous_of_linearMap (φ.comp (LinearMap.applyₗ v))).comp hcont
    refine hdense.induction_on g (p := fun a => φ (ρ a v) = 0)
      (isClosed_eq hc continuous_const) ?_
    intro w
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _ (S.apply_mem_toSubmodule w hv)⟩
  rcases hirr.eq_bot_or_eq_top T with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) h))

private theorem irreducible_extend_from_algClosed
    {E F : Type*} [Field E] [IsAlgClosed E] [Field F] [Algebra E F]
    {G : Type*} [Monoid G] (A : FiniteRepresentation E G)
    (hirr : Representation.IsIrreducible A.representation) :
    Representation.IsIrreducible (A.extendCoefficients F).representation := by
  apply irreducible_extendCoefficients_of_isAlgClosed E F A
  let e : (A.extendCoefficients E).representation.Equiv A.representation :=
    Representation.Equiv.mk (TensorProduct.lid E A) (by
      intro g
      apply TensorProduct.ext'
      intro a v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extendCoefficients_apply_tmul E A,
        TensorProduct.lid_tmul, map_smul])
  let f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hirr ⊢
  exact (f.isSimpleModule_iff_of_bijective e.bijective).mpr hirr

private theorem isContinuous_ladicScalarExtension_restrict
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (ι : PadicAlgCl ℓ →+* ℂ)
    (A : FiniteRepresentation.{0, uΩ, uW} (PadicAlgCl ℓ) (Ω ≃ₐ[K] Ω))
    (hcont : IsLadicContinuous ℓ A)
    (hfin : (A.representation '' (absoluteInertia K Ω : Set (Ω ≃ₐ[K] Ω))).Finite) :
    (ladicScalarExtension ℓ ι (A.restrict (localProjection K Ω).toMonoidHom)).IsContinuous := by
  let E := PadicAlgCl ℓ
  let W := localWeilGroup K Ω
  let I : OpenSubgroup W := ⟨localInertia K Ω, localInertia_isOpen K Ω⟩
  let restricted := A.representation.comp (localProjection K Ω).toMonoidHom
  let onInertia := restricted.comp I.toSubgroup.subtype
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  let : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
  let b := (Module.finBasis E (Module.End E A)).equivFun
  let : T2Space (Module.End E A) :=
    .of_injective_continuous b.injective (IsModuleTopology.continuous_of_linearMap b.toLinearMap)
  have hinertia : Continuous onInertia :=
    hcont.comp ((localProjection K Ω).continuous.comp continuous_subtype_val)
  have hfinite : (Set.range onInertia).Finite := hfin.subset (by
    rintro _ ⟨i, rfl⟩
    exact ⟨localProjection K Ω i, localProjection_mem_absoluteInertia K Ω i.property, rfl⟩)
  have hclosed : IsClosed (onInertia.ker : Set I) := isClosed_singleton.preimage hinertia
  have hopen : IsOpen (restricted.ker : Set W) :=
    (Weil.open_kernel_iff_open_restriction_kernel I restricted).mpr
      (Weil.open_kernel_of_finite_range_of_closed onInertia hfinite hclosed)
  let : Algebra E ℂ := ι.toAlgebra
  let B := ladicScalarExtension ℓ ι (A.restrict (localProjection K Ω).toMonoidHom)
  change B.IsContinuous
  let : TopologicalSpace (Module.End ℂ B) := moduleTopology ℂ (Module.End ℂ B)
  change Continuous B.representation
  apply Weil.continuous_of_open_kernel
  refine Subgroup.isOpen_mono ?_ hopen
  intro w hw
  change restricted w = 1 at hw
  change Module.End.baseChangeHom E ℂ A (restricted w) = 1
  rw [hw, map_one]

/-- Transport along the local Weil projection and the coefficient embedding
preserves rank and irreducibility and yields a continuous complex action. -/
theorem ladicWeilTransport : LadicWeilTransportStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ ℓ _ hℓp ι k ρ
  let := IsSepClosure.sep_closed K (K := Ω)
  obtain ⟨c, hrank⟩ := ρ
  obtain ⟨⟨A, hcont, hdef, hirr⟩, rfl⟩ := Quotient.exists_rep c
  let j := (localProjection K Ω).toMonoidHom
  let R := A.restrict j
  let B := ladicScalarExtension ℓ ι R
  have hfin := ladicFiniteInertia K Ω ℓ hℓp ι A hcont hdef hirr
  have hBcont : B.IsContinuous :=
    isContinuous_ladicScalarExtension_restrict K Ω ℓ ι A hcont hfin
  let : Algebra (PadicAlgCl ℓ) ℂ := ι.toAlgebra
  have hBirr : B.IsIrreducible := irreducible_extend_from_algClosed R
    (irreducible_comp_of_denseRange j (localProjection_denseRange K Ω) A.representation hcont hirr)
  refine ⟨⟨Quotient.mk _ ⟨B, hBcont, hBirr⟩, ?_⟩, rfl⟩
  change B.rank = (k.succPNat : ℕ)
  exact (rank_extendCoefficients ℂ R).trans hrank

end Langlands.Henniart
