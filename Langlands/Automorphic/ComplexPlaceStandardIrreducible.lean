import Langlands.Automorphic.PlaceIsotypicSimple
import Langlands.Representation.Archimedean.ComplexStandardScalarVector
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction

/-! # Standard modules embedded in isotypic place actions are irreducible

Let `V` carry a compact action `κ` of `U(n)` and a Lie action `π` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. Assume
that `V` has an irreducible stable subspace and that every subspace stable under `κ`, `π` and
the operators commuting with them is `⊥` or `⊤`. Then every `U(n)`-finite complex standard
module of `n` characters that embeds into `V` by an intertwining map is irreducible
(`isIrreducibleGKModule_of_embedding`). See the paired Markdown.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.PlaceIsotypic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Archimedean

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- The image of an injective intertwining map from a standard module is an atom among the
`opAlg κ π`-submodules. -/
theorem isAtom_range_of_embedding {W₀ : Submodule ℂ V} (hW₀ : PlaceComponent.IsIrreducible κ π W₀)
    (hcomm : ∀ Z : Submodule ℂ V,
      (∀ P : V →ₗ[ℂ] V, (∀ k y, P (κ k y) = κ k (P y)) → (∀ X y, P (π X y) = π X (P y)) →
        ∀ x ∈ Z, P x ∈ Z) →
      PlaceComponent.IsStable κ π Z → Z = ⊥ ∨ Z = ⊤)
    {ds : List ComplexCharacterData} (hlen : ds.length = n)
    {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}
    (hAinj : Function.Injective A) (hA : IsComplexStandardIntertwining n κ π ds A)
    (hMst : PlaceComponent.IsStable κ π (LinearMap.range A)) :
    IsAtom (toOpSubmodule (LinearMap.range A) hMst) := by
  obtain ⟨hss, hiso⟩ := isSemisimple_isotypic_of_commutant hW₀ hcomm
  have := isSimpleModule_toOpSubmodule hW₀
  set M := toOpSubmodule (LinearMap.range A) hMst with hM
  have hisoM : IsIsotypicOfType (opAlg κ π) M (toOpSubmodule W₀ hW₀.2.1) :=
    hiso.of_injective M.subtype M.injective_subtype
  let e : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) ≃ₗ[ℂ] M :=
    LinearEquiv.ofBijective
      { toFun := fun f => ⟨A f, f, rfl⟩
        map_add' := fun f g => Subtype.ext (map_add A f g)
        map_smul' := fun c f => Subtype.ext (map_smul A c f) }
      ⟨fun f g h => hAinj (congrArg Subtype.val h), fun m => by
        obtain ⟨f, hf⟩ := m.2
        exact ⟨f, Subtype.ext hf⟩⟩
  have he : ∀ f, ((e f : M) : V) = A f := fun f => rfl
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have heK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) f,
      e (complexStandardRep n ds k f) = (⟨κ k, compact_mem_opAlg κ π k⟩ : opAlg κ π) • e f := by
    intro k f
    apply Subtype.ext
    rw [he]
    exact hA.map_rep k f
  obtain ⟨f₀, hf₀0, hf₀⟩ := ComplexStandardScalarVector.exists_isScalarVector ds hlen
  have hm₀ : e f₀ ≠ 0 := fun h => hf₀0 (e.injective (h.trans (map_zero e).symm))
  have hscal : ∀ E : M →ₗ[opAlg κ π] M, ∃ a : ℂ, E (e f₀) = a • e f₀ := by
    intro E
    let E' : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
      e.symm.toLinearMap ∘ₗ (E.restrictScalars ℂ) ∘ₗ e.toLinearMap
    obtain ⟨a, ha⟩ := hf₀ E' (fun k f => by
      apply e.injective
      simp only [E', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        LinearMap.restrictScalars_apply]
      rw [heK, heK, LinearEquiv.apply_symm_apply, LinearMap.map_smul])
    refine ⟨a, ?_⟩
    have h := congrArg e ha
    simp only [E', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.restrictScalars_apply] at h
    rw [h, map_smul]
  exact isSimpleModule_iff_isAtom.mp (isSimpleModule_of_scalar hisoM hm₀ hscal)

/-- **Irreducibility of embedded standard modules.** -/
theorem isIrreducibleGKModule_of_embedding {W₀ : Submodule ℂ V}
    (hW₀ : PlaceComponent.IsIrreducible κ π W₀)
    (hcomm : ∀ Z : Submodule ℂ V,
      (∀ P : V →ₗ[ℂ] V, (∀ k y, P (κ k y) = κ k (P y)) → (∀ X y, P (π X y) = π X (P y)) →
        ∀ x ∈ Z, P x ∈ Z) →
      PlaceComponent.IsStable κ π Z → Z = ⊥ ∨ Z = ⊤)
    {ds : List ComplexCharacterData} (hlen : ds.length = n)
    {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}
    (hAinj : Function.Injective A) (hA : IsComplexStandardIntertwining n κ π ds A) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) := by
  have hMst : PlaceComponent.IsStable κ π (LinearMap.range A) := by
    refine ⟨fun k _ hx => ?_, fun Y _ hx => ?_⟩
    · obtain ⟨f, rfl⟩ := hx
      exact ⟨_, hA.map_rep k f⟩
    · obtain ⟨f, rfl⟩ := hx
      exact ⟨_, hA.map_lie Y f⟩
  have hatom := isAtom_range_of_embedding hW₀ hcomm hlen hAinj hA hMst
  refine ⟨complexStandardNontrivial n ds hlen, fun W hWk hWX => ?_⟩
  have hNst : PlaceComponent.IsStable κ π (W.map A) := by
    refine ⟨fun k _ hx => ?_, fun Y _ hx => ?_⟩
    · obtain ⟨f, hf, rfl⟩ := hx
      exact ⟨_, hWk k f hf, hA.map_rep k f⟩
    · obtain ⟨f, hf, rfl⟩ := hx
      exact ⟨_, hWX Y f hf, hA.map_lie Y f⟩
  have hNM : toOpSubmodule (W.map A) hNst ≤ toOpSubmodule (LinearMap.range A) hMst := by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f, rfl⟩
  rcases hNM.lt_or_eq with hlt | heq
  · left
    have h0 := hatom.2 _ hlt
    rw [eq_bot_iff]
    intro f hf
    have hAf : A f ∈ toOpSubmodule (W.map A) hNst := ⟨f, hf, rfl⟩
    rw [h0] at hAf
    rw [Submodule.mem_bot]
    exact hAinj (by rw [(Submodule.mem_bot _).1 hAf, map_zero])
  · right
    rw [eq_top_iff]
    intro f _
    have hAf : A f ∈ toOpSubmodule (LinearMap.range A) hMst := ⟨f, rfl⟩
    rw [← heq] at hAf
    obtain ⟨g, hg, hgf⟩ := hAf
    rwa [← hAinj hgf]

end Langlands.Automorphic.PlaceIsotypic
