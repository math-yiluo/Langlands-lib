import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! # Algebraic restriction of isotypic parts -/

noncomputable section
universe uR uM uN uS uG uV uW uU
set_option autoImplicit false

namespace Langlands.CompactSplitting

section Modules

variable (R : Type uR) [Ring R]
  (M : Type uM) [AddCommGroup M] [Module R M]
  (S : Type uS) [AddCommGroup S] [Module R S] [IsSimpleModule R S]

/-- For a simple source, the module isotypic component is the sum of all
linear-map ranges from that source. -/
theorem isotypicComponent_eq_iSup_range :
    isotypicComponent R M S = ⨆ f : S →ₗ[R] M, LinearMap.range f := by
  apply le_antisymm
  · apply sSup_le
    rintro P ⟨e⟩
    let f : S →ₗ[R] M := P.subtype.comp e.symm.toLinearMap
    apply le_trans _ (le_iSup (fun f : S →ₗ[R] M => LinearMap.range f) f)
    intro x hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    change (e.symm (e ⟨x, hx⟩)).val = x
    rw [LinearEquiv.symm_apply_apply]
  · apply iSup_le
    intro f
    rcases f.injective_or_eq_zero with hinj | hzero
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hinj).symm⟩
    · rw [hzero, LinearMap.range_zero]
      exact bot_le

variable {M}

/-- An injective module map pulls the isotypic component back to the
isotypic component of its domain. -/
theorem isotypicComponent_comap_of_injective
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    (isotypicComponent R N S).comap f = isotypicComponent R M S := by
  apply le_antisymm
  · let C := isotypicComponent R N S
    let P := C.comap f
    let j : P →ₗ[R] C := (f.comp P.subtype).codRestrict C (fun v : P => v.property)
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      exact hf (congrArg Subtype.val h)
    have : IsSemisimpleModule R P := IsSemisimpleModule.of_injective j hj
    have htype : IsIsotypicOfType R P S :=
      IsIsotypicOfType.of_injective (IsIsotypicOfType.isotypicComponent R N S) j hj
    have htop : (⊤ : Submodule R P) ≤ (isotypicComponent R M S).comap P.subtype := by
      rw [← IsSemisimpleModule.sSup_simples_eq_top R P]
      apply sSup_le
      intro Q hQ
      let : IsSimpleModule R Q := hQ
      obtain ⟨e⟩ := htype Q
      have hle : Q.map P.subtype ≤ isotypicComponent R M S :=
        le_sSup ⟨(Q.equivMapOfInjective _ P.subtype_injective).symm.trans e⟩
      exact Submodule.map_le_iff_le_comap.mp hle
    intro v hv
    exact htop (show (⟨v, hv⟩ : P) ∈ (⊤ : Submodule R P) from Submodule.mem_top)
  · exact LinearMap.le_comap_isotypicComponent S f

end Modules

section Representations

open scoped MonoidAlgebra

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

/-- The group-algebra isotypic component of a representation. -/
def isotypicModulePart (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Submodule ℂ[G] σ.asModule :=
  isotypicComponent ℂ[G] σ.asModule ρ.asModule

/-- The range of an intertwiner agrees with its group-algebra range. -/
theorem range_intertwining_eq_map_module_range
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : ρ.IntertwiningMap σ) :
    LinearMap.range f.toLinearMap =
      ((LinearMap.range (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)).restrictScalars ℂ).map σ.asModuleEquiv.toLinearMap := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨ρ.asModuleEquiv.symm v, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨ρ.asModuleEquiv u, rfl⟩

/-- For an irreducible source, the sum of intertwiner images is its
algebraic group-algebra isotypic component. -/
theorem isotypicPart_eq_map_modulePart
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] :
    isotypicPart ρ σ =
      ((isotypicModulePart ρ σ).restrictScalars ℂ).map σ.asModuleEquiv.toLinearMap := by
  rw [isotypicModulePart, isotypicComponent_eq_iSup_range,
    Submodule.restrictScalars_iSup, Submodule.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro f
    rw [range_intertwining_eq_map_module_range]
    exact le_iSup
      (fun g : ρ.asModule →ₗ[ℂ[G]] σ.asModule =>
        ((LinearMap.range g).restrictScalars ℂ).map σ.asModuleEquiv.toLinearMap)
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)
  · apply iSup_le
    intro f
    obtain ⟨g, rfl⟩ := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).surjective f
    rw [← range_intertwining_eq_map_module_range]
    exact range_le_isotypicPart ρ σ g

/-- Membership in the intertwiner-image sum is group-algebra isotypic membership. -/
theorem mem_isotypicPart_iff_modulePart
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] (w : W) :
    w ∈ isotypicPart ρ σ ↔ σ.asModuleEquiv.symm w ∈ isotypicModulePart ρ σ := by
  rw [isotypicPart_eq_map_modulePart, Submodule.mem_map_equiv]
  rfl

/-- An injective intertwiner pulls an irreducible isotypic part back exactly. -/
theorem isotypicPart_comap_of_injective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (τ : Representation ℂ G U) [ρ.IsIrreducible]
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    (isotypicPart ρ τ).comap f.toLinearMap = isotypicPart ρ σ := by
  let F := Representation.IntertwiningMap.equivLinearMapAsModule σ τ f
  have hF : Function.Injective F := hf
  have h := isotypicComponent_comap_of_injective ℂ[G] ρ.asModule F hF
  ext w
  change f w ∈ isotypicPart ρ τ ↔ w ∈ isotypicPart ρ σ
  rw [mem_isotypicPart_iff_modulePart, mem_isotypicPart_iff_modulePart]
  change F (σ.asModuleEquiv.symm w) ∈ isotypicComponent ℂ[G] τ.asModule ρ.asModule ↔
    σ.asModuleEquiv.symm w ∈ isotypicComponent ℂ[G] σ.asModule ρ.asModule
  rw [← h]
  rfl

/-- The image of the internal isotypic part is the ambient isotypic intersection. -/
theorem isotypicPart_map_of_injective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (τ : Representation ℂ G U) [ρ.IsIrreducible]
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    (isotypicPart ρ σ).map f.toLinearMap =
      isotypicPart ρ τ ⊓ LinearMap.range f.toLinearMap := by
  rw [← isotypicPart_comap_of_injective ρ σ τ f hf, Submodule.map_comap_eq, inf_comm]

end Representations

end Langlands.CompactSplitting
