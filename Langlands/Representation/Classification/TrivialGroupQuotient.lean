import Langlands.Representation.Classification.ConstituentRelations

/-! Quotients of a scalar line for a trivial group. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

/-- The map from a scalar line sending its scalar coordinate to a multiple of
`v` intertwines any two representations of a trivial group. -/
def scalarLineIntertwiningMap
    {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (π : Representation ℂ G W)
    (e : V ≃ₗ[ℂ] ℂ) (v : W) : ρ.IntertwiningMap π :=
  { toLinearMap := (LinearMap.id.smulRight v).comp e.toLinearMap
    isIntertwining' g := by
      rw [Subsingleton.elim g 1, map_one, map_one]
      rfl }

/-- For a trivial group, a representation on a scalar line surjects onto every
irreducible representation. -/
theorem isIrreducibleQuotient_of_subsingleton_linearEquiv
    {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (π : Representation ℂ G W)
    (hπ : Representation.IsIrreducible π) (e : V ≃ₗ[ℂ] ℂ) :
    IsIrreducibleQuotient ρ π := by
  let := hπ
  let : Nontrivial W :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  let q := scalarLineIntertwiningMap ρ π e v
  have hq : q ≠ 0 := by
    intro hzero
    apply hv
    have h := congrArg
      (fun a : ρ.IntertwiningMap π => a (e.symm 1)) hzero
    simpa [q, scalarLineIntertwiningMap] using h
  exact ⟨hπ, q,
    (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right hq⟩

end Langlands.Classification
