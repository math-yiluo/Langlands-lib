import Langlands.GroupScheme.Reductive.CenterBaseChangeProof

/-! # Finite scheme-theoretic centres under arbitrary base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G Z : GroupScheme S}

/-- A supplied finite representative of the full scheme-theoretic centre. -/
structure FiniteCenter (G : GroupScheme S) where
  group : GroupScheme S
  inclusion : group ⟶ G
  isCenter : IsSchemeTheoreticCenter inclusion
  finite : IsFinite group.X.hom

/-- An actual representative of the full centre remains one under base change. -/
theorem IsSchemeTheoreticCenter.baseChange {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) (b : S' ⟶ S) :
    IsSchemeTheoreticCenter ((GroupScheme.baseChange b).map z) := by
  refine ⟨hz.1.baseChange b, ?_⟩
  rw [SubgroupFunctor.range_baseChangeHom, hz.2, center_baseChange]

/-- Pull back a supplied finite centre representative, including its actual inclusion. -/
noncomputable def FiniteCenter.baseChange (C : FiniteCenter G) (b : S' ⟶ S) :
    FiniteCenter ((GroupScheme.baseChange b).obj G) := by
  let : IsFinite C.group.X.hom := C.finite
  refine ⟨(GroupScheme.baseChange b).obj C.group,
    (GroupScheme.baseChange b).map C.inclusion, C.isCenter.baseChange b, ?_⟩
  change IsFinite (Limits.pullback.snd C.group.X.hom b)
  infer_instance

/-- A supplied finite centre representative witnesses the existing existential predicate. -/
theorem FiniteCenter.hasFiniteCenter (C : FiniteCenter G) : HasFiniteCenter G :=
  ⟨C.group, C.inclusion, C.isCenter, C.finite⟩

/-- The entire finite scheme-theoretic centre is preserved by arbitrary base change. -/
theorem HasFiniteCenter.baseChange (h : HasFiniteCenter G) (b : S' ⟶ S) :
    HasFiniteCenter ((GroupScheme.baseChange b).obj G) := by
  obtain ⟨Z, z, hz, hfin⟩ := h
  exact (FiniteCenter.baseChange (⟨Z, z, hz, hfin⟩ : FiniteCenter G) b).hasFiniteCenter

end Langlands.GroupScheme
