import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Conjugation orbits of simple subrepresentations of a normal restriction

These algebraic helpers do not assert existence of a simple constituent.
-/

noncomputable section

namespace Langlands.NormalRestrictionOrbit

open scoped MonoidAlgebra

universe uk uG uV

section Modules

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The module of a subrepresentation is the corresponding ambient submodule. -/
def subrepresentationAsModuleEquiv (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[k[G]] S.asSubmodule := by
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  let j : S.toRepresentation.asModule →ₗ[k[G]] S.asSubmodule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ i).codRestrict
      S.asSubmodule (fun v => v.property)
  exact LinearEquiv.ofBijective j
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩

/-- Simplicity of an invariant subspace can be checked in the ambient module. -/
theorem isIrreducible_iff_isSimpleModule (S : Subrepresentation ρ) :
    S.toRepresentation.IsIrreducible ↔ IsSimpleModule k[G] S.asSubmodule := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (subrepresentationAsModuleEquiv S).toLinearMap.isSimpleModule_iff_of_bijective
    (subrepresentationAsModuleEquiv S).bijective

/-- An irreducible invariant subspace is an atom in the subrepresentation lattice. -/
theorem isAtom_of_isIrreducible (S : Subrepresentation ρ)
    (hS : S.toRepresentation.IsIrreducible) : IsAtom S := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  exact (e.isAtom_iff S).mp
    (isSimpleModule_iff_isAtom.mp ((isIrreducible_iff_isSimpleModule S).mp hS))

end Modules

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (H : Subgroup G) [H.Normal]

/-- The ambient action of `g` identifies the inverse-conjugate action on `W`
with the action on the translated subspace `ρ(g) W`. -/
def translateEquiv (g : G) (W : Subrepresentation (ρ.comp H.subtype)) :
    Representation.Equiv (W.toRepresentation.comp
      (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)
      (FiniteIndexRestriction.translate ρ H g⁻¹ W).toRepresentation := by
  let f : Representation.IntertwiningMap (W.toRepresentation.comp
      (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)
      (FiniteIndexRestriction.translate ρ H g⁻¹ W).toRepresentation :=
    { toLinearMap := ((ρ g).comp W.toSubmodule.subtype).codRestrict _ (fun w => by
        change ρ g⁻¹ (ρ g w.val) ∈ W.toSubmodule
        rw [Representation.inv_self_apply]
        exact w.property)
      isIntertwining' := fun h => by
        apply LinearMap.ext
        intro w
        apply Subtype.ext
        change ρ g (ρ (g⁻¹ * h.val * g) w.val) = ρ h.val (ρ g w.val)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        simp only [mul_inv_cancel_left, mul_assoc] }
  apply f.ofBijective
  constructor
  · intro w z heq
    apply Subtype.ext
    exact (ρ.apply_bijective g).injective (congrArg Subtype.val heq)
  · intro w
    refine ⟨⟨ρ g⁻¹ w.val, w.property⟩, ?_⟩
    apply Subtype.ext
    exact Representation.self_inv_apply ρ g w.val

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every ambient translate of an irreducible subgroup subrepresentation is irreducible. -/
theorem isIrreducible_translate (g : G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible) :
    (FiniteIndexRestriction.translate ρ H g⁻¹ W).toRepresentation.IsIrreducible := by
  apply FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom
  exact ((FiniteIndexRestriction.translateOrderIso ρ H g⁻¹).isAtom_iff W).mpr
    (isAtom_of_isIrreducible W hW)

/-- Every inverse-conjugate of an irreducible subgroup type occurs in the restriction. -/
theorem covariance (W : Subrepresentation (ρ.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible) (g : G) :
    ∃ W' : Subrepresentation (ρ.comp H.subtype), W'.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (W.toRepresentation.comp
        (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)
        W'.toRepresentation) :=
  ⟨FiniteIndexRestriction.translate ρ H g⁻¹ W,
    isIrreducible_translate ρ H g W hW, ⟨translateEquiv ρ H g W⟩⟩

end Langlands.NormalRestrictionOrbit
