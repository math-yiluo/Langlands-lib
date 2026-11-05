import Langlands.Representation.CuspidalSupport.NormalRestrictionCovariance
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! # A single orbit of simple normal-subgroup types -/

noncomputable section

namespace Langlands.NormalRestrictionOrbit

open scoped MonoidAlgebra

universe uk uG uV

section Generic

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (H : Subgroup G) [H.Normal]

/-- The ambient translates of any simple subrepresentation span an irreducible
ambient representation. -/
theorem translates_span (hρ : ρ.IsIrreducible)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible) :
    (⨆ g : G, (FiniteIndexRestriction.translate ρ H g⁻¹ W).toSubmodule) = ⊤ := by
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero W.toRepresentation hW
  have hv' : (v : V) ≠ 0 := fun h => hv (Subtype.ext h)
  apply top_unique
  rw [← FiniteIndexRestriction.span_orbit_eq_top ρ hρ hv']
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, rfl⟩
  apply le_iSup (fun a : G =>
    (FiniteIndexRestriction.translate ρ H a⁻¹ W).toSubmodule) g
  change ρ g⁻¹ (ρ g v.val) ∈ W.toSubmodule
  rw [Representation.inv_self_apply]
  exact v.property

/-- The spanning identity also holds in the ambient subgroup group-algebra module. -/
theorem translates_asSubmodule_span (hρ : ρ.IsIrreducible)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible) :
    (⨆ g : G, (FiniteIndexRestriction.translate ρ H g⁻¹ W).asSubmodule) = ⊤ := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp H.subtype)
  have ht : (⨆ g : G, FiniteIndexRestriction.translate ρ H g⁻¹ W) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    rw [Langlands.Subrepresentation.toSubmodule_iSup, translates_span ρ H hρ W hW]
    rfl
  change (⨆ g : G, e (FiniteIndexRestriction.translate ρ H g⁻¹ W)) = ⊤
  rw [← e.map_iSup, ht, e.map_top]

/-- A group-algebra equivalence between invariant subspaces is a representation
equivalence for their original actions. -/
def equivOfAsSubmoduleEquiv {A : Type uG} [Group A]
    {τ : Representation k A V} (S T : Subrepresentation τ)
    (e : S.asSubmodule ≃ₗ[k[A]] T.asSubmodule) :
    Representation.Equiv S.toRepresentation T.toRepresentation := by
  let e' := (subrepresentationAsModuleEquiv S).trans
    (e.trans (subrepresentationAsModuleEquiv T).symm)
  let f := (Representation.IntertwiningMap.equivLinearMapAsModule
    S.toRepresentation T.toRepresentation).symm e'.toLinearMap
  exact f.ofBijective e'.bijective

end Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (H : Subgroup G) [H.Normal]

/-- Every two irreducible types in a normal restriction of an irreducible
representation differ by inverse conjugation. -/
theorem singleOrbit (hρ : ρ.IsIrreducible)
    (W₁ W₂ : Subrepresentation (ρ.comp H.subtype))
    (hW₁ : W₁.toRepresentation.IsIrreducible)
    (hW₂ : W₂.toRepresentation.IsIrreducible) :
    ∃ g : G, Nonempty (Representation.Equiv (W₁.toRepresentation.comp
      (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom)
      W₂.toRepresentation) := by
  let s : Set (Submodule ℂ[H] (Representation.asModule (ρ.comp H.subtype))) :=
    Set.range fun g : G => (FiniteIndexRestriction.translate ρ H g⁻¹ W₁).asSubmodule
  let : IsSimpleModule ℂ[H] W₂.asSubmodule :=
    (isIrreducible_iff_isSimpleModule W₂).mp hW₂
  let : ∀ m : s, IsSimpleModule ℂ[H] m.val := by
    rintro ⟨m, g, rfl⟩
    exact (isIrreducible_iff_isSimpleModule _).mp
      (isIrreducible_translate ρ H g W₁ hW₁)
  have hs : sSup s = ⊤ := by
    change sSup (Set.range fun g : G =>
      (FiniteIndexRestriction.translate ρ H g⁻¹ W₁).asSubmodule) = ⊤
    rw [sSup_range]
    exact translates_asSubmodule_span ρ H hρ W₁ hW₁
  obtain ⟨_, ⟨g, rfl⟩, ⟨e⟩⟩ := W₂.asSubmodule.linearEquiv_of_sSup_eq_top s hs
  exact ⟨g, ⟨(translateEquiv ρ H g W₁).trans
    (equivOfAsSubmoduleEquiv _ _ e.symm)⟩⟩

end Langlands.NormalRestrictionOrbit
