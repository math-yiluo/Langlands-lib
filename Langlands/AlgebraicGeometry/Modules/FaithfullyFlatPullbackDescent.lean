import Langlands.AlgebraicGeometry.Modules.FlatPullbackExactProof
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison

/-! # Descent for ordinary module pullback along flat surjections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The actual pullback--pushforward comonad on modules on the source. -/
abbrev modulePullbackDescentComonad : Comonad X.Modules :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).toComonad

/-- A stalk map of a flat scheme morphism is faithfully flat, since it is local. -/
lemma faithfullyFlat_stalkMap [Flat p] (x : X) :
    (p.stalkMap x).hom.FaithfullyFlat := by
  algebraize [(p.stalkMap x).hom]
  exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
    (Flat.stalkMap p x) (p.toLRSHom.prop x)

/-- Ordinary pullback along a flat surjection reflects all module isomorphisms. -/
lemma pullback_reflectsIsomorphisms_of_flat_surjective [Flat p] [Surjective p] :
    (Scheme.Modules.pullback p).ReflectsIsomorphisms where
  reflects {M N} a ha := by
    apply (Langlands.SchemeModule.isIso_iff_stalk_isIso a).mpr
    intro y
    obtain ⟨x, rfl⟩ := p.surjective y
    have : IsIso ((stalkFunctor x).map ((Scheme.Modules.pullback p).map a)) :=
      Functor.map_isIso _ _
    have : IsIso ((ModuleCat.extendScalars (p.stalkMap x).hom).map
        ((stalkFunctor (p x)).map a)) :=
      (NatIso.isIso_map_iff (StalkPullback.pullbackStalkIso p x) a).mp this
    have : (ModuleCat.extendScalars (p.stalkMap x).hom).ReflectsIsomorphisms :=
      ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
        (faithfullyFlat_stalkMap p x)
    have h : IsIso ((stalkFunctor (p x)).map a) :=
      isIso_of_reflects_iso _ (ModuleCat.extendScalars (p.stalkMap x).hom)
    rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
    exact h

/-- Beck's theorem applies to ordinary pullback along every flat surjection. -/
@[instance_reducible]
def comonadicPullback_of_flat_surjective [Flat p] [Surjective p] :
    ComonadicLeftAdjoint (Scheme.Modules.pullback p) := by
  have := pullback_reflectsIsomorphisms_of_flat_surjective p
  have := flatPullbackExact X Y p inferInstance
  convert! Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩

/-- The comparison to the actual pullback--pushforward coalgebras is an equivalence. -/
lemma isEquivalence_modulePullbackComparison [Flat p] [Surjective p] :
    (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).IsEquivalence :=
  @ComonadicLeftAdjoint.eqv _ _ _ _ _ (comonadicPullback_of_flat_surjective p)

/-- Pullback along a flat surjection is faithful on all module morphisms. -/
lemma faithful_pullback_of_flat_surjective [Flat p] [Surjective p] :
    (Scheme.Modules.pullback p).Faithful := by
  have := isEquivalence_modulePullbackComparison p
  refine ⟨fun {M N} a b h ↦ ?_⟩
  apply (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction p)).map_injective
  ext1
  exact h

/-- Every coalgebra for the actual module pullback--pushforward comonad descends. -/
lemma exists_module_of_pullbackCoalgebra [Flat p] [Surjective p]
    (D : (modulePullbackDescentComonad p).Coalgebra) :
    ∃ M : Y.Modules,
      Nonempty ((Comonad.comparison
        (Scheme.Modules.pullbackPushforwardAdjunction p)).obj M ≅ D) := by
  have := isEquivalence_modulePullbackComparison p
  exact ⟨_, ⟨(Comonad.comparison
    (Scheme.Modules.pullbackPushforwardAdjunction p)).objObjPreimageIso D⟩⟩

end Langlands.AlgebraicGeometry.Modules
