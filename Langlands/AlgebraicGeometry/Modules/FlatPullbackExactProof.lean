import Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Proof that pullback of scheme modules along a flat morphism is exact -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

/-- Along a flat morphism, module pullback sends monomorphisms to monomorphisms: its stalk at
`x` is extension of scalars along the flat stalk map at `x`. -/
theorem pullback_map_mono_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] {M N : Y.Modules}
    (φ : M ⟶ N) [Mono φ] : Mono ((Scheme.Modules.pullback f).map φ) := by
  apply Langlands.SchemeModule.mono_of_stalk_injective
  intro x
  have : Mono ((stalkFunctor (f x)).map φ) :=
    (ModuleCat.mono_iff_injective _).2 (Langlands.SchemeModule.stalk_injective_of_mono φ (f x))
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{_, _, u} (f.stalkMap x).hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (Flat.stalkMap f x)
  have h := NatIso.naturality_2 (StalkPullback.pullbackStalkIso f x) φ
  have : Mono ((stalkFunctor x).map ((Scheme.Modules.pullback f).map φ)) := by
    change Mono ((Scheme.Modules.pullback f ⋙ stalkFunctor x).map φ)
    rw [← h, Functor.comp_map]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).1 this

/-- Pullback of scheme modules along a flat morphism preserves finite limits (Stacks, Lemma
17.20.2, tag 02N4, for schemes). -/
theorem flatPullbackExact : FlatPullbackExactStatement.{u} := by
  intro X Y f hf
  have : (Scheme.Modules.pullback f).PreservesMonomorphisms :=
    ⟨fun φ _ => pullback_map_mono_of_flat f φ⟩
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 inferInstance
    S hS).1, inferInstance⟩

/-- The closing theorem has exactly the type of the published statement. -/
example : FlatPullbackExactStatement.{u} := @flatPullbackExact.{u}

end Langlands.AlgebraicGeometry.Modules
