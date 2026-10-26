import Langlands.AlgebraicGeometry.FiniteIrreducibleEndomorphismSurjectiveStatement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.Sober

/-! # Finite endomorphisms of irreducible Noetherian schemes are surjective -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

private lemma eq_of_specializes_self_of_discrete_fibres
    {T : Type u} [TopologicalSpace T] [T0Space T] [NoetherianSpace T]
    (g : T → T) (hg : Continuous g) (hd : ∀ y, IsDiscrete (g ⁻¹' {y}))
    (x : T) (hx : x ⤳ g x) : x = g x := by
  suffices H : ∀ C : Closeds T, ∀ z : T,
      Closeds.closure {z} = C → z ⤳ g z → z = g z from H _ x rfl hx
  intro C
  refine (wellFounded_lt (α := Closeds T)).induction
    (C := fun C => ∀ z : T, Closeds.closure {z} = C → z ⤳ g z → z = g z) C ?_
  intro C ih
  rintro z rfl hz
  by_cases he : z = g z
  · exact he
  have hlt : Closeds.closure {g z} < Closeds.closure {z} := by
    refine lt_of_le_not_ge hz.closure_subset ?_
    intro hrev
    exact he ((hz.antisymm (specializes_iff_closure_subset.mpr hrev)).eq)
  have hnext : g z = g (g z) := ih _ hlt _ rfl (hz.map hg)
  exact (hd (g z)).eq_of_specializes hz rfl hnext.symm

/-- Every finite endomorphism of an irreducible scheme with Noetherian point
space is surjective, in every universe. -/
theorem finiteIrreducibleEndomorphismSurjective :
    FiniteIrreducibleEndomorphismSurjectiveStatement.{u} := by
  intro X _ _ f hf
  let : IsFinite f := hf
  have hη : genericPoint X = f (genericPoint X) :=
    eq_of_specializes_self_of_discrete_fibres f f.continuous
      f.isDiscrete_preimage_singleton (genericPoint X) (genericPoint_specializes _)
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hmem : genericPoint X ∈ Set.range f := ⟨genericPoint X, hη.symm⟩
  have hfull : (Set.univ : Set X) ⊆ Set.range f := by
    rw [← genericPoint_closure X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem) hclosed
  exact ⟨fun x ↦ hfull (Set.mem_univ x)⟩

end Langlands.AlgebraicGeometry
