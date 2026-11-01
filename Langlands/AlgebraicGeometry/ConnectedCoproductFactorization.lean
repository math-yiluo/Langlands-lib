import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.Connected.Clopen

/-! # Actual factorization of connected-source maps to scheme coproducts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry

/-- A morphism from a connected scheme to a scheme coproduct factors through
one actual summand as a scheme morphism. -/
theorem connectedHom_factor_coproduct {T : Scheme.{u}} [ConnectedSpace T]
    {I : Type u} (X : I → Scheme.{u}) (d : T ⟶ ∐ X) :
    ∃ i : I, ∃ a : T ⟶ X i, a ≫ Sigma.ι X i = d := by
  obtain ⟨i, g, _, hg⟩ :=
    ((AlgebraicGeometry.sigmaMk X).symm.continuous.comp d.continuous).exists_lift_sigma
  have hd (t : T) : d t = Sigma.ι X i (g t) := by
    have ht := congrArg (AlgebraicGeometry.sigmaMk X) (congrFun hg t)
    simpa only [Function.comp_apply, Homeomorph.apply_symm_apply,
      AlgebraicGeometry.sigmaMk_mk] using ht
  have hrange : Set.range d ⊆ Set.range (Sigma.ι X i) := by
    rintro _ ⟨t, rfl⟩
    exact ⟨g t, (hd t).symm⟩
  exact ⟨i, IsOpenImmersion.lift _ d hrange, IsOpenImmersion.lift_fac _ _ _⟩

/-- The summand selected by the proved factorization. Connectedness includes
nonemptiness; there is no assumption that the coproduct index is inhabited. -/
def connectedCoproductIndex {T : Scheme.{u}} [ConnectedSpace T]
    {I : Type u} (X : I → Scheme.{u}) (d : T ⟶ ∐ X) : I :=
  Classical.choose (connectedHom_factor_coproduct X d)

/-- The actual scheme morphism to the selected original summand. -/
def connectedCoproductLift {T : Scheme.{u}} [ConnectedSpace T]
    {I : Type u} (X : I → Scheme.{u}) (d : T ⟶ ∐ X) :
    T ⟶ X (connectedCoproductIndex X d) :=
  Classical.choose (Classical.choose_spec (connectedHom_factor_coproduct X d))

@[reassoc (attr := simp)] theorem connectedCoproductLift_comp
    {T : Scheme.{u}} [ConnectedSpace T]
    {I : Type u} (X : I → Scheme.{u}) (d : T ⟶ ∐ X) :
    connectedCoproductLift X d ≫ Sigma.ι X (connectedCoproductIndex X d) = d :=
  Classical.choose_spec (Classical.choose_spec (connectedHom_factor_coproduct X d))

end Langlands.AlgebraicGeometry
