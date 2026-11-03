import Langlands.GroupScheme.Torus.NoTorusUnipotentStatement
import Langlands.GroupScheme.Torus.NoTorusBaseChangeStatement
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Unipotent.TorusHom

/-! # Reduction of the field-extension invariance of the absence of tori to Milne 17.81 -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A homomorphism whose image is trivial on every test scheme is the trivial homomorphism. -/
theorem SubgroupFunctor.eq_zero_of_range_eq_bot {S : Scheme.{u}} {H G : GroupScheme S}
    {f : H ⟶ G} (hf : SubgroupFunctor.range f = ⊥) : f = 0 := by
  have h : f.hom.hom ∈ (SubgroupFunctor.range f).carrier H.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  rw [hf, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at h
  apply (Grp.forget _).map_injective
  exact h

/-- Milne, Proposition 17.81 (in the form `NoTorusUnipotentStatement`), implies that the absence
of tori in a smooth affine group scheme is invariant under every field extension
(`NoTorusBaseChangeStatement`). -/
def NoTorusBaseChangeReductionStatement : Prop :=
  NoTorusUnipotentStatement.{u} → NoTorusBaseChangeStatement.{u}

/-- Proof of `NoTorusBaseChangeReductionStatement`. It passes through the identity component,
using invariance of unipotence under field extension (Milne 14.9) and triviality of
homomorphisms from tori to unipotent groups (Milne 14.18(b)). -/
theorem noTorusBaseChangeReduction : NoTorusBaseChangeReductionStatement.{u} := by
  intro h k K _ _ _ Q _ _ hQ T hT g
  -- The identity component of `Q` receives only trivial homomorphisms from tori.
  have hQ0 : IsUnipotent (identityComponent Q) := by
    refine h k (identityComponent Q) fun T' hT' g' => ?_
    have h0 : g' ≫ identityComponentι Q = 0 ≫ identityComponentι Q :=
      (SubgroupFunctor.eq_zero_of_range_eq_bot (hQ T' hT' _)).trans zero_comp.symm
    rw [cancel_mono] at h0
    rw [h0, SubgroupFunctor.range_zero]
  let φ : k →+* K := algebraMap k K
  have hQ0K : IsUnipotent ((GroupScheme.baseChange (IdentityComponent.specMap φ)).obj
      (identityComponent Q)) := hQ0.baseChange
  have := hT.connectedSpace
  -- Tori are connected, so `g` factors through `(Q_K)⁰ ≅ (Q⁰)_K`.
  have hg : g = (IdentityComponent.factor _ g ≫ (IdentityComponent.baseChangeIso Q φ).inv) ≫
      (IdentityComponent.baseChangeIso Q φ).hom ≫ identityComponentι _ := by
    simp
  rw [hg, hT.hom_eq_zero_of_isUnipotent hQ0K
    (IdentityComponent.factor _ g ≫ (IdentityComponent.baseChangeIso Q φ).inv), zero_comp,
    SubgroupFunctor.range_zero]

end Langlands.GroupScheme
