import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctions

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Langlands.AlgebraicGeometry

/-- Proof of `FactorizationOfGlobalFunctions`: a morphism `g : X ⟶ Y` that agrees on points
with `p ≫ e ≫ g` equals it, when `e` is a section of `p` and every section map of `p` is an
isomorphism. -/
theorem factorizationOfGlobalFunctions : FactorizationOfGlobalFunctions.{u} := by
  intro X S Y p e g hep hp hg
  -- On every open `W` of `X` that is the preimage of its own preimage under `e`, the composite
  -- section map `Γ(X, W) ⟶ Γ(S, e ⁻¹ᵁ W) ⟶ Γ(X, p ⁻¹ᵁ e ⁻¹ᵁ W)` is the restriction along the
  -- equality of opens.
  have key : ∀ (W : X.Opens) (hW : p ⁻¹ᵁ (e ⁻¹ᵁ W) = W),
      e.app W ≫ p.app (e ⁻¹ᵁ W) = X.presheaf.map (eqToHom hW).op := by
    intro W hW
    obtain ⟨U, rfl⟩ : ∃ U, W = p ⁻¹ᵁ U := ⟨_, hW.symm⟩
    have := hp U
    have hU : e ⁻¹ᵁ (p ⁻¹ᵁ U) = U := by
      change (e ≫ p) ⁻¹ᵁ U = U
      rw [hep]
      rfl
    have h1 : p.app U ≫ e.app (p ⁻¹ᵁ U) = S.presheaf.map (eqToHom hU).op := by
      rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app hep]
      exact Category.id_comp _
    have h2 : e.app (p ⁻¹ᵁ U) = inv (p.app U) ≫ S.presheaf.map (eqToHom hU).op := by
      rw [IsIso.eq_inv_comp, h1]
    rw [h2, Category.assoc, Scheme.Hom.naturality, IsIso.inv_hom_id_assoc]
    rfl
  have hbase : g.base = (p ≫ e ≫ g).base := by
    ext x
    exact (hg x).trans (Scheme.Hom.comp_apply p (e ≫ g) x).symm
  refine Scheme.Hom.ext hbase fun V => ?_
  have hW : p ⁻¹ᵁ (e ⁻¹ᵁ (g ⁻¹ᵁ V)) = g ⁻¹ᵁ V :=
    (congrArg (fun f => (TopologicalSpace.Opens.map f).obj V) hbase).symm
  -- `(p ≫ e ≫ g).app V` unfolds definitionally to `g.app V ≫ e.app _ ≫ p.app _`.
  change _ = g.app V ≫ e.app (g ⁻¹ᵁ V) ≫ p.app (e ⁻¹ᵁ (g ⁻¹ᵁ V))
  rw [key _ hW]
  rfl

end Langlands.AlgebraicGeometry
