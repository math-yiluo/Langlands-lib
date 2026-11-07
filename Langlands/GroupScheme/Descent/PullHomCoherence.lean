import Langlands.GroupScheme.Descent.DatumRelation
import Langlands.GroupScheme.Descent.ComponentCoverLifts

/-! # Coherence of actual pullback transport -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme.Descent
variable {S T U V : Scheme.{u}}

/-- Successive actual pullback transport agrees with direct transport. -/
theorem pullHom_pullHom (q : U ⟶ T) (r : V ⟶ U)
    {f g : T ⟶ S} {f' g' : U ⟶ S} {f'' g'' : V ⟶ S}
    (hf : q ≫ f = f') (hg : q ≫ g = g')
    (hrf : r ≫ f' = f'') (hrg : r ≫ g' = g'')
    {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H) :
    pullHom r hrf hrg (pullHom q hf hg a) =
      pullHom (r ≫ q)
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hf).trans hrf))
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hg).trans hrg)) a := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hl := pullHom_eval r hrf hrg (pullHom q hf hg a)
      (pullback.fst G.X.hom f'') (pullback.snd G.X.hom f'') pullback.condition
    rw [pullback.lift_fst_snd, Category.id_comp, pullHom_eval q hf hg] at hl
    have hd := pullHom_eval (r ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hf).trans hrf))
      ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hg).trans hrg)) a
      (pullback.fst G.X.hom f'') (pullback.snd G.X.hom f'') pullback.condition
    rw [pullback.lift_fst_snd, Category.id_comp] at hd
    exact hl.trans (by simpa only [Category.assoc] using hd.symm)
  · exact (Over.w (pullHom r hrf hrg (pullHom q hf hg a)).hom.hom).trans
      (Over.w (pullHom (r ≫ q)
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hf).trans hrf))
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hg).trans hrg)) a).hom.hom).symm

/-- The same coherence for actual isomorphisms. -/
theorem pullIso_pullIso (q : U ⟶ T) (r : V ⟶ U)
    {f g : T ⟶ S} {f' g' : U ⟶ S} {f'' g'' : V ⟶ S}
    (hf : q ≫ f = f') (hg : q ≫ g = g')
    (hrf : r ≫ f' = f'') (hrg : r ≫ g' = g'')
    {G H : GroupScheme S}
    (a : (baseChange f).obj G ≅ (baseChange g).obj H) :
    pullIso r hrf hrg (pullIso q hf hg a) =
      pullIso (r ≫ q)
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hf).trans hrf))
        ((Category.assoc _ _ _).trans ((congrArg (fun b => r ≫ b) hg).trans hrg)) a := by
  apply Iso.ext
  exact pullHom_pullHom q r hf hg hrf hrg a.hom

namespace FiniteComponents

variable {I : Type} [Finite I] {Z : I → Scheme.{u}}
    (q : ∀ i, Z i ⟶ T) [IsIso (Sigma.desc q)]
    {f g : T ⟶ S} {fi gi : ∀ i, Z i ⟶ S}
    (hf : ∀ i, q i ≫ f = fi i) (hg : ∀ i, q i ≫ g = gi i)
    {G H : GroupScheme S}

/-- Assemble actual isomorphisms with explicitly specified component endpoints. -/
def pullbackIsoAlong
    (a : ∀ i, (baseChange (fi i)).obj G ≅ (baseChange (gi i)).obj H) :
    (baseChange f).obj G ≅ (baseChange g).obj H :=
  groupIso q (fun i =>
    pullbackComparison f (q i) (fi i) (hf i) G ≪≫ a i ≪≫
      (pullbackComparison g (q i) (gi i) (hg i) H).symm)

@[simp] theorem pullIso_pullbackIsoAlong
    (a : ∀ i, (baseChange (fi i)).obj G ≅ (baseChange (gi i)).obj H) (i : I) :
    pullIso (q i) (hf i) (hg i) (pullbackIsoAlong q hf hg a) = a i := by
  simp [pullIso, pullbackIsoAlong]

/-- Restrictions with specified endpoints jointly detect actual morphisms. -/
theorem pullHom_ext_along
    {a b : (baseChange f).obj G ⟶ (baseChange g).obj H}
    (h : ∀ i, pullHom (q i) (hf i) (hg i) a =
      pullHom (q i) (hf i) (hg i) b) : a = b := by
  apply groupHom_ext q
  intro i
  apply (cancel_epi (pullbackComparison f (q i) (fi i) (hf i) G).inv).mp
  apply (cancel_mono (pullbackComparison g (q i) (gi i) (hg i) H).hom).mp
  exact h i

end FiniteComponents
end Langlands.GroupScheme.Descent
