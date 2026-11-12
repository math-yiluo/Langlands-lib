import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.FrameCoord
import Langlands.AlgebraicGeometry.Picard.LineBundleStackBase
import Langlands.CategoryTheory.Sites.StackPullback
import Langlands.AlgebraicGeometry.Picard.ArtinianChartTestReduction

/-! # Module forms of actual Picard points -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open Langlands.CategoryTheory PicardGroupoid
open Langlands.Scheme.Modules.LineBundleFlatDescent

section Generic

variable {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
  {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} (R : ModuleRealization F)
  {U T : C} {ξ : F.obj (.mk (op (G.obj U)))} {η : F.obj (.mk (op (G.obj T)))}

/-- The module isomorphism of a point of a reindexed pseudofunctor. -/
def modIsoR {Z : Over T} (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) :
    (Scheme.Modules.pullback (G.map x.1)).obj (R.mod ξ) ≅
      (Scheme.Modules.pullback (G.map Z.hom)).obj (R.mod η) :=
  R.μIso (F := F) (f₁ := G.map x.1) (f₂ := G.map Z.hom) x.2.hom

/-- The point with a given base map and module isomorphism. -/
def mkPtR {Z : Over T} (a : Z.left ⟶ U)
    (ψ : (Scheme.Modules.pullback (G.map a)).obj (R.mod ξ) ≅
      (Scheme.Modules.pullback (G.map Z.hom)).obj (R.mod η)) :
    PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z :=
  ⟨a, R.isoOfIso (R.mapIso (G.map a) ξ ≪≫ ψ ≪≫ (R.mapIso (G.map Z.hom) η).symm)⟩

lemma modIsoR_mkPtR {Z : Over T} (a : Z.left ⟶ U)
    (ψ : (Scheme.Modules.pullback (G.map a)).obj (R.mod ξ) ≅
      (Scheme.Modules.pullback (G.map Z.hom)).obj (R.mod η)) :
    modIsoR G R (mkPtR G R a ψ) = ψ := by
  apply Iso.ext
  simp [modIsoR, mkPtR, ModuleRealization.μ]

lemma mkPtR_modIsoR {Z : Over T}
    (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) :
    mkPtR G R x.1 (modIsoR G R x) = x := by
  rcases x with ⟨a, e⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Iso.ext
  apply R.hom_ext
  simp [modIsoR, mkPtR, ModuleRealization.μ]

/-- The module form of the pullback of a morphism for a reindexed pseudofunctor with a module
realization is its transport. -/
lemma μ_pullHom_reindex {X₁ X₂ Y Y' : C} {M₁ : F.obj (.mk (op (G.obj X₁)))}
    {M₂ : F.obj (.mk (op (G.obj X₂)))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map (G.map f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map f₂).op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    R.μ (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := StackPullback.reindex G F) φ g gf₁
        gf₂ h₁ h₂) =
      tr (G.map g) (by rw [← G.map_comp, h₁]; rfl) (by rw [← G.map_comp, h₂]; rfl) (R.μ φ) := by
  rw [StackPullback.pullHom_reindex]
  exact R.μ_pullHom _ _ _ _ _ _

/-- The module isomorphism of a restricted point is the transport of the module isomorphism. -/
lemma modIsoR_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) :
    (modIsoR G R (PseudofunctorPointFiber.restrict (StackPullback.reindex G F) ξ η q x)).hom =
      tr (G.map q.left) (G.map_comp q.left x.1).symm (by rw [← Functor.map_comp, Over.w q])
        (modIsoR G R x).hom :=
  μ_pullHom_reindex G R x.2.hom q.left (q.left ≫ x.1) Z'.hom rfl (Over.w q)

/-- The module isomorphism of a pulled-back point with a prescribed base map. -/
lemma modIsoR_pullIso {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) (b : Z'.left ⟶ U)
    (hb : q.left ≫ x.1 = b) :
    (modIsoR G R (Z := Z')
        ⟨b, PseudofunctorPointFiber.pullIso x.2 q.left b Z'.hom hb q.w⟩).hom =
      tr (G.map q.left) (by rw [← Functor.map_comp, hb]) (by rw [← Functor.map_comp, Over.w q])
        (modIsoR G R x).hom :=
  μ_pullHom_reindex G R x.2.hom q.left b Z'.hom hb (Over.w q)

lemma restrict_eq_of_comp {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) (b : Z'.left ⟶ U)
    (hb : q.left ≫ x.1 = b) :
    PseudofunctorPointFiber.restrict (StackPullback.reindex G F) ξ η q x =
      ⟨b, PseudofunctorPointFiber.pullIso x.2 q.left b Z'.hom hb q.w⟩ := by
  subst hb
  rfl

end Generic

section Relative

variable {S X : Scheme.{u}} (f : X ⟶ S) {U T : Over S} {L : LineBundle ((relativeSpace f).obj U)}
  {N : LineBundle ((relativeSpace f).obj T)}

/-- The module isomorphism of an actual relative Picard point. -/
def modIso {Z : Over T}
    (x : PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk N) Z) :
    (Scheme.Modules.pullback ((relativeSpace f).map x.1)).obj L.obj ≅
      (Scheme.Modules.pullback ((relativeSpace f).map Z.hom)).obj N.obj :=
  modIsoR (relativeSpace f) moduleRealization (ξ := Core.mk L) (η := Core.mk N) x

lemma modIso_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk N) Z) :
    (modIso f (PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk N) q x)).hom =
      tr ((relativeSpace f).map q.left) ((relativeSpace f).map_comp q.left x.1).symm
        (by rw [← Functor.map_comp, Over.w q]) (modIso f x).hom :=
  modIsoR_restrict (relativeSpace f) moduleRealization (ξ := Core.mk L) (η := Core.mk N) q x

end Relative

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
