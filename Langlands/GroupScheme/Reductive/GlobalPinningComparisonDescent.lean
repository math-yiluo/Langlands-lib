import Langlands.GroupScheme.Reductive.GlobalPinningFixedTransitions
import Langlands.GroupScheme.Reductive.AffinePinnedTransitions
import Langlands.GroupScheme.Descent.FppfCoverIsomorphism

/-! # Descent of canonical pinned comparisons to the original groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent

variable {S U T W : Scheme.{u}} {G H : GroupScheme S}

/-- Express an actual comparison between iterated chart pullbacks as an
isomorphism between the direct pullbacks of the original groups. -/
def comparisonInOriginal (a : U ⟶ S) (f : T ⟶ U) (k : T ⟶ S)
    (hf : f ≫ a = k)
    (e : (baseChange f).obj ((baseChange a).obj G) ≅
      (baseChange f).obj ((baseChange a).obj H)) :
    (baseChange k).obj G ≅ (baseChange k).obj H :=
  (pullbackComparison a f k hf G).symm ≪≫ e ≪≫
    pullbackComparison a f k hf H

/-- Normalizing a chart comparison commutes with every further pullback. -/
theorem comparisonInOriginal_pull (a : U ⟶ S) (f : T ⟶ U) (k : T ⟶ S)
    (hf : f ≫ a = k)
    (e : (baseChange f).obj ((baseChange a).obj G) ≅
      (baseChange f).obj ((baseChange a).obj H))
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    pullIso q hl hl (comparisonInOriginal a f k hf e) =
      comparisonInOriginal a (q ≫ f) l
        ((Category.assoc _ _ _).trans ((congrArg (fun b => q ≫ b) hf).trans hl))
        (pullIso q rfl rfl e) := by
  have hcG := congrArg Iso.inv (pullbackComparison_comp a f k hf q l hl G)
  have hcH := congrArg Iso.hom (pullbackComparison_comp a f k hf q l hl H)
  dsimp only [Iso.trans_inv, Functor.mapIso_inv] at hcG
  dsimp only [Iso.trans_hom, Functor.mapIso_hom] at hcH
  apply Iso.ext
  simp only [comparisonInOriginal, pullIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (pullbackComparison k q l hl G).inv,
    hcG, Category.assoc, hcH]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.CoordinateRootDatum

variable {S : Scheme.{u}} {I J I' J' : Type u}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (hH : IsReductive H) (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (hQ : IsGlobalCoordinateRootDatumOf I' H t' Q)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (F' : AffineRootFrames t' Q) (hF' : AffineRootFrames.IsCoherent t' Q F')
    (b : P.Base) (c : Q.Base)
    (θ : RootPairing.Equiv Q P)
    (hθ : ∀ s : J', s ∈ c.support ↔ θ.indexEquiv s ∈ b.support)
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})

section OneChart

variable (R : Type u) [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)

local notation "M" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R a
local notation "N" => pinnedAffineModelOfFrames t' Q hH ht' hmax' hQ F' c R a

/-- The canonical fixed pinned comparison on one chart, expressed in the
actual original groups over any scheme mapping to that chart. -/
def affineFrameIsoOver {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of R))
    (k : T ⟶ S) (hf : f ≫ a = k) :
    (baseChange k).obj G ≅ (baseChange k).obj H :=
  Descent.comparisonInOriginal a f k hf
    (@AffinePinnedModel.fixedComparison M N θ hθ T hAffine f f).val

/-- The original-group comparison commutes with arbitrary further pullback,
including explicitly specified equal base maps. -/
theorem affineFrameIsoOver_pull {T W : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (k : T ⟶ S) (hf : f ≫ a = k)
    (q : W ⟶ T) (l : W ⟶ S) (hl : q ≫ k = l) :
    Descent.pullIso q hl hl
        (affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
          F F' b c θ hθ hAffine R a f k hf) =
      affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine R a (q ≫ f) l
          ((Category.assoc _ _ _).trans ((congrArg (fun z => q ≫ z) hf).trans hl)) := by
  have he :
      Descent.pullIso q rfl rfl
          (@AffinePinnedModel.fixedComparison M N θ hθ T hAffine f f).val =
        (@AffinePinnedModel.fixedComparison M N θ hθ W hAffine (q ≫ f) (q ≫ f)).val := by
    simpa only [Descent.pullIso, Descent.pullbackComparison,
      AffinePinnedModel.pullComparison, eqToIso_refl, Iso.trans_refl, Iso.symm_symm_eq] using
      (@AffinePinnedModel.fixedComparison_pull M N θ hθ T W hAffine f f q)
  unfold affineFrameIsoOver
  rw [Descent.comparisonInOriginal_pull, he]

end OneChart

section TwoCharts

variable (R R' : Type u) [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)

include hF hF' in
/-- The normalized canonical comparison is independent of the chosen affine
chart on every common scheme over the original base. -/
theorem affineFrameIsoOver_independent {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Spec (CommRingCat.of R'))
    (k : T ⟶ S) (hf : f ≫ a = k) (hg : g ≫ a' = k) :
    affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine R a f k hf =
      affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine R' a' g k hg := by
  have hn := canonicalAffineFrameComparison_naturality t t' P Q
    hG ht hmax hP hH ht' hmax' hQ F hF F' hF' b c θ hθ
    R R' a a' hAffine f g k hf hg
  have hh := congrArg
    (fun z => (Descent.pullbackComparison a f k hf G).inv ≫
      z ≫ (Descent.pullbackComparison a' g k hg H).hom)
    (congrArg Iso.hom hn)
  apply Iso.ext
  simpa only [affineFrameIsoOver, Descent.comparisonInOriginal,
    affineFrameComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm

end TwoCharts

section Family

variable {C : Type u} (R : C → Type u) [∀ i, CommRing (R i)]
    (a : ∀ i, Spec (CommRingCat.of (R i)) ⟶ S)

/-- The actual original-group isomorphism on each member of an affine family. -/
def affineFrameIsoFamily (i : C) :
    (baseChange (a i)).obj G ≅ (baseChange (a i)).obj H :=
  affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F F' b c θ hθ hAffine (R i) (a i) (𝟙 _) (a i) (Category.id_comp _)

include hF hF' in
/-- Coherent frames make the actual chart isomorphisms compatible on all
common schemes, as required by covering-family descent. -/
theorem affineFrameIsoFamily_isCompatible :
    Descent.CoverIsomorphism.IsCompatible a
      (affineFrameIsoFamily t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine R a) := by
  intro T i j f g k hf hg
  unfold affineFrameIsoFamily
  rw [affineFrameIsoOver_pull, affineFrameIsoOver_pull]
  simpa only [Category.comp_id] using
    (affineFrameIsoOver_independent t t' P Q hG ht hmax hP hH ht' hmax' hQ
      F hF F' hF' b c θ hθ hAffine (R i) (R j) (a i) (a j) f g k hf hg)

variable [Flat (Descent.CoverIsomorphism.projection a)]
    [Surjective (Descent.CoverIsomorphism.projection a)]
    [LocallyOfFinitePresentation (Descent.CoverIsomorphism.projection a)]

/-- An actual global isomorphism from coherent original root frames, a fixed
based full root-datum map, the affine pinned theorem and an affine fppf family. -/
def globalIsoOfCoherentFrames : G ≅ H :=
  Descent.CoverIsomorphism.descend a
    (affineFrameIsoFamily t t' P Q hG ht hmax hP hH ht' hmax' hQ
      F F' b c θ hθ hAffine R a)
    (affineFrameIsoFamily_isCompatible t t' P Q hG ht hmax hP hH ht' hmax' hQ
      F hF F' hF' b c θ hθ hAffine R a)

/-- The descended global isomorphism recovers every canonical original-group
chart isomorphism exactly. -/
theorem globalIsoOfCoherentFrames_on_member (i : C) :
    (baseChange (a i)).mapIso
        (globalIsoOfCoherentFrames t t' P Q hG ht hmax hP hH ht' hmax' hQ
          F hF F' hF' b c θ hθ hAffine R a) =
      affineFrameIsoFamily t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine R a i :=
  Descent.CoverIsomorphism.descend_on_member _ _ _ i

end Family

end Langlands.GroupScheme.CoordinateRootDatum
