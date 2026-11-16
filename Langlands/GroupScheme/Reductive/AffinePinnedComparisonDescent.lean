import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.FppfLocalGroupIso

/-! # Fppf descent of actual comparisons of affine pinned models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A pulled-back global isomorphism acts by the original morphism on every
relative test, independently of the chosen cover point. -/
@[simp] theorem ofBaseChangeIso_mapIso_toFun (e : G ≅ H)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (ofBaseChangeIso ((baseChange U.hom).mapIso e)).toFun a g =
      g ≫ e.hom.hom.hom := by
  change coverPointsEquiv H a
      ((coverPointsEquiv G a).symm g ≫ ((baseChange U.hom).map e.hom).hom.hom) = _
  rw [coverPointsEquiv_comp, MulEquiv.apply_symm_apply]

/-- The local family coming from a global isomorphism agrees at all cover points. -/
theorem ofBaseChangeIso_mapIso_isIndependent (e : G ≅ H) :
    (ofBaseChangeIso ((baseChange U.hom).mapIso e)).IsIndependent := by
  intro T a b g
  change (ofBaseChangeIso ((baseChange U.hom).mapIso e)).toFun a g =
    (ofBaseChangeIso ((baseChange U.hom).mapIso e)).toFun b g
  simp only [ofBaseChangeIso_mapIso_toFun]

variable [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]

/-- Pullback along a single fppf cover detects equality of actual isomorphisms. -/
theorem mapIso_injective_of_fppf :
    Function.Injective (fun e : G ≅ H => (baseChange U.hom).mapIso e) := by
  intro e d h
  apply Iso.ext
  apply hom_ext_points
  intro T g
  apply Over.OverMorphism.ext
  have : Epi (fst T U).left := by
    change Epi (CategoryTheory.Limits.pullback.fst T.hom U.hom)
    infer_instance
  apply (cancel_epi (fst T U).left).mp
  have he := congrArg
    (fun k : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H =>
      (ofBaseChangeIso k).toFun (snd T U) (fst T U ≫ g)) h
  simp only [ofBaseChangeIso_mapIso_toFun] at he
  exact congrArg (fun k => k.left) he

variable (e : LocalGroupIso G H U) (he : e.IsIndependent)

/-- Descent recovers every local value of an independent family. -/
@[simp] theorem ofBaseChangeIso_descendFppf :
    ofBaseChangeIso ((baseChange U.hom).mapIso (e.descendFppf he)) = e := by
  apply ext_toFun
  intro T a g
  rw [ofBaseChangeIso_mapIso_toFun]
  change g ≫ (e.toLocalGroupHom.descendFppf he).hom.hom = _
  rw [LocalGroupHom.comp_descendFppf]
  simpa only [Category.id_comp, toLocalGroupHom, MulEquiv.coe_toMonoidHom] using
    e.toLocalGroupHom.comp_valueFppf he (𝟙 T) a g

/-- The actual pullback of the descended isomorphism is the original
isomorphism recovered from the local family. -/
@[simp] theorem mapIso_descendFppf :
    (baseChange U.hom).mapIso (e.descendFppf he) = e.toBaseChangeIso := by
  have h := congrArg (fun k : LocalGroupIso G H U => k.toBaseChangeIso)
    (e.ofBaseChangeIso_descendFppf he)
  simpa only [toBaseChangeIso_ofBaseChangeIso] using h

include he in
/-- An independent family has a unique actual global isomorphism inducing it. -/
theorem existsUnique_descendFppf :
    ∃! d : G ≅ H, ofBaseChangeIso ((baseChange U.hom).mapIso d) = e := by
  refine ⟨e.descendFppf he, e.ofBaseChangeIso_descendFppf he, ?_⟩
  intro d hd
  apply mapIso_injective_of_fppf (U := U)
  have h := congrArg (fun k : LocalGroupIso G H U => k.toBaseChangeIso)
    (hd.trans (e.ofBaseChangeIso_descendFppf he).symm)
  simpa only [toBaseChangeIso_ofBaseChangeIso] using h

end Langlands.GroupScheme.LocalGroupIso

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base} (p : V ⟶ T)

/-- Express an actual comparison on the direct pullbacks as an isomorphism
between the iterated pullbacks along the cover. -/
def comparisonToIterated (d : Comparison (p ≫ f) (p ≫ g)) :
    (baseChange p).obj (M.groupOver f) ≅ (baseChange p).obj (N.groupOver g) :=
  (baseChangeCompIso f p M.group).symm ≪≫ d ≪≫ baseChangeCompIso g p N.group

/-- Passing a pulled-back comparison to iterated pullbacks recovers its
ordinary functorial pullback. -/
@[simp] theorem comparisonToIterated_pullComparison (e : Comparison f g) :
    comparisonToIterated p (pullComparison e p) = (baseChange p).mapIso e := by
  apply Iso.ext
  simp [comparisonToIterated, pullComparison]

/-- The local all-test family of a comparison on the cover, including the
actual direct/iterated pullback identifications. -/
def comparisonLocalIso (d : Comparison (p ≫ f) (p ≫ g)) :
    LocalGroupIso (M.groupOver f) (N.groupOver g) (Over.mk p) :=
  LocalGroupIso.ofBaseChangeIso (comparisonToIterated p d)

variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

local instance : Flat (Over.mk p).hom := by change Flat p; infer_instance
local instance : Surjective (Over.mk p).hom := by change Surjective p; infer_instance
local instance : LocallyOfFinitePresentation (Over.mk p).hom := by
  change LocallyOfFinitePresentation p
  infer_instance

/-- The target's normalized pullback operation detects equality on an
arbitrary fppf cover of the common test scheme. -/
theorem pullComparison_injective :
    Function.Injective (fun e : Comparison f g => pullComparison e p) := by
  intro e d h
  apply LocalGroupIso.mapIso_injective_of_fppf (U := Over.mk p)
  change (baseChange p).mapIso e = (baseChange p).mapIso d
  simpa only [comparisonToIterated_pullComparison] using
    congrArg (comparisonToIterated p) h

/-- Glue a comparison whose local all-test values are independent of the
point of the fppf cover. -/
def descendComparison (d : Comparison (p ≫ f) (p ≫ g))
    (hd : (comparisonLocalIso p d).IsIndependent) : Comparison f g :=
  (comparisonLocalIso p d).descendFppf hd

/-- Gluing recovers exactly the specified actual comparison on the cover. -/
@[simp] theorem pullComparison_descendComparison
    (d : Comparison (p ≫ f) (p ≫ g))
    (hd : (comparisonLocalIso p d).IsIndependent) :
    pullComparison (descendComparison p d hd) p = d := by
  have h := LocalGroupIso.mapIso_descendFppf (comparisonLocalIso p d) hd
  change (baseChange p).mapIso ((comparisonLocalIso p d).descendFppf hd) =
    (comparisonLocalIso p d).toBaseChangeIso at h
  unfold pullComparison descendComparison
  rw [h]
  simp only [comparisonLocalIso, LocalGroupIso.toBaseChangeIso_ofBaseChangeIso]
  apply Iso.ext
  simp [comparisonToIterated]

/-- Compatible actual comparisons have a unique global comparison, with
recovery stated using the target's normalized pullback operation. -/
theorem existsUnique_descendComparison
    (d : Comparison (p ≫ f) (p ≫ g))
    (hd : (comparisonLocalIso p d).IsIndependent) :
    ∃! e : Comparison f g, pullComparison e p = d := by
  refine ⟨descendComparison p d hd, pullComparison_descendComparison p d hd, ?_⟩
  intro e he
  apply pullComparison_injective p
  exact he.trans (pullComparison_descendComparison p d hd).symm

end Langlands.GroupScheme.AffinePinnedModel
