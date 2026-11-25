/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Finite limits on the affine étale and affine pro-étale sites of an affine scheme

Let `S` be an affine scheme. The small affine étale site `S.AffineEtale` and the affine
pro-étale site `S.AffineProEt` have pullbacks; in this file we show that they also have a
terminal object, namely `Spec Γ(S, ⊤) ≅ S` (resp. `S` itself), hence have finite limits, and
that the functors `AffineEtale.Spec S : S.AffineEtale ⥤ S.Etale` and
`AffineEtale.toAffineProEt S : S.AffineEtale ⥤ S.AffineProEt` preserve finite limits.

Consequently, for every object `V` of these sites, `Over V` has finite products (by the global
instance `CategoryTheory.Over.hasFiniteLimits`) and the functors `Over.post` induced by the two
functors above preserve finite products (by `PreservesFiniteLimits.overPost`). These are the
hypotheses of `CategoryTheory.Presheaf.exactAt_cechComplex_comp_iff`.

## Main definitions

- `AlgebraicGeometry.Scheme.AffineEtale.top`: the terminal object `Spec Γ(S, ⊤) ⟶ S` of the
  small affine étale site of an affine scheme `S`.
- `AlgebraicGeometry.Scheme.AffineProEt.top`: the terminal object `𝟙 S` of the affine
  pro-étale site of an affine scheme `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) [IsAffine S]

namespace AffineEtale

/-- The terminal object of the small affine étale site of an affine scheme `S`: the scheme
`Spec Γ(S, ⊤)` with structure morphism the inverse of `S.isoSpec`. -/
noncomputable def top : S.AffineEtale :=
  AffineEtale.mk S.isoSpec.inv

/-- The image of `AffineEtale.top S` in the small étale site is isomorphic to `S` itself. -/
noncomputable def specObjTopIso :
    (AffineEtale.Spec S).obj (top S) ≅ Scheme.Etale.mk (𝟙 S) :=
  MorphismProperty.Over.isoMk S.isoSpec.symm (Category.comp_id _)

/-- The image of `AffineEtale.top S` in the small étale site is a terminal object. -/
noncomputable def isTerminalSpecObjTop : IsTerminal ((AffineEtale.Spec S).obj (top S)) :=
  (MorphismProperty.Over.mkIdTerminal @Etale S).ofIso (specObjTopIso S).symm

/-- `AffineEtale.top S` is a terminal object of the small affine étale site. -/
noncomputable def isTerminalTop : IsTerminal (top S) :=
  IsTerminal.isTerminalOfObj (AffineEtale.Spec S) _ (isTerminalSpecObjTop S)

instance : HasTerminal S.AffineEtale :=
  (isTerminalTop S).hasTerminal

instance : HasFiniteLimits S.AffineEtale :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : PreservesFiniteLimits (AffineEtale.Spec S) :=
  have := preservesLimit_empty_of_isTerminal _ (isTerminalTop S) (isTerminalSpecObjTop S)
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (AffineEtale.Spec S)
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end AffineEtale

namespace AffineProEt

/-- The terminal object of the affine pro-étale site of an affine scheme `S`: the identity
of `S`. -/
noncomputable def top : S.AffineProEt :=
  AffineProEt.ofEtale (𝟙 S)

/-- `AffineProEt.top S` is a terminal object of the affine pro-étale site. -/
noncomputable def isTerminalTop : IsTerminal (top S) :=
  IsTerminal.ofUniqueHom (fun X ↦ MorphismProperty.Over.homMk X.hom (Category.comp_id _))
    fun X f ↦ MorphismProperty.Over.Hom.ext <|
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)

instance : HasTerminal S.AffineProEt :=
  (isTerminalTop S).hasTerminal

instance : HasFiniteLimits S.AffineProEt :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The image of `AffineEtale.top S` in the affine pro-étale site is isomorphic to
`AffineProEt.top S`. -/
noncomputable def toAffineProEtObjTopIso :
    (AffineEtale.toAffineProEt S).obj (AffineEtale.top S) ≅ top S :=
  MorphismProperty.Over.isoMk S.isoSpec.symm (Category.comp_id _)

/-- The image of `AffineEtale.top S` in the affine pro-étale site is a terminal object. -/
noncomputable def isTerminalToAffineProEtObjTop :
    IsTerminal ((AffineEtale.toAffineProEt S).obj (AffineEtale.top S)) :=
  (isTerminalTop S).ofIso (toAffineProEtObjTopIso S).symm

instance : PreservesFiniteLimits (AffineEtale.toAffineProEt S) :=
  have := preservesLimit_empty_of_isTerminal _ (AffineEtale.isTerminalTop S)
    (isTerminalToAffineProEtObjTop S)
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (AffineEtale.toAffineProEt S)
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end AffineProEt

end AlgebraicGeometry.Scheme
