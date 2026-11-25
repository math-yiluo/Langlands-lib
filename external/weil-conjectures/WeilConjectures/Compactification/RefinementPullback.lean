/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!

# A refinement out of a dense compactification is cartesian over the source

Let `f : X ⟶ Y` be a morphism of schemes, let `c` and `d` be compactifications of `f` and
let `r : c.Refinement d` be a refinement, so that `c.i ≫ r.hom = d.i`. If the open
immersion `c.i` is scheme-theoretically dominant, i.e. `c` is a *dense* compactification,
then `r.hom ⁻¹ (X) = X`: the square

```
X   --c.i-->  c.Z
|              |
𝟙            r.hom
v              v
X   --d.i-->  d.Z
```

is cartesian. This is the hypothesis under which the base change isomorphism for `j_!`
along a refinement is stated, and this file is what supplies instances of it.

## Main results

- `AlgebraicGeometry.Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`:
  the square above is cartesian for a refinement out of a dense compactification;
- `AlgebraicGeometry.Compactification.Refinement.isPullback_denseRefinement`: the
  specialisation to the dense refinement `c.denseRefinement` of an arbitrary
  compactification `c`, whose open immersion is scheme-theoretically dominant;
- `AlgebraicGeometry.Compactification.Refinement.isPullback_comp`: cartesianness of these
  squares pastes along a composite of refinements.

The proof compares `X` with the pullback `P := c.Z ×[d.Z] X` of `r.hom` along `d.i`. The
canonical morphism `t : X ⟶ P` is a section of the projection `P ⟶ X`, which is proper,
being a base change of the proper morphism `r.hom`; a section of a separated morphism is a
closed immersion, so `t` is a closed immersion. On the other hand `t` composed with the
projection `P ⟶ c.Z` is `c.i`, which is scheme-theoretically dominant, and `P ⟶ c.Z` is a
flat monomorphism, being a base change of the open immersion `d.i`; so `t` is
scheme-theoretically dominant as well. A closed immersion with trivial kernel is an
isomorphism, and that is exactly the assertion that the square is cartesian.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification.Refinement

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}

/-- **A refinement out of a dense compactification is cartesian over the source**: if the
open immersion `c.i` of the compactification `c` is scheme-theoretically dominant and
quasi-compact, then the inverse image of `X` under the ambient morphism of a refinement
`r : c.Refinement d` is again `X`. (blueprint: `BA43-DENSE-DATA`)

This is phrased with the density and quasi-compactness of `c.i` as instance binders, as in
`AlgebraicGeometry.Compactification.Refinement.instSubsingleton`: neither is findable by
typeclass search from `c` alone, but with them in scope the hypothesis of the base change
isomorphism for `j_!` along `r` is discharged automatically. Quasi-compactness of `c.i` is
equivalent to quasi-compactness of `f`
(`AlgebraicGeometry.Compactification.quasiCompact_openImmersion_iff`), which the blueprint
assumes throughout this chapter, `f` being finitely presented there. -/
theorem isPullback_of_isSchemeTheoreticallyDominant (r : c.Refinement d)
    [IsSchemeTheoreticallyDominant c.i] [QuasiCompact c.i] :
    IsPullback c.i (𝟙 X) r.hom d.i := by
  have hcomm : c.i ≫ r.hom = 𝟙 X ≫ d.i := by rw [Category.id_comp, r.i_hom]
  -- the canonical morphism from `X` to the pullback `c.Z ×[d.Z] X`
  set t : X ⟶ pullback r.hom d.i := pullback.lift c.i (𝟙 X) hcomm
  have hfst : t ≫ pullback.fst r.hom d.i = c.i := pullback.lift_fst _ _ _
  have hsnd : t ≫ pullback.snd r.hom d.i = 𝟙 X := pullback.lift_snd _ _ _
  -- `t` is a section of the proper, hence separated, projection to `X`
  have : IsClosedImmersion t := by
    have : IsClosedImmersion (t ≫ pullback.snd r.hom d.i) := by rw [hsnd]; infer_instance
    exact IsClosedImmersion.of_comp t (pullback.snd r.hom d.i)
  -- `t` is scheme-theoretically dominant, since `t ≫ pullback.fst r.hom d.i = c.i` is and
  -- the projection to `c.Z` is a flat monomorphism
  have : IsSchemeTheoreticallyDominant t := by
    have : QuasiCompact (t ≫ pullback.fst r.hom d.i) := by rw [hfst]; infer_instance
    have : IsSchemeTheoreticallyDominant (t ≫ pullback.fst r.hom d.i) := by
      rw [hfst]; infer_instance
    exact .of_comp t (pullback.fst r.hom d.i)
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso t) hfst hsnd

/-- The dense refinement of a compactification of a quasi-compact morphism satisfies both
instance hypotheses of
`AlgebraicGeometry.Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`
with no argument: its open immersion is the factor map through the scheme-theoretic image,
hence scheme-theoretically dominant, and it is quasi-compact because `f` is. -/
theorem isPullback_denseRefinement (c : Compactification f) [QuasiCompact f]
    (r : c.denseRefinement.Refinement d) :
    IsPullback c.denseRefinement.i (𝟙 X) r.hom d.i := by
  have hqc : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  have : IsSchemeTheoreticallyDominant c.denseRefinement.i :=
    c.isSchemeTheoreticallyDominant_denseRefinement_i
  have : QuasiCompact (c.i.toImage ≫ c.i.imageι) := by
    rw [Scheme.Hom.toImage_imageι]; exact hqc
  have : QuasiCompact c.denseRefinement.i := QuasiCompact.of_comp c.i.toImage c.i.imageι
  exact r.isPullback_of_isSchemeTheoreticallyDominant

/-- **Cartesianness pastes along a composite of refinements**: if the squares over `X` of
`r : c.Refinement d` and `s : d.Refinement e` are cartesian, then so is the square of the
composite refinement `r.comp s`. -/
theorem isPullback_comp {e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    IsPullback c.i (𝟙 X) (r.comp s).hom e.i := by
  simpa using hr.paste_vert hs

end AlgebraicGeometry.Compactification.Refinement
