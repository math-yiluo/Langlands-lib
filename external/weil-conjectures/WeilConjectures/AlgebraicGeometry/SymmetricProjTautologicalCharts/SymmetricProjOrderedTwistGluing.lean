/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedTwistLine
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOrderedTwistCoordinates

/-!
# Gluing the ordered tautological twist comparison

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-twist-gluing).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison

/-- Once the ordered scheme and affine twist comparisons are supplied, normalization
of a tautological quotient identifies its line and coordinate quotients with the pullback
of the standard twist. No scheme isomorphism is constructed by this statement.

Source: Stacks Project, Constructions, Tags 01OE (lemma-projective-space-bundle),
01OB (definition-projective-bundle), and 01MS (lemma-when-invertible).
(blueprint: lem-trf-symmetric-proj-ordered-twist-gluing).

Proof: Fix an affine V and unpack AffineFreeComparison to get beta, eC, its
section-preserving twist isomorphism, and gamma and eR. The integral polynomial chart
normalization of theta says that the composite local map to the integral Proj is the
coefficient-extension map fixing every ordered variable. The chart equation for eRel
therefore identifies the restriction of eRel followed by theta with this same standard
polynomial chart. Pulling back the standard twist gives the local polynomial degree-one
twist: on D_+(X_i) its generator is X_i, and extension of coefficients preserves both
this frame and every ratio X_j/X_i. Compose this comparison with the beta twist
isomorphism and the inverse of D.chart V. It sends the pulled coordinate section X_i
to the quotient of b(e_i), by D.generator. On intersections these maps agree: each
sends a local free frame to the same normalized quotient frame. The local inverses
agree as well, so they glue to an isomorphism t. Refine intersections of affine base
opens by affine opens; no separatedness of S is needed. Equality of the displayed
morphisms from the unit module can be checked on these charts, where the generator
formula gives it. The tensor pullback composition and unit comparisons in the formula
are precisely the canonical identifications used to transport these sections. The
argument includes r=0 and empty charts because it only uses free frames on standard
opens, and those opens still form a cover. -/
theorem exists_ordered_twist_comparison (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (r : ℕ) (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (eRel : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r)
    (hRel : eRel.hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
    (hAffine : ∀ V : S.affineOpens,
      ProjectiveBundleQuotientGeometry.AffineFreeComparison r b eRel V)
    (θ : RelativeProjectiveSpace.scheme S r ≅ ℙ(ULift.{u} (Fin (r + 1)); S))
    (hθ : θ.hom ≫ (ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S) =
      RelativeProjectiveSpace.π S r)
    (hθAffine : ∀ V : S.affineOpens, RelativeProjectiveSpace.IsIntegralProjComparison
      S r V (RelativeProjectiveSpace.affineToIntegral S r θ V)) :
    ∃ t : (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) S 1) ≅ D.line,
      ∀ i : ULift.{u} (Fin (r + 1)),
        (Scheme.Modules.tensorPullback
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).map
          (SheafOfModules.ιFree (R := S.ringCatSheaf) i ≫ b.hom) ≫ D.quotient =
        ((Scheme.Modules.boundaryPullbackComparison
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).app
              (Scheme.Modules.unit S) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom ≫
        ((Scheme.Modules.boundaryPullbackComparison (eRel ≪≫ θ).hom).app
            (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso (eRel ≪≫ θ).hom).inv ≫
        (Scheme.Modules.tensorPullback (eRel ≪≫ θ).hom).map
          (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (r + 1))) S i) ≫ t.hom := by
  obtain ⟨t, ht⟩ := exists_ordered_twist_line S E D r b eRel hRel hAffine θ hθ hθAffine
  exact ⟨t, ordered_twist_coordinate_compatibility S E D r b eRel θ t ht⟩

end AlgebraicGeometry.SymmetricProjTautologicalCharts
