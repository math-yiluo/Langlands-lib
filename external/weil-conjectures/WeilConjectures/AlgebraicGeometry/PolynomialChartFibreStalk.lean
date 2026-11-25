/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-! # The canonical fibre stalk map of a polynomial chart

Source: Stacks Project, Tag 00RH, polynomial chart and localization of its closed fibre.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.PolynomialChart

noncomputable section

variable {X T : Scheme.{u}} (f : X ⟶ T) (U : X.Opens)

/-- The inclusion of the fibre of an open subscheme into the original fibre.
Source: the scheme-fibre pullback construction in Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
def fibreInclusion (p : T) : (U.ι ≫ f).fiber p ⟶ f.fiber p :=
  (pullbackRightPullbackFstIso f (T.fromSpecResidueField p) U.ι).inv ≫
    pullback.snd U.ι (f.fiberι p)

instance (p : T) : IsOpenImmersion (fibreInclusion f U p) := by
  dsimp [fibreInclusion, Scheme.Hom.fiberι]
  infer_instance

/-- The fibre inclusion commutes with the maps into the original schemes.
Source: the defining pullback square, Stacks Project, the scheme-fibre construction in Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
lemma fibreInclusion_fiberι (p : T) :
    fibreInclusion f U p ≫ f.fiberι p = (U.ι ≫ f).fiberι p ≫ U.ι := by
  simp [fibreInclusion, Scheme.Hom.fiberι]

/-- The point of the open fibre over `f (U.ι x)`.
Source: the fibre homeomorphism, Stacks Project, the scheme-fibre construction in Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
def fibrePoint (x : U.toScheme) : (U.ι ≫ f).fiber (f (U.ι x)) :=
  ((U.ι ≫ f).fiberHomeo (f (U.ι x))).symm ⟨x, Scheme.Hom.comp_apply U.ι f x⟩

/-- The point of the open fibre maps to the original fibre point.
Source: the scheme-fibre inclusion in Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
lemma fibreInclusion_asFiber (x : U.toScheme) :
    fibreInclusion f U (f (U.ι x)) (fibrePoint f U x) = f.asFiber (U.ι x) := by
  apply (f.fiberι _).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, fibreInclusion_fiberι, Scheme.Hom.comp_apply,
    Scheme.Hom.fiberι_asFiber]
  exact congrArg U.ι ((U.ι ≫ f).fiberι_fiberHomeo_symm _ _)

variable (n : ℕ) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
  (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)

/-- Base change of the chart to the residue field of a point of the base.
Source: the polynomial chart in the proof of Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
def fibreMap (p : T) :
    (U.ι ≫ f).fiber p ⟶ (AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiber p :=
  (pullback.congrHom he.symm rfl).hom ≫
    (pullbackRightPullbackFstIso (AffineSpace (ULift.{u} (Fin n)) T ↘ T)
      (T.fromSpecResidueField p) e).inv ≫
    pullback.snd e ((AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiberι p)

instance [LocallyQuasiFinite e] (p : T) : LocallyQuasiFinite (fibreMap f U n e he p) := by
  dsimp [fibreMap, Scheme.Hom.fiberι]
  infer_instance

instance [LocallyOfFinitePresentation e] (p : T) :
    LocallyOfFinitePresentation (fibreMap f U n e he p) := by
  dsimp [fibreMap, Scheme.Hom.fiberι]
  infer_instance

/-- The source of the canonical chart stalk map: the polynomial fibre stalk.
Source: Stacks Project, Tag 00RH, the localization of the polynomial closed fibre.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
def sourceStalk (x : U.toScheme) : CommRingCat.{u} :=
  ((AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiber (f (U.ι x))).presheaf.stalk
    (fibreMap f U n e he (f (U.ι x)) (fibrePoint f U x))

/-- The canonical map from the polynomial fibre stalk to the actual fibre stalk.
The chart gives the stalk map into the open fibre stalk. The inverse of the open
immersion's stalk isomorphism identifies this stalk with the actual fibre stalk.
Source: Stacks Project, Tag 00RH, and its stalk localization comparison.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
def stalkMap (x : U.toScheme) : sourceStalk f U n e he x →+*
    (f.fiber (f (U.ι x))).presheaf.stalk (f.asFiber (U.ι x)) :=
  (eqToHom (congrArg (f.fiber (f (U.ι x))).presheaf.stalk
    (fibreInclusion_asFiber f U x))).hom.comp
    ((inv ((fibreInclusion f U (f (U.ι x))).stalkMap (fibrePoint f U x))).hom.comp
      ((fibreMap f U n e he (f (U.ι x))).stalkMap (fibrePoint f U x)).hom)

/-- The canonical fibre stalk map is local.
Source: locality of scheme stalk maps and of isomorphisms, Stacks Project, Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
instance (x : U.toScheme) : IsLocalHom (stalkMap f U n e he x) := by
  have hcast : IsLocalHom (eqToHom
      (congrArg (f.fiber (f (U.ι x))).presheaf.stalk
        (fibreInclusion_asFiber f U x))).hom := isLocalHom_of_isIso _
  have hinv : IsLocalHom
      (inv ((fibreInclusion f U (f (U.ι x))).stalkMap (fibrePoint f U x))).hom :=
    isLocalHom_of_isIso _
  have hmap : IsLocalHom
      ((fibreMap f U n e he (f (U.ι x))).stalkMap (fibrePoint f U x)).hom :=
    inferInstance
  exact ⟨fun a ha ↦ hmap.map_nonunit a
    (hinv.map_nonunit _ (hcast.map_nonunit _ ha))⟩

/-- Quasi-finiteness survives the canonical fibre and stalk comparisons.
Source: base change and localization of quasi-finite maps, Stacks Project, Tag 00RE.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
theorem quasiFinite_stalkMap [LocallyQuasiFinite e] (x : U.toScheme) :
    (stalkMap f U n e he x).QuasiFinite := by
  have hcast := RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective
    (eqToHom (congrArg (f.fiber (f (U.ι x))).presheaf.stalk
      (fibreInclusion_asFiber f U x))).hom
    (ConcreteCategory.bijective_of_isIso _).2)
  have hinv := RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective
    (inv ((fibreInclusion f U (f (U.ι x))).stalkMap (fibrePoint f U x))).hom
    (ConcreteCategory.bijective_of_isIso _).2)
  have hmap := (fibreMap f U n e he (f (U.ι x))).quasiFiniteAt (fibrePoint f U x)
  exact hcast.comp (hinv.comp hmap)

/-- The polynomial fibre stalk is regular local.
Source: polynomial regularity and localization, Stacks Project, Tag 00RE.
Proof: affine-space base change identifies the fibre with the spectrum of the
polynomial ring over the residue field. The stalk is its localization at a prime;
polynomial regularity and its defining localization property give regularity.
(blueprint: lem-sbc-polynomial-chart-canonical-fibre-stalk) -/
theorem isRegularLocalRing_sourceStalk (x : U.toScheme) :
    IsRegularLocalRing (sourceStalk f U n e he x) := by
  let p := f (U.ι x)
  let k := T.residueField p
  let P := CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) k)
  let i : (AffineSpace (ULift.{u} (Fin n)) T ↘ T).fiber p ≅ Spec P :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin n))
      (T.fromSpecResidueField p)).isoPullback.symm ≪≫
      AffineSpace.SpecIso (ULift.{u} (Fin n)) (T.residueField p)
  let y := fibreMap f U n e he p (fibrePoint f U x)
  let j := (Spec.stalkIso P (i.hom y)).symm ≪≫ asIso (i.hom.stalkMap y)
  exact IsRegularLocalRing.of_ringEquiv j.commRingCatIsoToRingEquiv

end
end AlgebraicGeometry.PolynomialChart
