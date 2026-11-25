/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure


public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Local sections of an integral geometric fibre

Source: Stacks Project, Tag 0EYP, using Tags 03Q9, 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- A neighbourhood section whose restriction to an integral geometric fibre is
zero becomes zero on a pointed etale refinement of that neighbourhood.

Source: Stacks Project, Tag 0EYP, degree zero, via Tags 03Q9, 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-fibre-section-local-zero).

Proof: write the integral pullback over the strict henselization Spec A as Spec B.
The section z restricts to a section z_sh there, by the inverse-image unit. With
m the maximal ideal of A, Tag 09XK makes (B,mB) henselian. The degree-zero
henselian comparison applied to the proper identity of Spec B is injective on
sections after restriction to Spec(B/mB). The residue field k of A is separably
closed; Tag 0A3I makes further restriction along k to Omega injective as well.
Composition of inverse-image units identifies the latter restriction of z_sh
with geometricFibreSectionRestriction applied to z, which is zero by hypothesis.
Therefore z_sh is zero. Tag 03Q9 identifies this equality with equality of the
germ of z and the zero germ. The filtered-colimit equality criterion gives a
pointed etale neighbourhood W mapping to the original V on which z is zero.
One can first refine V by an affine neighbourhood of its marked point; cofinality
of affine pointed neighbourhoods and the strict-henselization representative
functor ensures that the resulting W still maps to V with marked point v.
For module coefficients, forgetting to sets preserves the inverse images and
these canonical maps, and takes the module zero section to its zero section.
For an empty fibre, integrality makes the image closed, and a neighbourhood of
s disjoint from that image yields the same conclusion. -/
theorem integralFibreSection_localZero
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
    (z : F.obj.obj (op (f.Etale.obj V)))
    (hz : (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z = 0) :
    ∃ (W : Y.Etale) (w : (pointSmallEtale s).fiber.obj W) (a : W ⟶ V),
      (pointSmallEtale s).fiber.map a w = v ∧
        (F.obj.map (f.Etale.map a).op).hom z = 0 := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨hlocal, hstrict⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization s)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization s) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  let := hlocal
  let := hstrict
  obtain ⟨t, ht, hclosed, i, hsq, hi, Θ, b, hformula⟩ :=
    strictHenselizationModuleFibre_factorization Λ sq F
  have hintegral : IsIntegralHom (Limits.pullback.snd f
      (strictLocalizationToBase s)) := inferInstance
  let := hintegral
  have hinj := strictHenselianIntegralSections_injective Λ (strictHenselization s)
    (Limits.pullback.snd f (strictLocalizationToBase s)) t hclosed i f' hsq
    ((Limits.pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)
  let germ := (pointSmallEtale s).toPresheafFiber V v
    ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj
  have hzero : germ.hom z = 0 := by
    apply (ConcreteCategory.bijective_of_isIso Θ.hom).1
    apply hinj
    apply (ConcreteCategory.bijective_of_isIso b.hom).1
    simpa only [map_zero] using (hformula V v z).trans hz
  have heq : germ z = germ 0 := by simpa only [map_zero] using hzero
  obtain ⟨W, a, w, hw, ha⟩ :=
    ((pointSmallEtale s).toPresheafFiber_eq_iff'
      (P := ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj) V v z 0).mp heq
  refine ⟨W, w, a, hw, ?_⟩
  change (F.obj.map (f.Etale.map a).op).hom z =
    (F.obj.map (f.Etale.map a).op).hom 0 at ha
  simpa only [map_zero] using ha

end AlgebraicGeometry.Etale
