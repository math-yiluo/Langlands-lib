/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux

/-! # Local sections of an integral geometric fibre

Source: Stacks Project, Tag 0EYP, using Tags 03Q9, 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Every section on the geometric fibre of an integral morphism is the restriction
of a section over some pointed etale neighbourhood of the geometric point.

Source: Stacks Project, Tag 0EYP, degree zero, via Tags 03Q9, 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-fibre-section-local-lift).

Proof: pass to an affine neighbourhood of the image of s and let A be its strict
henselization at s. The pullback of the integral morphism is affine Spec B, with B
integral over A. If m is the maximal ideal of A, (B,mB) is henselian by Tag 09XK.
Apply the degree-zero henselian comparison (Tag 09ZH, or the proper comparison for
the identity of Spec B) to lift sections from Spec(B/mB) to Spec B. The residue
field k of A is separably closed and maps into Omega. Tag 0A3I identifies sections
on Spec(B/mB) with sections on its base change to Omega, the prescribed fibre X'.
Thus the given section t has a lift to Spec B. The strict-henselization section
continuity formula in Tag 03Q9 represents that lift on an affine pointed etale
neighbourhood (V,v). Compatibility of inverse-image composition with units shows
that its restriction to X' is the unit for g' restricted along the lift whose
projections are (f' followed by v,g') and the identity. These are exactly the
projections defining geometricFibreSectionRestriction. Forgetting the module
structure commutes with these inverse images and section maps, so the argument
for sets applies to F. No algebraicity of Omega over k is required. If the fibre
is empty its section module is zero, and the zero section over the identity
neighbourhood provides the required lift. -/
theorem integralFibreSection_localLift
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X')))) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (z : F.obj.obj (op (f.Etale.obj V))),
      (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z = t := by
  classical
  obtain ⟨e, he⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  obtain ⟨b, hb⟩ := exists_integralStrictLocalFibreComparison Λ sq F
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : N.Initial := (strictHenselizationAffineProperties s).1
  let := (strictHenselizationAffineProperties s).2.1
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj
  let c := ((pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : CategoryTheory.Limits.IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((pointSmallEtale s).isColimitPresheafFiberCocone P)
  obtain ⟨j, z, hz⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (CategoryTheory.Limits.isColimitOfPreserves (forget (ModuleCat.{u + 1} Λ)) hc) (e.inv (b.inv t))
  refine ⟨((AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1),
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2,
    z, ?_⟩
  have h := congrArg (fun a ↦ b.hom (e.hom a)) hz
  have hformula := congrArg (fun a ↦ a z)
    ((congrArg (fun a ↦ a ≫ b.hom) (he j.unop)).trans (hb j.unop))
  have hh := hformula.symm.trans h
  simp only [Iso.inv_hom_id_apply] at hh
  convert hh using 1

end AlgebraicGeometry.Etale
