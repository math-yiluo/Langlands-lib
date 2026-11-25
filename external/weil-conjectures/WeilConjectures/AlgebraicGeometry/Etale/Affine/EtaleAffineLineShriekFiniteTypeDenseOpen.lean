/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLineLisseFiniteComplement
import WeilConjectures.AlgebraicGeometry.Lisse.LisseOpenRelativeLineConstructibility
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.Compactification.CompactificationCategory
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! Dense-open constructibility over a finite-type integer affine base. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Constructibility when the non-lisse part is finite over the base. -/
private theorem affineLine_shriek_constructible_of_finite_complement
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (hΛ : ∀ (a : Λ) (s : Spec (.of R)), IsUnit (addOrderOf a : (Spec (.of R)).presheaf.stalk s))
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (hU : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F))
    {Z : Scheme.{u}} (i : Z ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)))
    [IsClosedImmersion i] (hij : Set.range i.base = (Set.range U.ι.base)ᶜ)
    (hZ : IsFinite (i ≫
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (c : Compactification
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let Y := Spec (.of R)
  let X := AffineSpace (ULift.{u} (Fin 1)) Y
  let f : X ⟶ Y := X ↘ Y
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : TopologicalSpace.NoetherianSpace X := inferInstance
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set X))
  let cU := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u} (U.ι ≫ f)).1
  let cZ := Classical.choice
    (Compactification.compactificationCategory_properties.{u, u} (i ≫ f)).1
  have : QuasiCompact cZ.i := cZ.quasiCompact_openImmersion inferInstance
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  obtain ⟨T, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT, _⟩ :=
    Etale.exists_compactSupport_openClosed_triangle Λ f U.ι i hij K c cU cZ
  let P := _root_.DerivedCategory.homologyProperty
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y)
  have h₁ : P T.obj₁ := by
    intro n
    have hn := Etale.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
      Λ R hΛ U ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F)
      ((Scheme.finite_locally_constant_module_values_iff _).1.mpr hU) cU n
    have hn' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hn
    let e := (Functor.mapDerivedCategoryPlusSingleFunctor
      (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι) 0).app F
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e₁ ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ n).mapIso
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} Λ) cU).mapIso e)).symm hn'
  have hqf : (i ≫ f).IsQuasiFinite :=
    ⟨inferInstance, inferInstance, fun x ↦
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp ((i ≫ f).quasiFiniteAt x)⟩
  have hK : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor _ n).obj
        (((Etale.upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus).obj K)) := by
    intro n
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
    have hc := Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0
    have hc' := Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar i hc
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc'.2 n)
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  have hz := Etale.constructibleCohomology_lowerShriek_of_quasiFinite Λ (i ≫ f)
    hqf _ hK cZ
  have h₃ : P T.obj₃ := by
    intro n
    have hn := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hz n)
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e₃).symm hn
  have h₂ := P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Y).prop_of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e₂) (h₂ q)

/-- The dense-open step in affine-line compact-support constructibility, over a base on
which the additive orders of the coefficients are invertible.
Source: Stacks Project, Tag 0GKZ, induction paragraph, and Tags 0GKY, 0GK3, 0GKP.
(blueprint: lem-weil-pbc-affine-line-shriek-finite-type-dense-open)

Proof: The geometric shrinking and generic-constancy theorem supplies a dense open
affine spectrum over which the input is lisse on an open with finite closed complement.
Choose compactifications of both pieces. The lisse-open-relative-line theorem proves
constructibility for the open piece. The finite complement is quasi-finite and finitely
presented over the Noetherian base, so quasi-finite shriek constructibility applies to
the pullback of the input placed in degree zero. The relative open-closed triangle has
these two outputs as outer vertices. Exact inverse image commutes with the single
functor, and constructible homology is a triangulated property (the Serre five-term
exact-sequence argument), so the middle output has constructible homology. Compact-support
base change, exactness of inverse image, and compactification independence identify this
output with the pullback of the original output. Identify the open affine spectrum with
its open range to obtain the required dense open of the original base. Empty schemes
and the zero input require no separate nonemptiness assumption.
-/
theorem exists_dense_open_affineLine_shriek_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Y : Scheme.{u}) [IsAffine Y]
    [Algebra.FiniteType ℤ Γ(Y, ⊤)]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (F : Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) (hF : Scheme.IsConstructibleEtaleModuleSheaf F)
    (c : Compactification (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)) (q : ℤ) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      Scheme.IsConstructibleEtaleModuleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf (AffineSpace (ULift.{u} (Fin 1)) Y).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F)))) := by
  classical
  obtain ⟨R, hR, hft, g, hg, hgd, U, hU, Z, i, hi, hij, hZ⟩ :=
    exists_dense_affine_open_lisse_finite_complement Λ Y F hF
  let c' := c.ofIsPullback (AffineSpace.isPullback_map g)
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ)
    (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
  have := Scheme.IsConstructibleSheaf.upperStar
    (AffineSpace.map (ULift.{u} (Fin 1)) g) F
  have hF' : Scheme.IsConstructibleEtaleModuleSheaf F' :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr inferInstance
  have hij' : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact hij
  have hc := affineLine_shriek_constructible_of_finite_complement
    Λ R (fun a s ↦ by simpa using (hΛ a (g s)).map (g.stalkMap s).hom) F' hF' U hU i hij' hZ
    c' q
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := _root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  let e := ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    H.mapIso ((asIso
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ
        (AffineSpace.isPullback_map g) c)).app K) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
      (c.ofIsPullback (AffineSpace.isPullback_map g))).mapIso
        (((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (AffineSpace.map (ULift.{u} (Fin 1)) g)).mapDerivedCategoryPlusSingleFunctor
          0).app F)) ≪≫
    H.mapIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso Λ
      (c.ofIsPullback (AffineSpace.isPullback_map g)) c').app _)
  have hsrc : Scheme.IsConstructibleSheaf
      (H.obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c').obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ)
              (AffineSpace.map (ULift.{u} (Fin 1)) g)).obj F)))) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
  let G := (_root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hc' : Scheme.IsConstructibleSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G) :=
    @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _ e.symm hsrc
  let V := g.opensRange
  have heq : Set.range g.base = Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; rfl
  let eV := IsOpenImmersion.isoOfRangeEq g V.ι heq
  refine ⟨V, hgd, ?_⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have hcPull := Scheme.IsConstructibleSheaf.upperStar eV.inv
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G)
  have hc'' := (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) V.toScheme).prop_of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) eV.inv g).app G).symm hcPull
  have heV : eV.inv ≫ g = V.ι := IsOpenImmersion.isoOfRangeEq_inv_fac g V.ι heq
  rw [heV] at hc''
  exact hc''

end AlgebraicGeometry
