/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation
import all WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation

/-! # Global sections and stalk coordinates for an affine tilde presentation

Source: Stacks Project, Tags 01HV and 01I9.
(blueprint: new-lem-pc-affine-tilde-global-sections-stalk-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The localization of global sections of a tilde presentation agrees with its stalk map.
Source: Stacks Project, Tags 01HV and 01I9.
(blueprint: new-lem-pc-affine-tilde-global-sections-stalk-coordinates).
Proof: the tilde stalk localization is natural for module maps: check on numerators
using naturality of germs, then use the localization universal property. Apply it
to the global-sections map composed with the tilde/global-sections unit. Naturality
of the tilde/Gamma counit moves the presentation morphism past the counit, and the
left adjunction triangle cancels the unit and counit on tilde V. The argument does
not require the presentation morphism to be invertible. It also applies to zero
modules; the zero ring has no prime to check. -/
theorem affineTildeGlobalSectionsStalk_coordinates
    (A : Type u) [CommRing A] (i : ℤ) (p : PrimeSpectrum A)
    (L : schemeDerivedQCohCategory (Spec (.of A))) (V : ModuleCat.{u} A)
    (d : (tilde.functor (.of A)).obj V ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L.obj)
    (x : LocalizedModule p.asIdeal.primeCompl V) :
    affineDerivedCohomologyStalkIso A i p L
        (LocalizedModule.map p.asIdeal.primeCompl
          ((tilde.isoTop (R := .of A) V).hom ≫
            (moduleSpecΓFunctor (R := .of A)).map d).hom x) =
      (RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p).map d
        ((IsLocalizedModule.iso p.asIdeal.primeCompl
          (StructureSheaf.toStalkₗ A V p)) x) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  let W := H.obj L.obj
  let G := (moduleSpecΓFunctor (R := .of A)).obj W
  let b : V ⟶ G := (tilde.isoTop (R := .of A) V).hom ≫
    (moduleSpecΓFunctor (R := .of A)).map d
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A)).toRingedSpace p
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom
  let t : V →ₗ[A] Rs.obj (s.obj (tilde (R := .of A) V)) :=
    StructureSheaf.toStalkₗ A V p
  let t' : G →ₗ[A] Rs.obj (s.obj (tilde (R := .of A) G)) :=
    StructureSheaf.toStalkₗ A G p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A V p))
  have : IsLocalizedModule p.asIdeal.primeCompl t' :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl (StructureSheaf.toStalkₗ A G p))
  have hmap : (Rs.map (s.map (tilde.map b))).hom =
      IsLocalizedModule.map p.asIdeal.primeCompl t t' b.hom := by
    apply IsLocalizedModule.ext p.asIdeal.primeCompl t (IsLocalizedModule.map_units t')
    ext z
    exact (affineTildeStalk_naturality A p b z).trans
      (IsLocalizedModule.map_apply p.asIdeal.primeCompl t t' b.hom z).symm
  have hloc := congrArg (fun z ↦ z x)
    (IsLocalizedModule.map_iso_commute p.asIdeal.primeCompl t t' b.hom)
  rw [← hmap] at hloc
  have hloc' : s.map (tilde.map b) ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x) =
      (IsLocalizedModule.iso p.asIdeal.primeCompl t')
        (LocalizedModule.map p.asIdeal.primeCompl b.hom x) := hloc
  have htriangle : tilde.map b ≫ Scheme.Modules.fromTildeΓ (R := .of A) W = d := by
    change (tilde.functor (.of A)).map
      ((tilde.isoTop (R := .of A) V).hom ≫
        (moduleSpecΓFunctor (R := .of A)).map d) ≫ _ = _
    rw [Functor.map_comp, Category.assoc]
    have hn := (Scheme.Modules.fromTildeΓNatTrans (R := .of A)).naturality d
    change (tilde.functor (.of A)).map ((moduleSpecΓFunctor (R := .of A)).map d) ≫
      Scheme.Modules.fromTildeΓ (R := .of A) W =
      Scheme.Modules.fromTildeΓ (R := .of A) (tilde V) ≫ d at hn
    rw [hn]
    rw [← Category.assoc]
    have ht := (tilde.adjunction (R := .of A)).left_triangle_components V
    change (tilde.functor (.of A)).map (tilde.isoTop (R := .of A) V).hom ≫
      Scheme.Modules.fromTildeΓ (R := .of A) (tilde V) = 𝟙 _ at ht
    rw [ht, Category.id_comp]
  change s.map (Scheme.Modules.fromTildeΓ (R := .of A) W)
      ((IsLocalizedModule.iso p.asIdeal.primeCompl t')
        (LocalizedModule.map p.asIdeal.primeCompl b.hom x)) =
    s.map d ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x)
  rw [← hloc']
  change (s.map (tilde.map b) ≫
    s.map (Scheme.Modules.fromTildeΓ (R := .of A) W))
      ((IsLocalizedModule.iso p.asIdeal.primeCompl t) x) = _
  rw [← s.map_comp, htriangle]
  rfl

end AlgebraicGeometry
