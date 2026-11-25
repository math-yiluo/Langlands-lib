/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction

/-! # Conjugation invariance of derived scalar units

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md, finite coefficient extension paragraph
(blueprint: lem-amb-cartier-derived-unit-conjugation).

## Main statements

* `isCartierDerivedScalarUnit_of_iso_conj`: the derived scalar-unit property is
  invariant under isomorphisms of its source and target sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

open Scheme

/--
The unbounded derived scalar-unit Hom bijections are preserved when the source
and target are replaced by isomorphic sheaves and the map is conjugated by
those isomorphisms.  Source: the finite coefficient extension paragraph of
the GeoCartier proof (blueprint: lem-amb-cartier-derived-unit-conjugation).

Proof: for each unbounded target, naturality of the degree-zero comparison
identifies the new Hom map with the composite of the old Hom bijection and the
Hom-set equivalences induced by the two displayed isomorphisms.  The inverse
isomorphisms give inverses to these two additional bijections.  Explicitly, if
`Φ_η` denotes the defining map, naturality gives
`Φ_(eF.hom ≫ η ≫ Res.map eG.hom) f = eF.hom[0] ≫
Φ_η (eG.hom[0] ≫ f)` for every `f`, and the two inverse isomorphisms invert
the outer Hom-set maps.
-/
theorem isCartierDerivedScalarUnit_of_iso_conj
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F F' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (G G' : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).obj G)
    (hη : IsCartierDerivedScalarUnit φ T F G η)
    (eF : F' ≅ F) (eG : G ≅ G') :
    IsCartierDerivedScalarUnit φ T F' G'
      (eF.hom ≫ η ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ).map eG.hom) := by
  unfold IsCartierDerivedScalarUnit at hη ⊢
  intro K
  let DR := DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)) 0
  let DS := DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S)) 0
  let Res := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
  let γ := Res.mapDerivedCategorySingleFunctor 0
  have bG : Function.Bijective (fun f : DS.obj G' ⟶ K ↦ DS.map eG.hom ≫ f) :=
    (DS.mapIso eG).symm.homFromEquiv.bijective
  have bF : Function.Bijective
      (fun f : DR.obj F ⟶ Res.mapDerivedCategory.obj K ↦ DR.map eF.hom ≫ f) :=
    (DR.mapIso eF).symm.homFromEquiv.bijective
  have hb := bF.comp ((hη K).comp bG)
  have hn : DR.map (Res.map eG.hom) ≫ γ.inv.app G' =
      γ.inv.app G ≫ Res.mapDerivedCategory.map (DS.map eG.hom) :=
    γ.inv.naturality eG.hom
  convert hb using 1
  funext f
  change DR.map (eF.hom ≫ η ≫ Res.map eG.hom) ≫ γ.inv.app G' ≫
      Res.mapDerivedCategory.map f =
    DR.map eF.hom ≫ DR.map η ≫ γ.inv.app G ≫
      Res.mapDerivedCategory.map (DS.map eG.hom ≫ f)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (DR.map (Res.map eG.hom)), hn]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale
