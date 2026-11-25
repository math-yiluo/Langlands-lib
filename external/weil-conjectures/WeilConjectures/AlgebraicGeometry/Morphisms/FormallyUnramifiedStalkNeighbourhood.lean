/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# An unramified stalk has an unramified neighbourhood

## References

* Stacks Project, Tag 02GF, openness of the unramified locus
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private theorem isUnramifiedAt_appLE_of_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : (f.stalkMap x).hom.FormallyUnramified)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V) :
    let := (f.appLE U V e).hom.toAlgebra
    Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  algebraize [(f.appLE U V e).hom]
  have H : (Y.presheaf.germ U _ (e hxV)).hom.FormallyUnramified := by
    algebraize [(Y.presheaf.germ U _ (e hxV)).hom]
    have := hU.isLocalization_stalk ⟨f x, e hxV⟩
    rw [← (Y.presheaf.germ U _ (e hxV)).hom.algebraMap_toAlgebra,
      RingHom.formallyUnramified_algebraMap]
    exact .of_isLocalization (hU.primeIdealOf ⟨_, e hxV⟩).asIdeal.primeCompl
  algebraize [(X.presheaf.germ V x hxV).hom]
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let iso := IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
  rw [Algebra.IsUnramifiedAt, ← RingHom.formallyUnramified_algebraMap]
  convert! (H.comp hx).comp (RingHom.FormallyUnramified.of_surjective iso.surjective)
  rw [← CommRingCat.hom_comp, f.germ_stalkMap,
    ← X.presheaf.germ_res (homOfLE e) _ hxV, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp, ← RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq Γ(Y, U) Γ(X, V), iso.toAlgHom.comp_algebraMap.symm]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Formal unramifiedness of a stalk map spreads to a source neighbourhood for a
morphism locally of finite type. -/
theorem FormallyUnramified.exists_neighbourhood_of_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hx : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ V : X.Opens, x ∈ V ∧ FormallyUnramified (V.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hfxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, e⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxU (f ⁻¹ᵁ U).isOpen
  let := (f.appLE U V e).hom.toAlgebra
  have : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (f.finiteType_appLE hU hV e).essFiniteType
  have := isUnramifiedAt_appLE_of_stalkMap f x hx hU hV e hxV
  obtain ⟨g, hg, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
    (R := Γ(Y, U)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let W := X.basicOpen g
  have hW : IsAffineOpen W := hV.basicOpen g
  have hxW : x ∈ W := by
    have hmem : hV.primeIdealOf ⟨x, hxV⟩ ∈ PrimeSpectrum.basicOpen g := hg
    rw [← hV.fromSpec_preimage_basicOpen] at hmem
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen g at hmem
    rwa [hV.fromSpec_primeIdealOf] at hmem
  have heW : W ≤ f ⁻¹ᵁ U := (X.basicOpen_le g).trans e
  have hres : FormallyUnramified (f.resLE U W heW) := by
    have : IsAffine (Scheme.Opens.toScheme U) := hU
    have : IsAffine W.toScheme := hW
    rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)]
    apply (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U W heW)).mpr
    let := (f.appLE U W heW).hom.toAlgebra
    have := hu
    have := hV.isLocalization_basicOpen g
    have : IsScalarTower Γ(Y, U) Γ(X, V) Γ(X, W) := by
      apply IsScalarTower.of_algebraMap_eq
      intro r
      change (f.appLE U W heW) r =
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op) ((f.appLE U V e) r)
      exact congr($(f.appLE_map e (homOfLE (X.basicOpen_le g)).op) r).symm
    rw [← RingHom.algebraMap_toAlgebra (f.appLE U W heW).hom,
      RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, W)).restrictScalars
        Γ(Y, U))
  have : FormallyUnramified ((f.resLE U W heW) ≫ Scheme.Opens.ι U) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ hres inferInstance
  exact ⟨W, hxW, by simpa only [Scheme.Hom.resLE_comp_ι] using this⟩

end AlgebraicGeometry
