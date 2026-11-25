/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Comparison data for inverse image opens of a union

Source: Stacks Project, Tag 08BW; canonical restriction diagram.
(blueprint: lem-sc-open-union-restriction-comparison-data).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  Functor.additive_of_preserves_binary_products

@[instance_reducible]
private def transportDerived
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] (e : C ≌ D) : HasDerivedCategory.{w} D := by
  let : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
  let ed := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory D) := (locallySmall_congr ed).mp inferInstance
  exact (HomologicalComplex.quasiIso D (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private def overlapRestrictionIso (X : Scheme.{u}) {A Y : X.Opens} (i : A ⟶ Y) :
    schemeOpenOverlapRestriction X i ≅ Modules.restrictFunctor (X.homOfLE (leOfHom i)) :=
  Functor.isoWhiskerLeft (Modules.overEquiv Y).inverse
      (Modules.overMapCompOverEquiv i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Modules.overEquiv Y).counitIso _ ≪≫ Functor.leftUnitor _

set_option backward.isDefEq.respectTransparency false in
private def inverseRestrictionEquivalence {S T : Scheme.{u}} (s : S ≅ T) :
    SheafOfModules.{u} (moduleRings S.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings T.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (Modules.restrictFunctor s.inv) (Modules.restrictFunctor s.hom)
    ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem directComparison (X : Scheme.{u}) {A Y : X.Opens} (i : A ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Y.ι ⁻¹ᵁ A).toScheme.toRingedSpace))] :
    ∃ e : schemeDerivedCategory (Y.ι ⁻¹ᵁ A).toScheme ≌ schemeDerivedCategory A.toScheme,
      Nonempty ((schemeOpenRestriction Y.toScheme (Y.ι ⁻¹ᵁ A)).mapDerivedCategory ⋙
        e.functor ≅ (schemeOpenOverlapRestriction X i).mapDerivedCategory) := by
  let U := Y.ι ⁻¹ᵁ A
  let s := Opens.isoOfLE (leOfHom i)
  let e₀ := inverseRestrictionEquivalence s
  have fac : s.inv ≫ U.ι = X.homOfLE (leOfHom i) := by
    apply (cancel_mono Y.ι).mp
    simp [s, U]
  let c : schemeOpenRestriction Y.toScheme U ⋙ e₀.functor ≅
      schemeOpenOverlapRestriction X i :=
    Functor.isoWhiskerRight (Modules.overFunctorEquiv U) e₀.functor ≪≫
      (Modules.restrictFunctorComp s.inv U.ι).symm ≪≫
      Modules.restrictFunctorCongr fac ≪≫ (overlapRestrictionIso X i).symm
  exact ⟨e₀.mapDerivedCategory, ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso c⟩⟩

attribute [local irreducible] Functor.mapDerivedCategory transportDerived

/-- Comparison equivalences and restriction isomorphisms on the three inverse image opens.
Source: Stacks Project Tag 08BW, canonical restriction diagram.
(blueprint: lem-sc-open-union-restriction-comparison-data).

Proof: The image of U under the union inclusion is W, since W is contained in the union;
likewise the image of T is V and the image of their intersection is W intersect V.
The open immersion therefore induces scheme isomorphisms from these three inverse image
opens to W, V, and their intersection. Their exact equivalences of module sheaves induce
derived equivalences. To obtain the derived localizations in Hom universe w, first use
nonempty_derivedOpenLocalization on the union scheme and transport along overEquiv.
The induced equivalence with the standard derived category transfers local w-smallness
by locallySmall_congr; hasLocalizationOfLocallySmall constructs the localization.
For each scheme isomorphism compare the
restriction from the union with the corresponding overlap restriction in X by
Modules.overMapCompOverEquiv, overFunctorEquiv, restrictFunctorComp, and
restrictFunctorCongr. Apply mapDerivedCategoryNatIso and mapDerivedCategoryCompIso
to these underived isomorphisms. This yields qW, qV, and the direct intersection
comparison; no compatibility of the overlap arrows is claimed here. For an empty
open the same scheme isomorphism and restriction construction apply. -/
theorem open_union_restriction_comparison_data
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    :
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let U := (W ⊔ V).ι ⁻¹ᵁ W
    let T := (W ⊔ V).ι ⁻¹ᵁ V
      ∃ hU : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      letI := hU
      ∃ hT : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace)),
      letI := hT
      ∃ hI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (moduleRings (U ⊓ T).toScheme.toRingedSpace)),
      letI := hI
      let RU := (schemeOpenRestriction (W ⊔ V).toScheme U).mapDerivedCategory
      let RT := (schemeOpenRestriction (W ⊔ V).toScheme T).mapDerivedCategory
      ∃ (eW : schemeDerivedCategory U.toScheme ≌ schemeDerivedCategory W.toScheme)
        (eV : schemeDerivedCategory T.toScheme ≌ schemeDerivedCategory V.toScheme)
        (_qW : RU ⋙ eW.functor ≅ PW) (_qV : RT ⋙ eV.functor ≅ PV),
      ∃ (eI : schemeDerivedCategory (U ⊓ T).toScheme ≌
          schemeDerivedCategory (W ⊓ V).toScheme),
        Nonempty ((schemeOpenRestriction (W ⊔ V).toScheme (U ⊓ T)).mapDerivedCategory ⋙
          eI.functor ≅ (schemeOpenOverlapRestriction X
            (homOfLE (inf_le_left.trans le_sup_left) : W ⊓ V ⟶ W ⊔ V)).mapDerivedCategory)
    := by
  classical
  rename_i dX dW dV dWV dY
  intro PW PV U T
  -- Bind each witness before elimination to avoid generalizing the dependent goal.
  have hO := nonempty_derivedOpenLocalization (W ⊔ V).toScheme
  obtain ⟨hO⟩ := hO
  let := hO
  let hD (Z : (W ⊔ V).toScheme.Opens) : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toScheme.toRingedSpace)) :=
    transportDerived (Modules.overEquiv Z)
  let hU := hD U
  let hT := hD T
  let hI := hD (U ⊓ T)
  let := hU
  let := hT
  let := hI
  have hW := @directComparison.{u, w} X W (W ⊔ V)
    (homOfLE le_sup_left) dW dY hU
  obtain ⟨eW, ⟨qW⟩⟩ := hW
  have hV := @directComparison.{u, w} X V (W ⊔ V)
    (homOfLE le_sup_right) dV dY hT
  obtain ⟨eV, ⟨qV⟩⟩ := hV
  have hInt := @directComparison.{u, w} X (W ⊓ V) (W ⊔ V)
    (homOfLE (inf_le_left.trans le_sup_left)) dWV dY hI
  obtain ⟨eI, ⟨qI⟩⟩ := hInt
  exact ⟨hU, hT, hI, eW, eV, qW, qV, eI, ⟨qI⟩⟩

end

end AlgebraicGeometry.Scheme
