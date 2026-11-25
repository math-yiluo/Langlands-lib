/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso

/-! # Lifting a derived stalk morphism to a chain map between local perfect models

Source: Stacks Project, Tags 09RE (affine case), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-hom-lift).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

-- Generalizes restriction: no inclusion V ≤ U or geometric origin of T is required.
private theorem map_strictlyPerfect_of_mapFree
    (X : Scheme.{u}) (U V : X.Opens)
    (T : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    [T.PreservesZeroMorphisms]
    (e : ∀ m : ℕ, T.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
      SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K) :
    IsStrictlyPerfect X V ((T.mapHomologicalComplex (.up ℤ)).obj K) := by
  constructor
  · obtain ⟨a, b, hab⟩ := hK.1
    exact ⟨a, b, fun n hn ↦ T.map_isZero (hab n hn)⟩
  · intro n
    obtain ⟨m, i, r, hir⟩ := hK.2 n
    refine ⟨m, T.map i ≫ (e m).hom, (e m).inv ≫ T.map r, ?_⟩
    change (T.map i ≫ (e m).hom) ≫ (e m).inv ≫ T.map r = 𝟙 (T.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact T.map_id _

set_option backward.isDefEq.respectTransparency false in
/-- The comparison between the open stalk at `x` of a local model `P` of `G` on `U` and the
stalk of `G` at `x`, in the derived category of the stalk ring, built from the given
identification `eP` of the restriction of `G` with `P`: stalks commute with the derived
restriction, and the stalk of a restriction is the original stalk. -/
def perfectLocalModelStalkComparison
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (U : X.Opens) (hx : x ∈ U)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (eP : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P) :
    let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hx⟩
    letI : S.PreservesZeroMorphisms :=
      AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hx⟩
    DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (.up ℤ)).obj G) := by
  let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hx⟩
  have : S.PreservesZeroMorphisms :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hx⟩
  have : S.Additive := AlgebraicGeometry.openModuleStalkFunctor_additive X U ⟨x, hx⟩
  have : PreservesFiniteLimits S :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X U ⟨x, hx⟩
  have : PreservesFiniteColimits S :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X U ⟨x, hx⟩
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let Gu := (R.mapHomologicalComplex (.up ℤ)).obj G
  let d := (S.mapDerivedCategoryFactors.app P).symm ≪≫
    (S.mapDerivedCategory.mapIso eP).symm ≪≫
    S.mapDerivedCategory.mapIso (R.mapDerivedCategoryFactors.app G) ≪≫
    S.mapDerivedCategoryFactors.app Gu
  let ρ := (U.ι.stalkMap ⟨x, hx⟩).hom
  let A := ModuleCat.restrictScalars ρ
  let H := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hx⟩
  let C := ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (.up ℤ)).obj G
  have : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let c := (nonempty_restriction_stalk_extension_iso U.ι ⟨x, hx⟩ G).some
  let eρ := RingEquiv.ofBijective ρ
    (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap ⟨x, hx⟩))
  have : A.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  let ev := (NatIso.mapHomologicalComplex (Scheme.Modules.overFunctorEquiv U)
    (.up ℤ)).app G
  let q : (S.mapHomologicalComplex (.up ℤ)).obj Gu ≅ C :=
    (A.mapHomologicalComplex (.up ℤ)).mapIso
      ((H.mapHomologicalComplex (.up ℤ)).mapIso ev) ≪≫
    ((A.mapHomologicalComplex (.up ℤ)).mapIso c).symm ≪≫
    ((NatIso.mapHomologicalComplex
      (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) (.up ℤ)).app C).symm
  exact d ≪≫ DerivedCategory.Q.mapIso q

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary derived stalk morphism lifts to a chain map between strictly perfect
models restricted to a smaller affine neighbourhood. The stalk comparison isomorphisms identify
the derived image of that chain map with the original morphism. No invertibility of the
original morphism or the lifted map is asserted.

Source: Stacks Project, Tags 09RE (affine case), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-hom-lift).

Proof: On an affine neighbourhood of x in U, the finite-free retract terms of P and Q are
quasi-coherent and
correspond to finite projective modules over the ring of sections. The complexes are
bounded. Exactness of stalks identifies the stalks of the derived comparisons with the
prime localizations of these module complexes. The comparison isomorphisms cG, cH are
the canonical restriction comparison followed by `perfectLocalModelStalkComparison`.
Transport the given morphism by cG and cH. Present the prime localization as the filtered
colimit of principal localizations outside the prime (00CR). Surjectivity of the perfect
Hom comparison (09RE, or 0BC7 (2)) descends this morphism to one principal localization.
Bounded projective complexes are K-projective, so its derived morphism has a chain-map
representative. The affine correspondence transports this chain map back to the
restricted perfect sheaf complexes; exact restriction and stalk comparisons give the
stated equation. This uses only Hom surjectivity, not descent of an inverse or inverse
identities. Zero ranks and zero complexes cause no exception. -/
theorem exists_affine_perfect_stalk_hom_lift
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (U : X.Opens) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (iG : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P)
    (iH : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj H) ≅ DerivedCategory.Q.obj Q)
    (t : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      let c : T ⋙ S.mapHomologicalComplex (.up ℤ) ≅
          (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ) :=
        Functor.mapHomologicalComplexCompIso
          (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      let cG := DerivedCategory.Q.mapIso (c.app P) ≪≫
        perfectLocalModelStalkComparison X x U hxU G P iG
      let cH := DerivedCategory.Q.mapIso (c.app Q) ≪≫
        perfectLocalModelStalkComparison X x U hxU H Q iH
      ∃ f : T.obj P ⟶ T.obj Q,
        DerivedCategory.Q.map
          ((S.mapHomologicalComplex (.up ℤ)).map f) =
            cG.hom ≫ t ≫ cH.inv := by
  let a := perfectLocalModelStalkComparison X x U hxU G P iG
  let b := perfectLocalModelStalkComparison X x U hxU H Q iH
  obtain ⟨V, hxV, hV, hVU, g, hg⟩ :=
    exists_affine_perfect_open_stalk_derived_hom_descent
      X x U hxU P Q hP (a.hom ≫ t ≫ b.inv)
  let R := moduleRings X.toRingedSpace
  let T := (SheafOfModules.overMap.{u} R (homOfLE hVU : V ⟶ U)).mapHomologicalComplex
    (.up ℤ)
  let S : SheafOfModules.{u} (R.over V) ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
    openModuleStalkFunctor X V ⟨x, hxV⟩
  have : S.PreservesZeroMorphisms :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
  have : S.Additive := AlgebraicGeometry.openModuleStalkFunctor_additive X V ⟨x, hxV⟩
  have : PreservesFiniteLimits S :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
  have : PreservesFiniteColimits S :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
  let F := SheafOfModules.overMap.{u} R (homOfLE hVU : V ⟶ U)
  let e := fun m : ℕ ↦ (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
    (SheafOfModules.overMapUnitIso (R := R) (homOfLE hVU)).symm).symm
  obtain ⟨f, hf⟩ := perfect_affine_map_representative X V hV (T.obj P) (T.obj Q)
    (map_strictlyPerfect_of_mapFree X U V F e P hP)
    (map_strictlyPerfect_of_mapFree X U V F e Q hQ) g
  refine ⟨V, hxV, hV, hVU, f, ?_⟩
  have hn := S.mapDerivedCategoryFactors.hom.naturality f
  change S.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
      (S.mapDerivedCategoryFactors.app (T.obj Q)).hom =
    (S.mapDerivedCategoryFactors.app (T.obj P)).hom ≫
      DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map f) at hn
  rw [hf] at hn
  have he : DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map f) =
      (S.mapDerivedCategoryFactors.app (T.obj P)).inv ≫
        S.mapDerivedCategory.map g ≫ (S.mapDerivedCategoryFactors.app (T.obj Q)).hom := by
    rw [hn]
    simp
  rw [he, hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rfl

end
end AlgebraicGeometry.Scheme
