/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

/-! # Finite models of the outer terms of an open/closed localization triangle -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonObj CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryPlus

namespace AlgebraicGeometry.ProEtale
namespace CondensedRing
set_option backward.isDefEq.respectTransparency false in
private theorem pushScalarSingleIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    Nonempty ((Mod.extendScalars (coefficientMap a X)).obj ((lowerStar Λ k).obj P) ≅
      (lowerStar Λ' k).obj ((Mod.extendScalars (coefficientMap a Z)).obj P)) := by
  let Q := (Mod.extendScalars (coefficientMap a X)).obj ((lowerStar Λ k).obj P)
  have hzCond := openRestrictionPushforwardZero Λ k j hjk P
  have hz : IsZero ((upperStar Λ' j).obj Q) :=
    ((Mod.extendScalars (coefficientMap a U)).map_isZero hzCond).of_iso
      ((pullIso a j).app ((lowerStar Λ k).obj P)).symm
  obtain ⟨_, hsupport⟩ := abelian_closed_support_counit_and_unit k j hjk
  have hAb : IsIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} k).unit.app Q.X) := by
    apply hsupport
    exact ((Mod.forget _).map_isZero hz).of_iso
      ((profinitePointModuleForgetPullbackIso Λ' j).app Q).symm
  have := moduleUnitOfAbelian Λ' k Q hAb
  have hrec := condensed_open_closed_recollement Λ k j hjk
  rcases hrec with ⟨hc, hrec⟩
  rcases hrec with ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩
  exact ⟨asIso ((upperStarLowerStarAdjunction Λ' k).unit.app Q) ≪≫
    (lowerStar Λ' k).mapIso
      (((pullIso a k).app ((lowerStar Λ k).obj P)).symm ≪≫
        (Mod.extendScalars (coefficientMap a Z)).mapIso (e.app P))⟩

private theorem openModelIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (e : Nonempty ((Mod.extendScalars (coefficientMap a U)).obj P ≅
      (upperStar Λ' j).obj N)) :
    Nonempty ((Mod.extendScalars (coefficientMap a X)).obj
      ((openImmersionLowerShriek Λ j).obj P) ≅
      (openImmersionLowerShriek Λ' j).obj ((upperStar Λ' j).obj N)) := by
  obtain ⟨e⟩ := e
  exact ⟨(openImmersionShriekIso a j).app P ≪≫
    (openImmersionLowerShriek Λ' j).mapIso e⟩

private theorem closedModelIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (e : Nonempty ((Mod.extendScalars (coefficientMap a Z)).obj P ≅
      (upperStar Λ' k).obj N)) :
    Nonempty ((Mod.extendScalars (coefficientMap a X)).obj ((lowerStar Λ k).obj P) ≅
      (lowerStar Λ' k).obj ((upperStar Λ' k).obj N)) := by
  obtain ⟨e⟩ := e
  obtain ⟨ePush⟩ := pushScalarSingleIso a j k hjk P
  exact ⟨ePush ≪≫ (lowerStar Λ' k).mapIso e⟩

end CondensedRing

private theorem singleIsoTrans
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A B : C} {K : DerivedCategory C} (e : Nonempty (A ≅ B))
    (h : Nonempty ((DerivedCategory.singleFunctor C 0).obj B ≅ K)) :
    Nonempty ((DerivedCategory.singleFunctor C 0).obj A ≅ K) := by
  obtain ⟨e⟩ := e
  obtain ⟨h⟩ := h
  exact ⟨(DerivedCategory.singleFunctor C 0).mapIso e ≪≫ h⟩

private noncomputable def exactOuterSingleIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (N : C) :
    (DerivedCategory.singleFunctor C 0).obj (G.obj (F.obj N)) ≅
      DerivedCategory.Plus.ι.obj
        (G.mapDerivedCategoryPlus.obj
          (F.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N))) :=
  ((DerivedCategory.Plus.singleFunctorιIso C 0).app (G.obj (F.obj N))).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (((G.mapDerivedCategoryPlusSingleFunctor 0).app (F.obj N)).symm ≪≫
        G.mapDerivedCategoryPlus.mapIso ((F.mapDerivedCategoryPlusSingleFunctor 0).app N).symm)

attribute [local irreducible] exactOuterSingleIso

private theorem localizationTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ∃ D : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      D ∈ distTriang _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj
          ((CondensedRing.upperStar Λ j).obj N)) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ k).obj ((CondensedRing.upperStar Λ k).obj N)) ≅ D.obj₃) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj D.obj₂ ≅ N) := by
  have hrec := CondensedRing.condensed_open_closed_recollement Λ k j hjk
  rcases hrec with ⟨hc, hrec⟩
  rcases hrec with ⟨hjl, hjc, hkl, hkc, hsl, hsc, hcl, _, _, _, _, _, r⟩
  let _ := hc
  let _ := hjl
  let _ := hjc
  let _ := hkl
  let _ := hkc
  let _ := hsl
  let _ := hsc
  let _ := hcl
  obtain ⟨ish, ha, hl, r⟩ := r
  let _ := ha
  let _ := hl
  obtain ⟨ash, aj, bj, ai, bi, hjshift, hishift, r⟩ := r
  let _ := hjshift
  let _ := hishift
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, δ, ε, _, _, htri, _⟩ := r
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj N
  let Dp := Pretriangulated.Triangle.mk (aj.counit.app K) (ai.unit.app K) (δ.app K)
  let D := DerivedCategory.Plus.ι.mapTriangle.obj Dp
  refine ⟨D, DerivedCategory.Plus.ι.map_distinguished Dp (htri K), ?_, ?_, ?_⟩
  · exact ⟨exactOuterSingleIso (CondensedRing.upperStar Λ j)
      (CondensedRing.openImmersionLowerShriek Λ j) N⟩
  · exact ⟨exactOuterSingleIso (CondensedRing.upperStar Λ k) (CondensedRing.lowerStar Λ k) N⟩
  · exact ⟨(DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N⟩

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] CondensedRing.openImmersionShriekIso
  CondensedRing.upperStar CondensedRing.openImmersionLowerShriek
  CondensedRing.lowerStar CategoryTheory.Mod.extendScalars

private theorem localizationModelTriangle
    {ΛA ΛB Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj ΛA] [IsCommMonObj ΛA] [MonObj ΛB] [IsCommMonObj ΛB]
    [MonObj Λ] [IsCommMonObj Λ]
    (a : ΛA ⟶ Λ) [IsMonHom a] (b : ΛB ⟶ Λ) [IsMonHom b]
    {X U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k] (hjk : Set.range j = (Set.range k)ᶜ)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj ΛA U))
    (Q : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj ΛB Z))
    (eP : Nonempty ((Mod.extendScalars (coefficientMap a U)).obj P ≅
      (CondensedRing.upperStar Λ j).obj N))
    (eQ : Nonempty ((Mod.extendScalars (coefficientMap b Z)).obj Q ≅
      (CondensedRing.upperStar Λ k).obj N)) :
    ∃ D : Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      D ∈ distTriang _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap a X)).obj
          ((CondensedRing.openImmersionLowerShriek ΛA j).obj P)) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap b X)).obj
          ((CondensedRing.lowerStar ΛB k).obj Q)) ≅ D.obj₃) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj D.obj₂ ≅ N) := by
  obtain ⟨D, hD, eOpen, eClosed, eMiddle⟩ := localizationTriangle Λ j k hjk N
  refine ⟨D, hD, ?_, ?_, eMiddle⟩
  · exact singleIsoTrans (CondensedRing.openModelIso a j P N eP) eOpen
  · exact singleIsoTrans (CondensedRing.closedModelIso b j k hjk Q N eQ) eClosed

/-- Localization with the prescribed finite-coefficient images as its outer objects.

Source: `ModuleObject/Colimit/TwoColimit.lean`, support induction; condensed open/closed
recollement and change of coefficients.
(auxiliary; not a blueprint node)

Proof: apply condensed open/closed recollement to N in degree zero and include its first
localization triangle from the bounded-below derived category into the unbounded one.
Exactness of the open pullback and extension, and of the closed pullback and direct image,
identifies the outer objects with the single complexes of j! j* N and k_* k* N. Replace
j* N and k* N by the supplied scalar extensions. Scalar extension commutes with j! by
openImmersionShriekIso. For k_*, the proved pushScalarSingleIso helper below the source
imports gives the comparison: pullIso shows that the scalar extension is zero on U;
abelian closed support and moduleUnitOfAbelian make its closed unit invertible; pullIso
on Z and the closed counit identify its restriction with the scalar extension of PZ.
Thus the specified two scalar extensions give the required outer isomorphisms.
The middle object is N in degree zero, so its zeroth cohomology is N. No
constructibility assumption is needed here, and either complementary piece may be empty.
-/
theorem exists_finiteCoefficient_localization_triangle
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Z : Scheme.{u}} (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (padicSubfieldRingObj U ℓ EU))
    (EZ : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicSubfieldRingObj Z ℓ EZ))
    (eU : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) j).obj N))
    (eZ : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ EZ)).obj PZ ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) k).obj N)) :
    ∃ D : Pretriangulated.Triangle (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))),
      D ∈ distTriang _ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ EU)).obj
          ((CondensedRing.openImmersionLowerShriek
            (Profinite.continuousMapRingObj.{u} EU) j).obj PU)) ≅ D.obj₁) ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ EZ)).obj
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} EZ) k).obj PZ)) ≅
          D.obj₃) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ 0).obj D.obj₂ ≅ N) := by
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact localizationModelTriangle
    (ΛA := Profinite.continuousMapRingObj.{u} EU)
    (ΛB := Profinite.continuousMapRingObj.{u} EZ)
    (Λ := Profinite.padicAlgClRingObj.{u} ℓ)
    (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ EU)
    (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ EZ) j k hjk N PU PZ eU eZ

end AlgebraicGeometry.ProEtale
