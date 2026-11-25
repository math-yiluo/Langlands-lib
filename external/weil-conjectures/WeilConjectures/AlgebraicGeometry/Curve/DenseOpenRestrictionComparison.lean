/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import WeilConjectures.AlgebraicGeometry.Curve.LowerShriekCoefficientCounit

/-!
# DenseOpenRestrictionComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-restriction-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-restriction-comparison).

Proof: Let a : W → X be any open immersion. Intersecting the dense open U with W leaves a
dense open with finite zero-dimensional complement. The open-closed sequence on X
and its restriction to W therefore identify H^2(G) with H^2(F), both on X and on W.
The pullback long exact ladder makes these identifications commute with restriction
along a. Surjectivity transports in both directions across this square of additive
equivalences: lift the corresponding class through the surjective restriction map,
then through the inverse horizontal equivalence; commutativity and injectivity of the
other horizontal equivalence give the required equality. Since a was arbitrary this
proves exactly the equivalence of the two restriction predicates.
-/
theorem IsCurve.dense_open_restriction_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) F ↔
      IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) G := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let T := sheafCompose P.C.smallEtaleTopology E
  let V := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let F := T.obj P.F
  let B := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
  let G := T.obj B
  let ε : V.obj G ⟶ V.obj F := V.map (T.map
    ((Etale.openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
      U.ι).counit.app P.F))
  let : IsCurve P.toSpec := P.isCurve
  obtain ⟨e, he⟩ := Etale.exists_lowerShriek_coefficient_counit U P.F
  let e' := V.mapIso e
  let δ := V.map ((Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).counit.app F)
  have hcomp : e'.hom ≫ ε = δ := by
    change V.map e.hom ≫ V.map (T.map _) = V.map _
    rw [← V.map_comp]
    exact congrArg V.map he
  obtain ⟨hhigh, hopen⟩ := IsCurve.dense_open_high_cohomology
    (ULift.{u + 1} ℤ) P.toSpec F U hU
  have hi : Function.Bijective (Sheaf.H.map ε 2) := by
    have hc : (Sheaf.H.map ε 2) ∘ (Sheaf.H.map e'.hom 2) = Sheaf.H.map δ 2 := by
      funext x
      dsimp only [Function.comp_apply]
      rw [← Sheaf.H.map_comp_apply, hcomp]
      rfl
    have he : Function.Bijective (Sheaf.H.map e'.hom 2) :=
      (Iso.addCommGroupIsoToAddEquiv
        ((Sheaf.functorH P.C.smallEtaleTopology 2).mapIso e')).bijective
    exact he.of_comp_iff _ |>.mp (hc.symm ▸ hhigh 2 (by omega))
  have hj {W : Scheme.{u}} (a : W ⟶ P.C) [IsOpenImmersion a] :
      Function.Bijective (Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} a).map ε) 2) := by
    let A := Etale.upperStar AddCommGrpCat.{u + 1} a
    have hc : (Sheaf.H.map (A.map ε) 2) ∘ (Sheaf.H.map (A.map e'.hom) 2) =
        Sheaf.H.map (A.map δ) 2 := by
      funext x
      dsimp only [Function.comp_apply]
      rw [← Sheaf.H.map_comp_apply, ← A.map_comp, hcomp]
      rfl
    have he : Function.Bijective (Sheaf.H.map (A.mapIso e').hom 2) :=
      (Iso.addCommGroupIsoToAddEquiv
        ((Sheaf.functorH W.smallEtaleTopology 2).mapIso (A.mapIso e'))).bijective
    exact he.of_comp_iff _ |>.mp (hc.symm ▸ hopen a)
  change IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) F ↔
    IsCurve.SurjectiveRestrictionTwo (ULift.{u + 1} ℤ) G
  have hrestriction {W : Scheme.{u}} (a : W ⟶ P.C) [IsOpenImmersion a] :
      Function.Surjective (Etale.cohomologyMap a (V.obj G) 2) ↔
        Function.Surjective (Etale.cohomologyMap a (V.obj F) 2) := by
    have hcomm :
        (Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} a).map ε) 2) ∘
          (Etale.cohomologyMap a (V.obj G) 2) =
        (Etale.cohomologyMap a (V.obj F) 2) ∘ (Sheaf.H.map ε 2) := by
      funext x
      exact (Etale.cohomologyMap_map a 2 ε x).symm
    rw [← Function.Surjective.of_comp_iff' (hj a), hcomm,
      Function.Surjective.of_comp_iff _ hi.surjective]
  constructor
  · intro h W a _
    exact (hrestriction a).mpr (h a)
  · intro h W a _
    exact (hrestriction a).mp (h a)

end AlgebraicGeometry
