/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The eight curve assertions pass to retracts

Source: Stacks Project, Etale Cohomology, Section 03SB, proof of Lemma 03SD,
first paragraph (blueprint: lem-weil-pbc-curve-assertions-retract).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem cohomology_section_injective {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) (r : G ⟶ F) (har : a ≫ r = 𝟙 F) (q : ℕ) :
    Function.Injective (Sheaf.H.map a q) := by
  apply Function.LeftInverse.injective (g := Sheaf.H.map r q)
  intro x
  rw [← Sheaf.H.map_comp_apply, har, Sheaf.H.map_id_apply]

private theorem pullback_surjective_of_retract {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) (r : G ⟶ F) (har : a ≫ r = 𝟙 F) (q : ℕ)
    (h : Function.Surjective (Etale.cohomologyMap f G q)) :
    Function.Surjective (Etale.cohomologyMap f F q) := by
  intro y
  obtain ⟨x, hx⟩ := h (Sheaf.H.map ((Etale.upperStar _ f).map a) q y)
  refine ⟨Sheaf.H.map r q x, ?_⟩
  rw [Etale.cohomologyMap_map, hx, ← Sheaf.H.map_comp_apply,
    ← CategoryTheory.Functor.map_comp, har, CategoryTheory.Functor.map_id,
    Sheaf.H.map_id_apply]

private theorem pullback_bijective_of_retract {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) (r : G ⟶ F) (har : a ≫ r = 𝟙 F) (q : ℕ)
    (h : Function.Bijective (Etale.cohomologyMap f G q)) :
    Function.Bijective (Etale.cohomologyMap f F q) := by
  refine ⟨?_, pullback_surjective_of_retract f a r har q h.2⟩
  intro x y hxy
  apply cohomology_section_injective a r har q
  apply h.1
  simpa only [Etale.cohomologyMap_map] using
    congrArg (Sheaf.H.map ((Etale.upperStar _ f).map a) q) hxy

/-- The eight curve assertions pass from a torsion abelian sheaf `H` to `P.F` when
`a ≫ b` is invertible and the conditional coefficient hypotheses pass from `P.F` to `H`.
The local `E` is the same coefficient equivalence used in finite_pushforward_assertions;
it views abelian groups as modules over `ULift ℤ`, adding no coefficient structure.
Source: Stacks Project, Section 03SB, proof of Lemma 03SD, first paragraph
(blueprint: lem-weil-pbc-curve-assertions-retract).

Proof:
1. Put `r = b ≫ inv (a ≫ b)`. Associativity gives `a ≫ r = 𝟙 P.F`.
Apply the coefficient-equivalence and underlying-abelian-group functors to this identity.
2. `Sheaf.H.map_comp_apply` and `Sheaf.H.map_id_apply` make the map induced by `r`
a left inverse to the map induced by `a`. Hence the latter is injective in every degree.
3. C1 and C2 descend by injectivity into a subsingleton. For C3 pass the primary
hypothesis to H first and use the same argument.
4. For C4 and C5 use `Scheme.isConstructibleSheaf_integral_iff` to turn module
constructibility of G into the underlying-set predicate, pass it through hconstructible,
and turn it back into module constructibility of H. Torsion is used in this comparison.
Pass invertible order to H for C4. Injectivity into its finite cohomology proves both fields.
5. Naturality `Etale.cohomologyMap_map` for a and r descends surjectivity of any pullback:
lift the image of a target class under the section, then apply the retraction to the lift.
Naturality and the retraction identity show that this is a lift of the original class.
Injectivity descends by applying the coefficient section, then injectivity for H,
then injectivity of the section on source cohomology.
6. Apply the bijectivity argument to the extension projection for C6 and C7, passing
invertible order to H in C6. Apply the surjectivity argument to the open immersion
in degree two for C8. These are the eight fields of Assertions. -/
theorem IsCurve.assertions_of_isIso_comp {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k)
    (H : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : P.C.IsTorsionAbelianSheaf H) (a : P.F ⟶ H) (b : H ⟶ P.F)
    [IsIso (a ≫ b)]
    (hconstructible : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)) →
      (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj H))) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let G' := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let H' := (sheafCompose P.C.smallEtaleTopology E).obj H
    (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G' →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) H') →
    (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
      Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G' p →
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) H' p) →
    IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec H' →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G' := by
  dsimp only
  intro horder hprimary h
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let T := sheafCompose P.C.smallEtaleTopology E ⋙
    sheafCompose P.C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let a' := T.map a
  let r' := T.map (b ≫ inv (a ≫ b))
  have har : a' ≫ r' = 𝟙 (T.obj P.F) := by
    dsimp [a', r']
    rw [← T.map_comp]
    have ha : a ≫ (b ≫ inv (a ≫ b)) = 𝟙 P.F := by
      rw [← Category.assoc, IsIso.hom_inv_id]
    rw [ha, T.map_id]
  have hinj (q : ℕ) := cohomology_section_injective a' r' har q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let : Subsingleton (Sheaf.H (T.obj H) q) := h.subsingleton_of_two_lt q hq
    exact (hinj q).subsingleton
  · intro _ q hq
    let : Subsingleton (Sheaf.H (T.obj H) q) :=
      h.subsingleton_of_one_lt_of_isAffine q hq
    exact (hinj q).subsingleton
  · intro p _ _ hG q hq
    let : Subsingleton (Sheaf.H (T.obj H) q) :=
      h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hprimary p hG) q hq
    exact (hinj q).subsingleton
  · intro hG hGorder q
    have hPc : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)) :=
      (Scheme.isConstructibleSheaf_integral_iff P.F 
        ((Scheme.isTorsionAbelianSheaf_characterizations
          P.F).1.mpr P.isTorsion)).mp hG
    let : Scheme.IsConstructibleSheaf ((sheafCompose _ E).obj H) :=
      (Scheme.isConstructibleSheaf_integral_iff H hH).mpr (hconstructible hPc)
    let : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
        ((sheafCompose _ E).obj H) := horder hGorder
    let : Finite (Sheaf.H (T.obj H) q) := h.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (hinj q)
  · intro _ hG q
    have hPc : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)) :=
      (Scheme.isConstructibleSheaf_integral_iff P.F 
        ((Scheme.isTorsionAbelianSheaf_characterizations
          P.F).1.mpr P.isTorsion)).mp hG
    let : Scheme.IsConstructibleSheaf ((sheafCompose _ E).obj H) :=
      (Scheme.isConstructibleSheaf_integral_iff H hH).mpr (hconstructible hPc)
    let : Finite (Sheaf.H (T.obj H) q) := h.finite_of_isProper q
    exact Finite.of_injective _ (hinj q)
  · intro hG k' _ _ X' ι f' ι' hp q
    let := horder hG
    exact pullback_bijective_of_retract ι' a' r' har q
      (h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hp q)
  · intro _ k' _ _ X' ι f' ι' hp q
    exact pullback_bijective_of_retract ι' a' r' har q
      (h.bijective_cohomologyMap_of_isProper k' hp q)
  · intro W f _
    exact pullback_surjective_of_retract f a' r' har 2
      (h.surjective_cohomologyMap_of_isOpenImmersion f)

end AlgebraicGeometry
