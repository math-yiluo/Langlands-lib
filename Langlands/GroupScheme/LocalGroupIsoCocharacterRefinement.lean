import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.LocalGroupIsoBorelRefinement
import Langlands.GroupScheme.Rational.FiniteFieldCocycleTorusReduction
import Mathlib.FieldTheory.Galois.Basic

/-! # Cocharacter matching under a finite Galois refinement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U V : Over S}

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_cocharacter_points (e : LocalGroupIso G H U)
    (χ₁ : (Gm S).toGrp ⟶ G) (χ₂ : (Gm S).toGrp ⟶ H)
    (n : Over.mk (𝟙 U.left) ⟶ ((baseChange U.hom).obj H).X)
    (h : Dynamic.baseChangeCocharacter U.hom χ₁ ≫ e.toBaseChangeIso.hom ≫
      (((baseChange U.hom).obj H).innerIso n).hom =
        Dynamic.baseChangeCocharacter U.hom χ₂)
    {T : Over S} (a : T ⟶ U) (z : T ⟶ (Gm S).X) :
    (a ≫ baseChangeBasePointsEquiv U.hom H n) * e.toFun a (z ≫ χ₁.hom.hom) *
        (a ≫ baseChangeBasePointsEquiv U.hom H n)⁻¹ = z ≫ χ₂.hom.hom := by
  let χ₁' := (baseChange U.hom).map χ₁
  let χ₂' := (baseChange U.hom).map χ₂
  let c := (((baseChange U.hom).obj H).innerIso n).hom
  let z' := (coverPointsEquiv (Gm S).toGrp a).symm z
  have h' : χ₁' ≫ e.toBaseChangeIso.hom ≫ c = χ₂' :=
    (cancel_epi (Gm.baseChangeIso U.hom).inv).mp (by
      simpa only [Dynamic.baseChangeCocharacter, Category.assoc] using h)
  have hz := congrArg (fun f => z' ≫ f.hom.hom) h'
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hz
  rw [comp_innerIso_hom] at hz
  have hp : coverPointsEquiv H a (((baseChange U.hom).obj H).constantPoint n (coverTest a)) =
      a ≫ baseChangeBasePointsEquiv U.hom H n := by
    apply Over.OverMorphism.ext
    simp only [coverPointsEquiv_left, constantPoint, Over.comp_left,
      Over.homMk_left, baseChangeBasePointsEquiv_left, Category.assoc]
    rfl
  have hx : z' ≫ χ₁'.hom.hom = (coverPointsEquiv G a).symm (z ≫ χ₁.hom.hom) := by
    apply (coverPointsEquiv G a).injective
    rw [coverPointsEquiv_comp, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have he := congrArg (coverPointsEquiv H a) hz
  rw [map_mul, map_mul, map_inv, hp, hx, toBaseChangeIso_coverPoints,
    coverPointsEquiv_comp, MulEquiv.apply_symm_apply] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_cocharacter_points_of_refine (e : LocalGroupIso G H U)
    (χ₁ : (Gm S).toGrp ⟶ G) (χ₂ : (Gm S).toGrp ⟶ H) (p : V ⟶ U)
    [Flat p.left] [Surjective p.left] (n : U ⟶ H.X)
    (h : ∀ (T : Over S) (a : T ⟶ V) (z : T ⟶ (Gm S).X),
      (a ≫ p ≫ n) * (e.refine p).toFun a (z ≫ χ₁.hom.hom) * (a ≫ p ≫ n)⁻¹ =
        z ≫ χ₂.hom.hom)
    {T : Over S} (a : T ⟶ U) (z : T ⟶ (Gm S).X) :
    (a ≫ n) * e.toFun a (z ≫ χ₁.hom.hom) * (a ≫ n)⁻¹ = z ≫ χ₂.hom.hom := by
  let W : Over S := Over.mk (pullback.snd p.left a.left ≫ T.hom)
  let t : W ⟶ T := Over.homMk (pullback.snd p.left a.left)
  let b : W ⟶ V := Over.homMk (pullback.fst p.left a.left) (by
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w a]
    rfl)
  let : Epi t.left := Flat.epi_of_flat_of_surjective (pullback.snd p.left a.left)
  let : Epi t := Over.epi_of_epi_left t
  have hba : b ≫ p = t ≫ a := Over.OverMorphism.ext pullback.condition
  apply (cancel_epi t).mp
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← e.naturality, ← Category.assoc]
  simpa only [refine_toFun, ← Category.assoc, hba] using h W b (t ≫ z)

private theorem twist_conjugation_by_target (e : LocalGroupIso G H U)
    (n : U ⟶ H.X) {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (e.twist (AutomorphicAction.conjugation (𝟙 G))
        ((e.toFun (𝟙 U)).symm n)).toFun a g =
      (a ≫ n) * e.toFun a g * (a ≫ n)⁻¹ := by
  change e.toFun a ((AutomorphicAction.conjugation (𝟙 G)).act
    (a ≫ (e.toFun (𝟙 U)).symm n) g) = _
  rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id,
    map_mul, map_mul, map_inv]
  have hc := e.naturality a (𝟙 U) ((e.toFun (𝟙 U)).symm n)
  rw [Category.comp_id, MulEquiv.apply_symm_apply] at hc
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- A specified geometric conjugator matching two cocharacters descends, together
with the matching equation, to a finite Galois refinement of the original
trivialization. -/
theorem exists_finiteGalois_cocharacterMatching
    {k L Ω : Type u} [Field k] [Field L] [Field Ω] [Algebra k L] [Algebra k Ω]
    [FiniteDimensional k L] [Algebra.IsSeparable k Ω] [Normal k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (e : LocalGroupIso G H (ringTest k L)) (φ : L →ₐ[k] Ω)
    (χ₁ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (χ₂ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange (algebraBaseMap k Ω)).obj H).X)
    (h : Dynamic.baseChangeCocharacter (algebraBaseMap k Ω) χ₁ ≫
      (e.refine (ringTestMap k φ)).toBaseChangeIso.hom ≫
        (((baseChange (algebraBaseMap k Ω)).obj H).innerIso n).hom =
          Dynamic.baseChangeCocharacter (algebraBaseMap k Ω) χ₂) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E) (j : L →ₐ[k] E) (f : ringTest k E ⟶ G.X),
      ∀ (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ ringTest k E)
        (z : T ⟶ (Gm (Spec (CommRingCat.of k))).X),
        ((e.refine (ringTestMap k j)).twist (AutomorphicAction.conjugation (𝟙 G)) f).toFun
          a (z ≫ χ₁.hom.hom) = z ≫ χ₂.hom.hom := by
  let nΩ : ringTest k Ω ⟶ H.X := baseChangeBasePointsEquiv (ringTest k Ω).hom H n
  obtain ⟨E₀, h₀, -, n₀, hn₀⟩ := Cocycle.exists_finite_factor H nΩ (∅ : Set Ω)
  let : FiniteDimensional k E₀ := h₀
  let : FiniteDimensional k φ.fieldRange :=
    FiniteDimensional.of_surjective φ.equivFieldRange.toLinearMap φ.equivFieldRange.surjective
  let D := E₀ ⊔ φ.fieldRange
  let E := IntermediateField.normalClosure k D Ω
  let : FiniteDimensional k E := normalClosure.is_finiteDimensional k D Ω
  let j₀ : E₀ →ₐ[k] E := IntermediateField.inclusion (le_sup_left.trans D.le_normalClosure)
  let j : L →ₐ[k] E := φ.codRestrict E.toSubalgebra fun x =>
    (le_sup_right.trans D.le_normalClosure : φ.fieldRange ≤ E) ⟨x, rfl⟩
  let p := ringTestMap k E.val
  let nE := ringTestMap k j₀ ≫ n₀
  have hnE : p ≫ nE = nΩ := by
    rw [← Category.assoc, ← ringTestMap_comp]
    exact hn₀
  have hj : p ≫ ringTestMap k j = ringTestMap k φ := by
    rw [← ringTestMap_comp]
    rfl
  let eE := e.refine (ringTestMap k j)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, j,
    (eE.toFun (𝟙 _)).symm nE, ?_⟩
  intro T a z
  rw [twist_conjugation_by_target]
  obtain ⟨-, hflat, hsurj⟩ := Cocycle.ringTestMap_fpqc E.val
  let : Flat p.left := hflat
  let : Surjective p.left := hsurj
  apply conjugate_cocharacter_points_of_refine eE χ₁ χ₂ p nE
  intro W b w
  simpa only [Category.assoc, hnE, refine_toFun, eE, hj] using
    conjugate_cocharacter_points (e.refine (ringTestMap k φ)) χ₁ χ₂ n h b w

end Langlands.GroupScheme.LocalGroupIso
