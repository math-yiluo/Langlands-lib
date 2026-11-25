/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # The quotient-completion unit on arbitrary complexes

Source: Stacks Tags 099M and 0941; naturality of localization and derived comparisons.
(blueprint: lem-constant-completion-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

attribute [local irreducible] ConstantCompletion.reductionTower
  ConstantCompletion.ordinaryUnit ConstantCompletion.reductionUnit
  ConstantCompletion.rlim ConstantCompletion.limitComparison ConstantCompletion.strictLimit

private theorem constantOrdinaryUnit_projection
    {C : Type t} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type t) [CommRing A] (I : Ideal A) (b : Bool)
    (P : ConstantCompletion.Cx (ConstantCompletion.coefficients J A I b))
    (q : ℤ) (n : ℕ) :
    (ConstantCompletion.ordinaryUnit J A I b P).f q ≫
      limit.π ((ConstantCompletion.reductionComplex J A I b P).X q) (op n) =
      ((ConstantCompletion.reductionUnit J A I b).app (P.X q)).app (op n) := by
  unfold ConstantCompletion.ordinaryUnit
  exact (ConstantCompletion.ordinaryUnit_existsUnique J A I b P).exists.choose_spec q n

private theorem constantOrdinaryUnit_naturality
    {C : Type t} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type t) [CommRing A] (I : Ideal A) (b : Bool)
    {P Q : ConstantCompletion.Cx (ConstantCompletion.coefficients J A I b)} (f : P ⟶ Q) :
    f ≫ ConstantCompletion.ordinaryUnit J A I b Q =
      ConstantCompletion.ordinaryUnit J A I b P ≫
        (ConstantCompletion.ordinaryLimit (ConstantCompletion.coefficients J A I b)).map
          (((ConstantCompletion.reductionTower J A I b).mapHomologicalComplex (.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  change (f.f q ≫ (ConstantCompletion.ordinaryUnit J A I b Q).f q) ≫ limit.π _ n =
    ((ConstantCompletion.ordinaryUnit J A I b P).f q ≫
      limMap ((ConstantCompletion.reductionTower J A I b).map (f.f q))) ≫ limit.π _ n
  rw [Category.assoc, constantOrdinaryUnit_projection J A I b Q q n.unop,
    Category.assoc, limMap_π, ← Category.assoc,
    constantOrdinaryUnit_projection J A I b P q n.unop]
  exact congrArg (fun t ↦ t.app n)
    ((ConstantCompletion.reductionUnit J A I b).naturality (f.f q))

/-- The representative normalization of quotient completion holds on every complex.

Source: Stacks Tags 06YY, 099M and 0941.
(blueprint: lem-constant-completion-unit-normalization).

Proof: resolve the input by a flat-term K-flat complex. Its localization map is an
isomorphism, so cancel it. Naturality of the derived completion unit and the universal
reduction comparison reduces the equation to the stipulated K-flat normalization.
The ordinary strict-limit unit is natural because its finite projections are the
natural quotient units. This naturality and that of the universal limit comparison
identify the remaining composite with the required normalization at the input. -/
theorem constantCompletionUnit_normalization_all
    {C : Type t} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type t) [CommRing A] (I : Ideal A) (b : Bool)
    (P : ConstantCompletion.Cx (ConstantCompletion.coefficients J A I b)) :
    (ConstantCompletion.completionUnit J A I b).app
        ((ConstantCompletion.Q (ConstantCompletion.coefficients J A I b)).obj P) ≫
      (ConstantCompletion.rlim (ConstantCompletion.coefficients J A I b)).map
        ((ConstantCompletion.quotientPresentation J A I b).comparison.app P) =
      (ConstantCompletion.Q (ConstantCompletion.coefficients J A I b)).map
        (ConstantCompletion.ordinaryUnit J A I b P) ≫
        (ConstantCompletion.limitComparison (ConstantCompletion.coefficients J A I b)).app
          (ConstantCompletion.reductionComplex J A I b P) := by
  let O := ConstantCompletion.coefficients J A I b
  let Q : ConstantCompletion.Cx O ⥤ ConstantCompletion.D O := ConstantCompletion.Q O
  let L := (ConstantCompletion.quotientPresentation J A I b).tower
  let R := ConstantCompletion.rlim O
  let κ := ConstantCompletion.completionUnit J A I b
  let ε := (ConstantCompletion.quotientPresentation J A I b).comparison
  let η := ConstantCompletion.limitComparison O
  let Lc := (ConstantCompletion.reductionTower J A I b).mapHomologicalComplex (.up ℤ)
  let Rc := ConstantCompletion.ordinaryLimit O
  obtain ⟨Y, f, hY, hflat, hf, _⟩ := CochainComplex.exists_isKFlatResolution P
  have := hf
  apply (cancel_epi (Q.map f)).mp
  have hκ := κ.naturality (Q.map f)
  dsimp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map] at hκ
  change Q.map f ≫ κ.app (Q.obj P) =
    κ.app (Q.obj Y) ≫ R.map (L.map (Q.map f)) at hκ
  change (Q.map f) ≫ κ.app (Q.obj P) ≫ R.map (ε.app P) = _
  rw [← Category.assoc, hκ]
  have hε := ε.naturality f
  dsimp only [CategoryTheory.Functor.comp_map] at hε
  rw [Category.assoc, ← R.map_comp, hε, R.map_comp, ← Category.assoc]
  erw [(ConstantCompletion.quotientPresentation J A I b).laws.2.2 Y hY hflat]
  have hν := constantOrdinaryUnit_naturality J A I b f
  have hη := η.naturality (Lc.map f)
  dsimp only [CategoryTheory.Functor.comp_map] at hη
  rw [Category.assoc, ← hη, ← Q.map_comp_assoc, ← hν, Q.map_comp]
  exact Category.assoc _ _ _

end CategoryTheory.ConstantCompletion
