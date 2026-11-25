/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.Constant.ConstantSpecifiedBasis
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite bases of completed constant quotient sheaves

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59, for the inverse-limit model.
The finite-basis and cofinal-filtration refinement is the agent argument in the DAG
(blueprint: lem-pur-adic-basis-limit).

Levels of the inverse sequence are numbered by n : ℕ and have exponent n+1.
Finite products in module sheaves are the finite direct sums in the statement.
The displayed sums characterize the quotient basis maps and the completed map,
including their columns, without a choice of an unrelated isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)

/-- Ring sheafification on the small site, via Mathlib's small-model construction.
Source: def-weil-pbc-constant-sheaf (blueprint: lem-pur-adic-basis-limit). -/
instance adicBasisRingSheafify : HasSheafify J RingCat.{max uC vC r} :=
  letI : EssentiallySmall.{max uC vC r} C := essentiallySmallSelf.{r} _
  hasSheafifyEssentiallySmallSite J RingCat.{max uC vC r}

/-- The constant quotient ring sheaf at a positive exponent n+1.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
abbrev adicBasisResidue (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1)))

/-- The actual quotient tower, with reduction induced by the identity on A.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
def adicBasisTower (A : Type (max uC vC r)) [CommRing A] (t : A) :
    ℕᵒᵖ ⥤ Sheaf J RingCat.{max uC vC r} :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  let Q : ℕᵒᵖ ⥤ RingCat.{max uC vC r} :=
    { obj := fun n ↦ RingCat.of (A ⧸ (Ideal.span {t}) ^ (n.unop + 1))
      map := fun f ↦ RingCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {t})
        (Nat.succ_le_succ (leOfHom f.unop)))
      map_id := fun _ ↦ by ext x; rfl
      map_comp := fun _ _ ↦ by ext x; rfl }
  Q ⋙ constantSheaf J RingCat.{max uC vC r}

/-- The limit is Mathlib's limit of ring sheaves and is computed sectionwise.
Source: Bhatt--Scholze, Lemma 6.8.2(1); def-pur-sheaf-inverse-limit
(blueprint: lem-pur-adic-basis-limit). -/
abbrev adicBasisCompletion (A : Type (max uC vC r)) [CommRing A] (t : A) :=
  limit (adicBasisTower.{uC, vC, r} J A t)

/-- The projection at positive exponent n+1.
Source: Bhatt--Scholze, Lemma 6.8.2(1), inverse-limit model
(blueprint: lem-pur-adic-basis-limit). -/
def adicBasisProjection (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) :
    adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisResidue.{uC, vC, r} J A t n :=
  limit.π (adicBasisTower.{uC, vC, r} J A t) (op n)

/-- The residue of an element as a constant section, using the sheafification unit.
Source: DAG proof, steps 1--2 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisConstant (A : Type (max uC vC r)) [CommRing A] (t : A) (n : ℕ) (U : Cᵒᵖ)
    (a : A) : (adicBasisResidue.{uC, vC, r} J A t n).obj.obj U :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (toSheafify J ((Functor.const Cᵒᵖ).obj
    (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1))))).app U
      (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1)) a)

/-- A finite direct sum of the coefficient module, represented by its finite product.
Source: DAG proof, step 5; situation-conventions
(blueprint: lem-pur-adic-basis-limit). -/
abbrev adicBasisFree (R : Sheaf J RingCat.{max uC vC r}) (d : ℕ) :
    ringedSiteModules.{max uC vC r} R :=
  ∏ᶜ (fun _ : Fin d ↦ SheafOfModules.unit R)

/-- Coordinate projections of the finite direct sum on sections.
Source: DAG proof, step 5 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisCoordinate (R : Sheaf J RingCat.{max uC vC r}) (d : ℕ) (U : Cᵒᵖ)
    (x : (adicBasisFree.{uC, vC, r} J R d).val.obj U) (i : Fin d) : R.obj.obj U :=
  (Pi.π (fun _ : Fin d ↦ SheafOfModules.unit R) i).val.app U x

variable {A B : Type r} [CommRing A] [CommRing B] [Algebra A B]

/-- The two ideal inclusions needed for the same-level and cofinal quotient maps.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit).
Proof: t^n maps to u^n v^(en), so t^n B = v^(en) B because u^n is a unit.
Since en ≥ n, this ideal is contained in v^n B. Taking inverse images gives
both displayed inclusions at the positive exponent n+1. The subtraction in the
second exponent merely converts its positive exponent to a natural-number level. -/
theorem adicBasis_ideal_bounds (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    (Ideal.span {t}) ^ (n + 1) ≤
        ((Ideal.span {v}) ^ (n + 1)).comap (algebraMap A B) ∧
      (Ideal.span {t}) ^ (n + 1) ≤
        ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)).comap (algebraMap A B) := by
  have hmap : Ideal.map (algebraMap A B) ((Ideal.span {t}) ^ (n + 1)) =
      (Ideal.span {v}) ^ (e * (n + 1)) := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, ht,
      Ideal.span_singleton_mul_left_unit a.isUnit, ← Ideal.span_singleton_pow, pow_mul]
  have hpos : 1 ≤ e * (n + 1) := by nlinarith
  constructor
  · apply Ideal.map_le_iff_le_comap.mp
    rw [hmap]
    exact Ideal.pow_le_pow_right (by nlinarith)
  · apply Ideal.map_le_iff_le_comap.mp
    rw [hmap, Nat.sub_add_cancel hpos]

private def adicQuotientBasis (d : ℕ) (b : Module.Basis (Fin d) A B) (I : Ideal A) :
    Module.Basis (Fin d) (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
  (b.baseChange (A ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv

private theorem adicQuotientBasis_exists (d : ℕ) (b : Module.Basis (Fin d) A B)
    (I : Ideal A) (K : Ideal B) (hK : K = I.map (algebraMap A B))
    (h : I ≤ K.comap (algebraMap A B)) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap h
    ∃ c : Module.Basis (Fin d) (A ⧸ I) (B ⧸ K),
      ∀ i : Fin d, c i = Ideal.Quotient.mk K (b i) := by
  subst K
  refine ⟨adicQuotientBasis d b I, ?_⟩
  intro i
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  simp [adicQuotientBasis]

private theorem adicBasisCofinal_basis (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap
      (adicBasis_ideal_bounds t v a e he ht n).2
    ∃ c : Module.Basis (Fin d) (A ⧸ (Ideal.span {t}) ^ (n + 1))
        (B ⧸ (Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)),
      ∀ i : Fin d, c i =
        Ideal.Quotient.mk ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)) (b i) := by
  apply adicQuotientBasis_exists d b
  have hpos : 1 ≤ e * (n + 1) := by nlinarith
  rw [Nat.sub_add_cancel hpos, Ideal.map_pow, Ideal.map_span, Set.image_singleton, ht,
    Ideal.span_singleton_mul_left_unit a.isUnit, ← Ideal.span_singleton_pow, pow_mul]

variable {A B : Type (max uC vC r)} [CommRing A] [CommRing B] [Algebra A B]

/-- The canonical quotient map A/t^(n+1) -> B/v^(n+1).
Its underlying ring map is induced by the given algebra map.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisScalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    adicBasisResidue.{uC, vC, r} J A t n ⟶ adicBasisResidue.{uC, vC, r} J B v n :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom
    (Ideal.quotientMap ((Ideal.span {v}) ^ (n + 1)) (algebraMap A B)
      (adicBasis_ideal_bounds.{max uC vC r} t v a e he ht n).1))

/-- The quotient map at exponents n+1 and e(n+1), using t^(n+1)B=v^(e(n+1))B.
Natural-number level e(n+1)-1 denotes positive exponent e(n+1).
Source: DAG proof, steps 3--4 (blueprint: lem-pur-adic-basis-limit). -/
def adicBasisCofinalScalar (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    adicBasisResidue.{uC, vC, r} J A t n ⟶ adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1) :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  (constantSheaf J RingCat.{max uC vC r}).map (RingCat.ofHom
    (Ideal.quotientMap ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)) (algebraMap A B)
      (adicBasis_ideal_bounds.{max uC vC r} t v a e he ht n).2))

/-- The normalization characterizing the ring map of completions.
Source: DAG proof, step 3 (blueprint: lem-pur-adic-basis-limit). -/
def AdicBasisScalarCondition (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v) : Prop :=
  ∀ n : ℕ, f ≫ adicBasisProjection.{uC, vC, r} J B v n =
    adicBasisProjection.{uC, vC, r} J A t n ≫ adicBasisScalar.{uC, vC, r} J t v a e he ht n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def adicBasisFreeEquiv (R : Sheaf J RingCat.{max uC vC r}) (d : ℕ) (U : Cᵒᵖ) :
    (adicBasisFree.{uC, vC, r} J R d).val.obj U ≃ (Fin d → R.obj.obj U) :=
  let E := SheafOfModules.evaluation.{max uC vC r} R U
  (asIso (piComparison E (fun _ : Fin d ↦ SheafOfModules.unit R)) ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv.toEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicBasisFreeEquiv_apply (R : Sheaf J RingCat.{max uC vC r})
    (d : ℕ) (U : Cᵒᵖ) (x : (adicBasisFree.{uC, vC, r} J R d).val.obj U) (i : Fin d) :
    adicBasisFreeEquiv.{uC, vC, r} J R d U x i =
      adicBasisCoordinate.{uC, vC, r} J R d U x i := by
  change ((piComparison (SheafOfModules.evaluation.{max uC vC r} R U) _ ≫
    (ModuleCat.piIsoPi _).hom ≫ ModuleCat.ofHom (LinearMap.proj i)) x) = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype, piComparison_comp_π]
  rfl

private theorem adicBasisTower_map (t : A) (i j : ℕ) (h : i ≤ j) :
    letI := adicBasisRingSheafify.{uC, vC, r} J
    (adicBasisTower.{uC, vC, r} J A t).map (homOfLE h).op =
      (constantSheaf J RingCat.{max uC vC r}).map
        (RingCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {t})
          (Nat.succ_le_succ h))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicBasisCofinal_iso (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) :
    ∃ β : adicBasisFree.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d ≅
        (SheafOfModules.restrictScalars
          (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n)).obj
            (SheafOfModules.unit (adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1))),
      ∀ (U : Cᵒᵖ)
        (y : (adicBasisFree.{uC, vC, r} J
          (adicBasisResidue.{uC, vC, r} J A t n) d).val.obj U),
        β.hom.val.app U y = ∑ i : Fin d,
          (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U
            (adicBasisCoordinate.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d U y i) *
            adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i) := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  let : EssentiallySmall.{max uC vC r} C := essentiallySmallSelf.{r} _
  let : HasSheafify J AddCommGrpCat.{max uC vC r} :=
    hasSheafifyEssentiallySmallSite J AddCommGrpCat.{max uC vC r}
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vC, max uC vC r,
      uC, (max uC vC r) + 1, max uC vC r, max uC vC r, max uC vC r} _
  let := Ideal.Quotient.algebraQuotientOfLEComap
    (adicBasis_ideal_bounds t v a e he ht n).2
  obtain ⟨c, hc⟩ := adicBasisCofinal_basis.{max uC vC r} d b t v a e he ht n
  obtain ⟨β, hβ⟩ := constantSheaf_specifiedBasis.{uC, vC, r} J
    (A ⧸ (Ideal.span {t}) ^ (n + 1))
    (B ⧸ (Ideal.span {v}) ^ (e * (n + 1) - 1 + 1)) d c
      (Ideal.quotientMap ((Ideal.span {v}) ^ (e * (n + 1) - 1 + 1))
        (algebraMap A B) (adicBasis_ideal_bounds t v a e he ht n).2) rfl
  refine ⟨β, ?_⟩
  intro U y
  simpa only [hc, adicBasisCoordinate, adicBasisConstant, adicBasisCofinalScalar,
    adicBasisResidue] using hβ U y

private def adicBasisQuotientSum (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) (U : Cᵒᵖ)
    (y : Fin d → (adicBasisResidue.{uC, vC, r} J A t n).obj.obj U) :
    (adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1)).obj.obj U :=
  ∑ i : Fin d, (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U (y i) *
    adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicBasisQuotientSum_bijective (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) (n : ℕ) (U : Cᵒᵖ) :
    Function.Bijective (adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U) := by
  obtain ⟨β, hβ⟩ := adicBasisCofinal_iso.{uC, vC, r} J d b t v a e he ht n
  let E := SheafOfModules.evaluation.{max uC vC r}
    (adicBasisResidue.{uC, vC, r} J A t n) U
  let h := (adicBasisFreeEquiv.{uC, vC, r} J
    (adicBasisResidue.{uC, vC, r} J A t n) d U).symm.trans
      (E.mapIso β).toLinearEquiv.toEquiv
  have hh : adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U = h := by
    funext y
    change _ = β.hom.val.app U _
    rw [hβ]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    rw [← adicBasisFreeEquiv_apply]
    exact (congrFun ((adicBasisFreeEquiv.{uC, vC, r} J
      (adicBasisResidue.{uC, vC, r} J A t n) d U).apply_symm_apply y) i).symm
  rw [hh]
  exact h.bijective

private def adicBasisScalarTower (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) :
    adicBasisTower.{uC, vC, r} J A t ⟶ adicBasisTower.{uC, vC, r} J B v :=
  NatTrans.ofOpSequence (fun n ↦ adicBasisScalar.{uC, vC, r} J t v a e he ht n) (by
    intro n
    dsimp only [adicBasisTower, Functor.comp_map]
    dsimp only [adicBasisScalar]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext x
    rfl)

private theorem adicBasisScalar_exists_unique (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e) :
    ∃ f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v,
      AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f ∧
      ∀ g, AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht g → g = f := by
  let f := limMap (adicBasisScalarTower.{uC, vC, r} J t v a e he ht)
  have hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f := by
    intro n
    exact limMap_π (adicBasisScalarTower.{uC, vC, r} J t v a e he ht) (op n)
  refine ⟨f, hf, ?_⟩
  intro g hg
  apply limit.hom_ext
  intro n
  exact (hg n.unop).trans (hf n.unop).symm

private theorem adicBasisScalar_cofinal (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) (n : ℕ) :
    f ≫ adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1) =
      adicBasisProjection.{uC, vC, r} J A t n ≫
        adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  have hn : n ≤ e * (n + 1) - 1 := by
    have hp : n + 1 ≤ e * (n + 1) := by nlinarith
    omega
  have hq : (adicBasisTower.{uC, vC, r} J A t).map (homOfLE hn).op ≫
      adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n =
        adicBasisScalar.{uC, vC, r} J t v a e he ht (e * (n + 1) - 1) := by
    rw [adicBasisTower_map]
    dsimp only [adicBasisCofinalScalar, adicBasisScalar]
    rw [← Functor.map_comp]
    congr 1
    ext x
    rfl
  rw [hf, ← hq]
  exact limit.w_assoc _ (homOfLE hn).op _

private theorem adicBasisCofinal_naturality (t : A) (v : B) (a : Bˣ) (e : ℕ)
    (he : 1 ≤ e) (ht : algebraMap A B t = (a : B) * v ^ e)
    (i j : ℕ) (h : i ≤ j) :
    (adicBasisTower.{uC, vC, r} J A t).map (homOfLE h).op ≫
        adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht i =
      adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht j ≫
        (adicBasisTower.{uC, vC, r} J B v).map
          (homOfLE (Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.succ_le_succ h)) 1)).op := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  rw [adicBasisTower_map, adicBasisTower_map]
  dsimp only [adicBasisCofinalScalar]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  rfl

private def adicBasisFromConstant (t : A) :
    letI := adicBasisRingSheafify.{uC, vC, r} J
    (constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A) ⟶
      adicBasisCompletion.{uC, vC, r} J A t :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  limit.lift _
    { pt := (constantSheaf J RingCat.{max uC vC r}).obj (RingCat.of A)
      π := NatTrans.ofOpSequence (G := adicBasisTower.{uC, vC, r} J A t)
        (fun n ↦ (constantSheaf J RingCat.{max uC vC r}).map
          (RingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1))))) (by
          intro n
          simp only [Functor.const_obj_map]
          dsimp only [adicBasisTower, Functor.comp_map]
          rw [← Functor.map_comp]
          congr 1) }

private theorem adicBasisFromConstant_projection (t : A) (n : ℕ) :
    letI := adicBasisRingSheafify.{uC, vC, r} J
    adicBasisFromConstant.{uC, vC, r} J t ≫ adicBasisProjection.{uC, vC, r} J A t n =
      (constantSheaf J RingCat.{max uC vC r}).map
        (RingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1)))) :=
  limit.lift_π _ (op n)

private theorem adicBasisCompletion_ext (t : A) (U : Cᵒᵖ)
    (x y : (adicBasisCompletion.{uC, vC, r} J A t).obj.obj U)
    (h : ∀ n : ℕ, (adicBasisProjection.{uC, vC, r} J A t n).hom.app U x =
      (adicBasisProjection.{uC, vC, r} J A t n).hom.app U y) : x = y := by
  let E := sheafToPresheaf J RingCat.{max uC vC r} ⋙
    (evaluation Cᵒᵖ RingCat.{max uC vC r}).obj U
  exact Concrete.isLimit_ext _ (isLimitOfPreserves E (limit.isLimit
    (adicBasisTower.{uC, vC, r} J A t))) x y (fun n ↦ h n.unop)

private def adicBasisCompletedUnit (t : A) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      (adicBasisCompletion.{uC, vC, r} J A t).obj :=
  letI := adicBasisRingSheafify.{uC, vC, r} J
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A)) ≫
    (adicBasisFromConstant.{uC, vC, r} J t).hom

private theorem adicBasisCompletedUnit_projection (t : A) (n : ℕ) :
    letI := adicBasisRingSheafify.{uC, vC, r} J
    adicBasisCompletedUnit.{uC, vC, r} J t ≫
        (adicBasisProjection.{uC, vC, r} J A t n).hom =
      (Functor.const Cᵒᵖ).map
        (RingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1)))) ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj
            (RingCat.of (A ⧸ (Ideal.span {t}) ^ (n + 1)))) := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  change toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A)) ≫
    (adicBasisFromConstant.{uC, vC, r} J t ≫
      adicBasisProjection.{uC, vC, r} J A t n).hom = _
  rw [adicBasisFromConstant_projection]
  exact (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
    (RingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {t}) ^ (n + 1)))))).symm

private def adicBasisColumn (t : A) (v : B)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (c : B) : SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J A t) ⟶
      (SheafOfModules.restrictScalars f).obj
        (SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J B v)) :=
  ((SheafOfModules.restrictScalars f).obj
    (SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J B v))).unitHomEquiv.symm
      ⟨fun U ↦ (adicBasisCompletedUnit.{uC, vC, r} J v).app U c,
        fun {_ _} k ↦ (ConcreteCategory.congr_hom
          ((adicBasisCompletedUnit.{uC, vC, r} J v).naturality k) c).symm⟩

omit [Algebra A B] in
private theorem adicBasisColumn_apply (t : A) (v : B)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (c : B) (U : Cᵒᵖ) (x : (adicBasisCompletion.{uC, vC, r} J A t).obj.obj U) :
    (adicBasisColumn.{uC, vC, r} J t v f c).val.app U x =
      f.hom.app U x * (adicBasisCompletedUnit.{uC, vC, r} J v).app U c := rfl

private def adicBasisForward (d : ℕ) (b : Module.Basis (Fin d) A B) (t : A) (v : B)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v) :
    adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d ⟶
      (SheafOfModules.restrictScalars f).obj
        (SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J B v)) :=
  ∑ i : Fin d, Pi.π _ i ≫ adicBasisColumn.{uC, vC, r} J t v f (b i)

private theorem adicBasisForward_apply (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (U : Cᵒᵖ)
    (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U) :
    (adicBasisForward.{uC, vC, r} J d b t v f).val.app U x = ∑ i : Fin d,
      f.hom.app U (adicBasisCoordinate.{uC, vC, r} J
        (adicBasisCompletion.{uC, vC, r} J A t) d U x i) *
          (adicBasisCompletedUnit.{uC, vC, r} J v).app U (b i) := by
  let E := SheafOfModules.evaluation.{max uC vC r}
    (adicBasisCompletion.{uC, vC, r} J A t) U
  let : E.Additive := inferInstanceAs
    (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).Additive
  change (E.map (∑ i : Fin d, Pi.π
    (fun _ : Fin d ↦ SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J A t)) i ≫
      adicBasisColumn.{uC, vC, r} J t v f (b i))) x = _
  rw [Functor.map_sum]
  change (∑ i : Fin d, (E.map (Pi.π
    (fun _ : Fin d ↦ SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J A t)) i ≫
      adicBasisColumn.{uC, vC, r} J t v f (b i)))).hom x = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact adicBasisColumn_apply.{uC, vC, r} J t v f (b i) U _

private theorem adicBasisForward_projection (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f)
    (n : ℕ) (U : Cᵒᵖ)
    (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U) :
    (adicBasisProjection.{uC, vC, r} J B v n).hom.app U
        ((adicBasisForward.{uC, vC, r} J d b t v f).val.app U x) =
      ∑ i : Fin d,
        (adicBasisScalar.{uC, vC, r} J t v a e he ht n).hom.app U
          ((adicBasisProjection.{uC, vC, r} J A t n).hom.app U
            (adicBasisCoordinate.{uC, vC, r} J
              (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) *
          adicBasisConstant.{uC, vC, r} J B v n U (b i) := by
  rw [adicBasisForward_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  have hs := congrArg (fun h ↦ h.hom.app U
    (adicBasisCoordinate.{uC, vC, r} J
      (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) (hf n)
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (adicBasisCompletedUnit_projection.{uC, vC, r} J v n) U) (b i)
  exact congrArg₂ (· * ·) hs hc

private theorem adicBasisForward_cofinal (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f)
    (n : ℕ) (U : Cᵒᵖ)
    (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U) :
    (adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1)).hom.app U
        ((adicBasisForward.{uC, vC, r} J d b t v f).val.app U x) =
      adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U
        (fun i ↦ (adicBasisProjection.{uC, vC, r} J A t n).hom.app U
          (adicBasisCoordinate.{uC, vC, r} J
            (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) := by
  rw [adicBasisForward_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  have hs := congrArg (fun h ↦ h.hom.app U
    (adicBasisCoordinate.{uC, vC, r} J
      (adicBasisCompletion.{uC, vC, r} J A t) d U x i))
        (adicBasisScalar_cofinal.{uC, vC, r} J t v a e he ht f hf n)
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (adicBasisCompletedUnit_projection.{uC, vC, r} J v (e * (n + 1) - 1)) U) (b i)
  exact congrArg₂ (· * ·) hs hc

omit [Algebra A B] in
private theorem adicBasisConstant_map (t : A) (i j : ℕ) (h : i ≤ j) (U : Cᵒᵖ) (c : A) :
    ((adicBasisTower.{uC, vC, r} J A t).map (homOfLE h).op).hom.app U
        (adicBasisConstant.{uC, vC, r} J A t j U c) =
      adicBasisConstant.{uC, vC, r} J A t i U c := by
  have hj := ConcreteCategory.congr_hom (NatTrans.congr_app
    (adicBasisCompletedUnit_projection.{uC, vC, r} J t j) U) c
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app
    (adicBasisCompletedUnit_projection.{uC, vC, r} J t i) U) c
  change (adicBasisProjection.{uC, vC, r} J A t j).hom.app U
    ((adicBasisCompletedUnit.{uC, vC, r} J t).app U c) =
      adicBasisConstant.{uC, vC, r} J A t j U c at hj
  change (adicBasisProjection.{uC, vC, r} J A t i).hom.app U
    ((adicBasisCompletedUnit.{uC, vC, r} J t).app U c) =
      adicBasisConstant.{uC, vC, r} J A t i U c at hi
  rw [← hj, ← hi]
  exact congrArg (fun q ↦ q.hom.app U
    ((adicBasisCompletedUnit.{uC, vC, r} J t).app U c))
      (limit.w (adicBasisTower.{uC, vC, r} J A t) (homOfLE h).op)

private theorem adicBasisQuotientSum_naturality (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) (i j : ℕ) (h : i ≤ j) (U : Cᵒᵖ)
    (y : Fin d → (adicBasisResidue.{uC, vC, r} J A t j).obj.obj U) :
    ((adicBasisTower.{uC, vC, r} J B v).map
        (homOfLE (Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.succ_le_succ h)) 1)).op
      ).hom.app U (adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht j U y) =
      adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht i U
        (fun k ↦ ((adicBasisTower.{uC, vC, r} J A t).map (homOfLE h).op).hom.app U (y k)) := by
  dsimp only [adicBasisQuotientSum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, adicBasisConstant_map]
  congr 1
  exact (congrArg (fun q ↦ q.hom.app U (y k))
    (adicBasisCofinal_naturality.{uC, vC, r} J t v a e he ht i j h)).symm

omit [Algebra A B] in
private theorem adicBasisCompletion_cofinal_ext (t : A) (e : ℕ) (he : 1 ≤ e) (U : Cᵒᵖ)
    (x y : (adicBasisCompletion.{uC, vC, r} J A t).obj.obj U)
    (h : ∀ n : ℕ,
      (adicBasisProjection.{uC, vC, r} J A t (e * (n + 1) - 1)).hom.app U x =
        (adicBasisProjection.{uC, vC, r} J A t (e * (n + 1) - 1)).hom.app U y) : x = y := by
  apply adicBasisCompletion_ext.{uC, vC, r} J t U x y
  intro n
  have hn : n ≤ e * (n + 1) - 1 := by
    have hp : n + 1 ≤ e * (n + 1) := by nlinarith
    omega
  have hw (z : (adicBasisCompletion.{uC, vC, r} J A t).obj.obj U) :=
    congrArg (fun q ↦ q.hom.app U z)
      (limit.w (adicBasisTower.{uC, vC, r} J A t) (homOfLE hn).op)
  exact (hw x).symm.trans ((congrArg
    (((adicBasisTower.{uC, vC, r} J A t).map (homOfLE hn).op).hom.app U) (h n)).trans (hw y))

private theorem adicBasisForward_injective (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) (U : Cᵒᵖ) :
    Function.Injective ((adicBasisForward.{uC, vC, r} J d b t v f).val.app U) := by
  intro x y h
  apply (adicBasisFreeEquiv.{uC, vC, r} J
    (adicBasisCompletion.{uC, vC, r} J A t) d U).injective
  funext i
  rw [adicBasisFreeEquiv_apply, adicBasisFreeEquiv_apply]
  apply adicBasisCompletion_ext.{uC, vC, r} J t U
  intro n
  have hs := congrArg ((adicBasisProjection.{uC, vC, r} J B v
    (e * (n + 1) - 1)).hom.app U) h
  rw [adicBasisForward_cofinal.{uC, vC, r} J d b t v a e he ht f hf,
    adicBasisForward_cofinal.{uC, vC, r} J d b t v a e he ht f hf] at hs
  exact congrFun ((adicBasisQuotientSum_bijective.{uC, vC, r} J d b t v a e he ht n U).1 hs) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicBasisForward_surjective (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) (U : Cᵒᵖ) :
    Function.Surjective ((adicBasisForward.{uC, vC, r} J d b t v f).val.app U) := by
  let := adicBasisRingSheafify.{uC, vC, r} J
  intro s
  let Q (n : ℕ) := Equiv.ofBijective
    (adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U)
    (adicBasisQuotientSum_bijective.{uC, vC, r} J d b t v a e he ht n U)
  let c (n : ℕ) := (Q n).symm
    ((adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1)).hom.app U s)
  have hcq (n : ℕ) : adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U (c n) =
      (adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1)).hom.app U s :=
    (Q n).apply_symm_apply _
  have hc (n : ℕ) :
      (fun i ↦ ((adicBasisTower.{uC, vC, r} J A t).map
        (homOfLE (Nat.le_succ n)).op).hom.app U (c (n + 1) i)) = c n := by
    apply (Q n).injective
    change adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U _ =
      adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U (c n)
    rw [← adicBasisQuotientSum_naturality.{uC, vC, r} J d b t v a e he ht n (n + 1)
      (Nat.le_succ n), hcq, hcq]
    exact congrArg (fun q ↦ q.hom.app U s)
      (limit.w (adicBasisTower.{uC, vC, r} J B v)
        (homOfLE (Nat.sub_le_sub_right
          (Nat.mul_le_mul_left e (Nat.succ_le_succ (Nat.le_succ n))) 1)).op)
  let E := sheafToPresheaf J RingCat.{max uC vC r} ⋙
    (evaluation Cᵒᵖ RingCat.{max uC vC r}).obj U ⋙ forget RingCat.{max uC vC r}
  let F := adicBasisTower.{uC, vC, r} J A t ⋙ E
  let hL := isLimitOfPreserves E (limit.isLimit (adicBasisTower.{uC, vC, r} J A t))
  let D (i : Fin d) : Cone F :=
    { pt := PUnit.{(max uC vC r) + 1}
      π := NatTrans.ofOpSequence (G := F) (fun n ↦ ↾fun _ ↦ c n i) (by
        intro n
        ext z
        exact (congrFun (hc n) i).symm) }
  let r (i : Fin d) : (adicBasisCompletion.{uC, vC, r} J A t).obj.obj U :=
    hL.lift (D i) PUnit.unit
  have hr (i : Fin d) (n : ℕ) :
      (adicBasisProjection.{uC, vC, r} J A t n).hom.app U (r i) = c n i :=
    ConcreteCategory.congr_hom (hL.fac (D i) (op n)) PUnit.unit
  let x := (adicBasisFreeEquiv.{uC, vC, r} J
    (adicBasisCompletion.{uC, vC, r} J A t) d U).symm r
  have hx (i : Fin d) : adicBasisCoordinate.{uC, vC, r} J
      (adicBasisCompletion.{uC, vC, r} J A t) d U x i = r i := by
    rw [← adicBasisFreeEquiv_apply]
    exact congrFun ((adicBasisFreeEquiv.{uC, vC, r} J
      (adicBasisCompletion.{uC, vC, r} J A t) d U).apply_symm_apply r) i
  refine ⟨x, ?_⟩
  apply adicBasisCompletion_cofinal_ext.{uC, vC, r} J v e he U
  intro n
  rw [adicBasisForward_cofinal.{uC, vC, r} J d b t v a e he ht f hf]
  calc
    _ = adicBasisQuotientSum.{uC, vC, r} J d b t v a e he ht n U (c n) := by
      congr 1
      funext i
      rw [hx, hr]
    _ = _ := hcq n

private theorem adicBasisForward_isIso (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v)
    (hf : AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f) :
    IsIso (adicBasisForward.{uC, vC, r} J d b t v f) := by
  let G := SheafOfModules.toSheaf.{max uC vC r}
    (adicBasisCompletion.{uC, vC, r} J A t) ⋙ sheafToPresheaf J AddCommGrpCat.{max uC vC r}
  have (U : Cᵒᵖ) : IsIso ((G.map (adicBasisForward.{uC, vC, r} J d b t v f)).app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ⟨adicBasisForward_injective.{uC, vC, r} J d b t v a e he ht f hf U,
      adicBasisForward_surjective.{uC, vC, r} J d b t v a e he ht f hf U⟩
  have := NatIso.isIso_of_isIso_app (G.map (adicBasisForward.{uC, vC, r} J d b t v f))
  exact isIso_of_reflects_iso _ G

/-- Finite bases pass to completed constant quotient sheaves, with their specified
columns and their cofinal projection factorization.

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59, for the inverse-limit model;
finite-basis/cofinal-filtration refinement: DAG agent argument
(blueprint: lem-pur-adic-basis-limit).

Proof: (1) The basis map A^d -> B descends modulo t^n, with inverse given by
reducing the coordinate maps. Both commute with reductions, including d=0.
(2) Constant presheaves and sheafification carry these maps to quotient basis
isomorphisms, since sheafification preserves finite products
(situation-conventions). The module-sheafification universal property
(lem-pc-sites-module-sheafification-interface) and its underlying-set comparison
(lem-pc-sites-sheafification-underlying-sets) identify the target with the ring sheaf.
(3) The ideal identities t^n B=v^(en)B and inclusions t^m B ⊆ v^m B give
compatible quotient ring maps. Their sectionwise limit is f; its coordinates give
uniqueness. (4) Restriction to exponents en identifies the two B-towers cofinally:
the inverse reduces the em-th component to exponent m. The two composites are
identities by tower compatibility. (5) Passing the compatible quotient basis
isomorphisms and their coordinate inverses to sectionwise limits gives Φ.
Finite sums of coordinate inclusions identify the finite product with the direct
sum. (6) At cofinal exponent en the scalar action factors through A/t^n, so Φ
is R-linear. Its columns have residues b_i at every level, and its en-th
projection is precisely the quotient basis map after coordinatewise projection.
-/
theorem adic_basis_limit (d : ℕ) (b : Module.Basis (Fin d) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e) :
    ∃ f : adicBasisCompletion.{uC, vC, r} J A t ⟶ adicBasisCompletion.{uC, vC, r} J B v,
      AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht f ∧
      (∀ g, AdicBasisScalarCondition.{uC, vC, r} J t v a e he ht g → g = f) ∧
      ∃ Φ : adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d ≅
          (SheafOfModules.restrictScalars f).obj
            (SheafOfModules.unit (adicBasisCompletion.{uC, vC, r} J B v)),
        (∀ (n : ℕ) (U : Cᵒᵖ)
          (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U),
          (adicBasisProjection.{uC, vC, r} J B v n).hom.app U (Φ.hom.val.app U x) =
            ∑ i : Fin d,
              (adicBasisScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                ((adicBasisProjection.{uC, vC, r} J A t n).hom.app U
                  (adicBasisCoordinate.{uC, vC, r} J
                    (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) *
                adicBasisConstant.{uC, vC, r} J B v n U (b i)) ∧
        (∀ n : ℕ, ∃ β : adicBasisFree.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d ≅
            (SheafOfModules.restrictScalars
              (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n)).obj
                (SheafOfModules.unit (adicBasisResidue.{uC, vC, r} J B v (e * (n + 1) - 1))),
          (∀ (U : Cᵒᵖ)
            (y : (adicBasisFree.{uC, vC, r} J
              (adicBasisResidue.{uC, vC, r} J A t n) d).val.obj U),
            β.hom.val.app U y = ∑ i : Fin d,
              (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                (adicBasisCoordinate.{uC, vC, r} J (adicBasisResidue.{uC, vC, r} J A t n) d U y i) *
                adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i)) ∧
          (∀ (U : Cᵒᵖ)
            (x : (adicBasisFree.{uC, vC, r} J (adicBasisCompletion.{uC, vC, r} J A t) d).val.obj U),
            (adicBasisProjection.{uC, vC, r} J B v (e * (n + 1) - 1)).hom.app U
                (Φ.hom.val.app U x) =
              ∑ i : Fin d,
                (adicBasisCofinalScalar.{uC, vC, r} J t v a e he ht n).hom.app U
                  ((adicBasisProjection.{uC, vC, r} J A t n).hom.app U
                    (adicBasisCoordinate.{uC, vC, r} J
                    (adicBasisCompletion.{uC, vC, r} J A t) d U x i)) *
                  adicBasisConstant.{uC, vC, r} J B v (e * (n + 1) - 1) U (b i))) := by
  obtain ⟨f, hf, huniq⟩ := adicBasisScalar_exists_unique.{uC, vC, r} J t v a e he ht
  let := adicBasisForward_isIso.{uC, vC, r} J d b t v a e he ht f hf
  refine ⟨f, hf, huniq, asIso (adicBasisForward.{uC, vC, r} J d b t v f), ?_, ?_⟩
  · exact adicBasisForward_projection.{uC, vC, r} J d b t v a e he ht f hf
  · intro n
    obtain ⟨β, hβ⟩ := adicBasisCofinal_iso.{uC, vC, r} J d b t v a e he ht n
    exact ⟨β, hβ, adicBasisForward_cofinal.{uC, vC, r} J d b t v a e he ht f hf n⟩

end CategoryTheory
