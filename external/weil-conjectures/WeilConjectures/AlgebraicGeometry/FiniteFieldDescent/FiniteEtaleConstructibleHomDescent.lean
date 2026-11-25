/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.AlgebraicGeometry.FiniteFieldDescent.FiniteEtaleConstructibleObjectDescent
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Finite-stage descent and Hom continuity for constructible finite-coefficient complexes

Source: `literature/stacks-project/etale-cohomology.tex`, Lemma 09YU (3),
constructible sheaves over inverse limits with affine transition maps; bounded finite-Tor
complexes are obtained by finite flat resolutions and descent of morphisms.
(blueprint: lem-sfb-finite-etale-constructible-hom-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The canonical compositor for two successive field-stage pullbacks.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def pullCompIso {A B C : Type u} [Field A] [Field B] [Field C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (Λ : Type (u + 1)) [CommRing Λ] (h : A →ₐ[K] B) (i : B →ₐ[K] C) :
    pull f Λ (i.comp h) ≅ pull f Λ h ⋙ pull f Λ i :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (projection f i) (projection f h)
    (projection f (i.comp h)) (by
      apply pullback.hom_ext
      · simp [projection, Category.assoc]
      · simp [projection, Category.assoc, ← Spec.map_comp]
        congr 1)

/-- The canonical compositor from a finite intermediate stage to `L`.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def pullValCompIso {L : Type u} [Field L] [Algebra K L]
    {E E' : IntermediateField K L} (hEE' : E ≤ E')
    (Λ : Type (u + 1)) [CommRing Λ] :
    pull f Λ (IntermediateField.val E) ≅
      pull f Λ (IntermediateField.inclusion hEE') ⋙
        pull f Λ (IntermediateField.val E') :=
  (eqToIso (congrArg (fun j : E →ₐ[K] L => pull f Λ j)
    (by ext x; rfl))).trans
    (pullCompIso f Λ (IntermediateField.inclusion hEE')
      (IntermediateField.val E'))

/-- Finite intermediate stages above a fixed finite stage.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
def finiteStageIndex {L : Type u} [Field L] [Algebra K L]
    (E₀ : IntermediateField K L) :=
  {E : IntermediateField K L // E₀ ≤ E ∧ FiniteDimensional K E}

instance finiteStageIndexSemilatticeSup {L : Type u} [Field L] [Algebra K L]
    (E₀ : IntermediateField K L) : SemilatticeSup (finiteStageIndex E₀) :=
  Subtype.semilatticeSup (fun _ _ hx hy ↦ by
    let _ := hx.2
    let _ := hy.2
    exact ⟨hx.1.trans le_sup_left, inferInstance⟩)

/-- The canonical transition on finite-stage Hom sets.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def finiteStageHomTransition {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E E' : finiteStageIndex E₀} (h : E ≤ E')
    (u : (pull f Λ (A := E₀) (B := E.1) (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (A := E₀) (B := E.1) (IntermediateField.inclusion E.property.1)).obj Q₀) :
    (pull f Λ (A := E₀) (B := E'.1) (IntermediateField.inclusion E'.property.1)).obj P₀ ⟶
      (pull f Λ (A := E₀) (B := E'.1) (IntermediateField.inclusion E'.property.1)).obj Q₀ := by
  let h₀E' : E₀ ≤ E'.1 := E'.property.1
  let hEE' : E.1 ≤ E'.1 := h
  let compIso :=
    (eqToIso (congrArg (fun j : E₀ →ₐ[K] E'.1 => pull f Λ (A := E₀) (B := E'.1) j)
      (show IntermediateField.inclusion h₀E' =
          (IntermediateField.inclusion hEE').comp
            (IntermediateField.inclusion E.property.1) by
        ext x
        rfl))).trans
      (pullCompIso f Λ (IntermediateField.inclusion E.property.1)
        (IntermediateField.inclusion hEE'))
  exact compIso.hom.app P₀ ≫
      (pull f Λ (A := E.1) (B := E'.1) (IntermediateField.inclusion hEE')).map u ≫
    compIso.inv.app Q₀

/-- The canonical leg from a finite-stage Hom set to the limiting Hom set.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def finiteStageHomLeg {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E : finiteStageIndex E₀}
    (u : (pull f Λ (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E.property.1)).obj Q₀) :
    (pull f Λ (IntermediateField.val E₀)).obj P₀ ⟶
      (pull f Λ (IntermediateField.val E₀)).obj Q₀ :=
  (pullValCompIso f E.property.1 Λ).hom.app P₀ ≫
      (pull f Λ (IntermediateField.val E.1)).map u ≫
    (pullValCompIso f E.property.1 Λ).inv.app Q₀

/-- A concrete pullback Hom cocone over all finite stages above `E₀`.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
structure FiniteStageHomSystem {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    (P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)) where
  F : finiteStageIndex E₀ ⥤ Type (u + 1)
  objEquiv : ∀ E, F.obj E ≃
    ((pull f Λ (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E.property.1)).obj Q₀)
  map_eq : ∀ {E E'} (h : E ⟶ E') (x : F.obj E),
    objEquiv E' (F.map h x) =
      finiteStageHomTransition f Λ (leOfHom h) (objEquiv E x)
  c : Cocone F
  vertexEquiv : c.pt ≃
    ((pull f Λ (IntermediateField.val E₀)).obj P₀ ⟶
      (pull f Λ (IntermediateField.val E₀)).obj Q₀)
  leg_eq : ∀ (E) (x : F.obj E),
    vertexEquiv (c.ι.app E x) = finiteStageHomLeg f Λ (objEquiv E x)

end AlgebraicGeometry.Etale.FiniteFieldDescent

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

private theorem finiteStageHomLeg_map {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ] {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    (E : finiteStageIndex E₀) (u : P₀ ⟶ Q₀) :
    finiteStageHomLeg f Λ (E := E)
        ((pull f Λ (IntermediateField.inclusion E.property.1)).map u) =
      (pull f Λ (IntermediateField.val E₀)).map u := by
  unfold finiteStageHomLeg
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]
  simp

private theorem finiteStageHomTransition_map {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ] {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E E' : finiteStageIndex E₀} (h : E ≤ E') (u : P₀ ⟶ Q₀) :
    finiteStageHomTransition f Λ h
        ((pull f Λ (IntermediateField.inclusion E.property.1)).map u) =
      (pull f Λ (IntermediateField.inclusion E'.property.1)).map u := by
  unfold finiteStageHomTransition
  dsimp only
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]
  simp

/-- The canonical finite-stage Hom system is colimiting.

Source: Stacks Lemma 09YU (3), with derived internal-Hom comparison and cohomology
continuity (blueprint: lem-sfb-finite-etale-constructible-hom-descent).

Proof: the finite intermediate fields above E₀ form a directed nonempty system and
present Y_L as an affine inverse limit of qcqs schemes. Express Hom as degree-zero
cohomology of derived global sections of RHom(P₀,Q₀). Its source is bounded below:
P₀ is bounded above and Q₀ bounded below. The affine ind-etale comparison identifies
its pullback with RHom at each stage and at L, naturally in P₀ and Q₀. Derived etale
cohomology continuity therefore makes the resulting H⁰ cocone colimiting. Transport
from H⁰ to Hom using the evaluation adjunction; its naturality fixes the maps to be
finiteStageHomTransition and finiteStageHomLeg. These canonical maps satisfy identity,
composition and cocone naturality by coherence of leftDerivedUpperStarComp. Define F
on the actual Hom sets, choose identity object and vertex equivalences, and apply the
transported colimit universal property. The construction includes zero objects, the
empty scheme and L = K. -/
theorem finiteEtaleConstructibleHomContinuity
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [Algebra.IsSeparable K L] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (E₀ : IntermediateField K L) (hE₀ : FiniteDimensional K E₀)
    (P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀))
    (hP₀ : ctf f Λ P₀) (hQ₀ : ctf f Λ Q₀) :
    ∃ (H : FiniteStageHomSystem f Λ P₀ Q₀), Nonempty (IsColimit H.c) := by
  sorry

/-- Finite-stage descent and Hom continuity. The first three clauses are essential surjectivity,
descent of morphisms, and eventual equality; the last is the filtered-colimit Hom comparison.
Proof steps: (1) finite intermediate fields give a filtered affine finite-etale system; (2) bounded
finite-flat constructible models and their differentials descend simultaneously; (3) internal-Hom
and derived-cohomology continuity gives finite-stage representatives; (4) injectivity of that
continuity gives eventual equality of morphisms; (5) the concrete `FiniteStageHomSystem` has
objects the finite-stage Hom sets, transitions `finiteStageHomTransition`, and legs
`finiteStageHomLeg`, and its cocone is colimiting. Source: Stacks Lemma 09YU (3)
(blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
theorem finiteEtaleConstructibleHomDescent
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [Algebra.IsSeparable K L] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : DerivedCategoryModule Λ (scheme f L)) (hP : ctf f Λ P) :
    (∃ (E : IntermediateField K L), FiniteDimensional K E ∧
      ∃ (P_E : DerivedCategoryModule Λ (scheme f E)), ctf f Λ P_E ∧
        Nonempty ((pull f Λ (A := E) (B := L) (IntermediateField.val E)).obj P_E ≅ P)) ∧
    (∀ (E : IntermediateField K L) (_hE : FiniteDimensional K E)
      (P_E Q_E : DerivedCategoryModule Λ (scheme f E)),
      ctf f Λ P_E → ctf f Λ Q_E →
      ∀ (u : (pull f Λ (A := E) (B := L) (IntermediateField.val E)).obj P_E ⟶
        (pull f Λ (A := E) (B := L) (IntermediateField.val E)).obj Q_E),
      ∃ (E' : IntermediateField K L) (hEE' : E ≤ E'),
        FiniteDimensional K E' ∧
        ctf f Λ ((pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).obj P_E) ∧
        ctf f Λ ((pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).obj Q_E) ∧
        ∃ (v : (pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).obj P_E ⟶
          (pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).obj Q_E),
          (pullValCompIso f hEE' Λ).hom.app P_E ≫
              (pull f Λ (A := E') (B := L) (IntermediateField.val E')).map v ≫
            (pullValCompIso f hEE' Λ).inv.app Q_E = u) ∧
    (∀ (E : IntermediateField K L) (_hE : FiniteDimensional K E)
      (P_E Q_E : DerivedCategoryModule Λ (scheme f E)),
      ctf f Λ P_E → ctf f Λ Q_E →
      ∀ (u v : P_E ⟶ Q_E),
        (pull f Λ (A := E) (B := L) (IntermediateField.val E)).map u =
          (pull f Λ (A := E) (B := L) (IntermediateField.val E)).map v →
        ∃ (E' : IntermediateField K L) (hEE' : E ≤ E'),
          FiniteDimensional K E' ∧
          (pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).map u =
            (pull f Λ (A := E) (B := E') (IntermediateField.inclusion hEE')).map v) ∧
    (∀ (E₀ : IntermediateField K L) (_hE₀ : FiniteDimensional K E₀)
      (P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)),
      ctf f Λ P₀ → ctf f Λ Q₀ →
      ∃ (H : FiniteStageHomSystem f Λ P₀ Q₀), Nonempty (IsColimit H.c)) := by
  refine ⟨finiteEtaleConstructibleObjectDescent f Λ P hP, ?_, ?_, ?_⟩
  · intro E hE P_E Q_E hPE hQE u
    obtain ⟨H, ⟨hH⟩⟩ := finiteEtaleConstructibleHomContinuity f Λ E hE P_E Q_E hPE hQE
    obtain ⟨E', x, hx⟩ := Types.jointly_surjective_of_isColimit hH (H.vertexEquiv.symm u)
    refine ⟨E'.val, E'.property.1, E'.property.2, ?_, ?_, H.objEquiv E' x, ?_⟩
    · exact constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ)
        (projection f (IntermediateField.inclusion E'.property.1)) hPE
    · exact constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ)
        (projection f (IntermediateField.inclusion E'.property.1)) hQE
    · change finiteStageHomLeg f Λ (H.objEquiv E' x) = u
      rw [← H.leg_eq, hx, Equiv.apply_symm_apply]
  · intro E hE P_E Q_E hPE hQE u v huv
    obtain ⟨H, ⟨hH⟩⟩ := finiteEtaleConstructibleHomContinuity f Λ E hE P_E Q_E hPE hQE
    let i : finiteStageIndex E := ⟨E, le_rfl, hE⟩
    let x : H.F.obj i := (H.objEquiv i).symm
      ((pull f Λ (A := E) (B := i.1) (IntermediateField.inclusion i.property.1)).map u)
    let y : H.F.obj i := (H.objEquiv i).symm
      ((pull f Λ (A := E) (B := i.1) (IntermediateField.inclusion i.property.1)).map v)
    have hxy : H.c.ι.app i x = H.c.ι.app i y := by
      apply H.vertexEquiv.injective
      simp only [H.leg_eq, x, y, Equiv.apply_symm_apply, finiteStageHomLeg_map]
      exact huv
    obtain ⟨j, a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hH x y).1 hxy
    refine ⟨j.val, j.property.1, j.property.2, ?_⟩
    have ht := congrArg (H.objEquiv j) ha
    rw [H.map_eq, H.map_eq] at ht
    simpa only [x, y, Equiv.apply_symm_apply, finiteStageHomTransition_map] using ht
  · exact finiteEtaleConstructibleHomContinuity f Λ

end AlgebraicGeometry.Etale.FiniteFieldDescent
