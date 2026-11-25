/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalReductionResolution
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationComplexSequence
import WeilConjectures.AlgebraicGeometry.Exact.ExactDerivedTransformation
import WeilConjectures.AlgebraicGeometry.SixFunctors.PureMultiplicationTriangleAssembly

/-! # Multiplication triangles after evaluating a pure strict reduction
Source: diagonal tower system proof, steps (2) and (3).
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  diagonalScalarExtension diagonalScalarAdjunction diagonalForget

/-- The canonical evaluation comparison for a supplied pure strict-system isomorphism.
Its three factors are evaluation, the exact functor's shift comparison, and its single
comparison. No cohomology identification is chosen.
Source: exact evaluation comparisons in diagonal tower system proof, step (3)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/
@[irreducible] def diagonalPureEvaluationIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {Z : DerivedCategory (ℕᵒᵖ ⥤ B)} (H : ℕᵒᵖ ⥤ B)
    (b : Z ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (n : ℕ) :
    (diagonalEvaluationForget U n).mapDerivedCategory.obj Z ≅
      ((DerivedCategory.singleFunctor A 0).obj (U.obj (H.obj (op n))))⟦(2 : ℤ)⟧ :=
  (diagonalEvaluationForget U n).mapDerivedCategory.mapIso b ≪≫
    ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≪≫
    (shiftFunctor (DerivedCategory A) (2 : ℤ)).mapIso
      (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).app H)

/-- The multiplication-triangle and transition property, kept folded when
specializing to concrete sheaf categories. This is a proposition containing no
chosen data.
Source: diagonal tower proof, steps (2) and (3)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle). -/
@[irreducible] def PureEvaluationTriangle
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    (M : A) (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧) : Prop :=
  ∃ d : ∀ n, U.obj (H.obj (op n)) ⟶ M,
    (∀ n, Pretriangulated.Triangle.mk
      (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧))
      ((η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalPureEvaluationIso U H b n).hom)
      (((DerivedCategory.singleFunctor A 0).map (d n))⟦(2 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M)) ∈ distTriang (DerivedCategory A)) ∧
    ∀ n, U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ d n =
      d (n + 1) ≫ (ℓ • 𝟙 M)

private def evaluationTransition
    {A B : Type*} [Category A] [Category B] (U : B ⥤ A) (n : ℕ) :
    diagonalEvaluationForget U (n + 1) ⟶ diagonalEvaluationForget U n where
  app H := U.map (H.map (homOfLE (Nat.le_succ n)).op)
  naturality {H H'} f := by
    change U.map (f.app (op (n + 1))) ≫
      U.map (H'.map (homOfLE (Nat.le_succ n)).op) =
        U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ U.map (f.app (op n))
    rw [← U.map_comp, ← U.map_comp]
    exact congrArg U.map (f.naturality _).symm

private theorem pureEvaluationIso_transition
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {Z : DerivedCategory (ℕᵒᵖ ⥤ B)} (H : ℕᵒᵖ ⥤ B)
    (b : Z ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (n : ℕ) :
    (exactDerivedTransformation (evaluationTransition U n)).app Z ≫
        (diagonalPureEvaluationIso U H b n).hom =
      (diagonalPureEvaluationIso U H b (n + 1)).hom ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (H.map (homOfLE (Nat.le_succ n)).op)))⟦(2 : ℤ)⟧' := by
  let τ := exactDerivedTransformation (evaluationTransition U n)
  have hn := τ.naturality b.hom
  simp only [diagonalPureEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← reassoc_of% hn]
  exact congrArg (fun f ↦
    (diagonalEvaluationForget U (n + 1)).mapDerivedCategory.map b.hom ≫ f)
      (exactDerivedTransformation_shiftedSingle (evaluationTransition U n) H 2)

private theorem pureEvaluationIso_quotient
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L) (n : ℕ)
    (η : DiagonalEvaluationUnit U ad D n) (P : CochainComplex A ℤ)
    [IsIso (D.ε.app P)] {K : DerivedCategory A} (e : DerivedCategory.Q.obj P ≅ K)
    (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj K ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧) :
    DerivedCategory.Q.map (diagonalEvaluationComplexMap U ad D n P) ≫
      ((((diagonalEvaluationForget U n).mapDerivedCategoryFactors.app
          ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
        diagonalPureEvaluationIso U H
          ((asIso (D.ε.app P)).symm ≪≫ D.T.mapIso e ≪≫ b) n).hom) =
      e.hom ≫ η.unit.app K ≫ (diagonalPureEvaluationIso U H b n).hom := by
  let G := diagonalEvaluationForget U n
  let R := (D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P
  let q := diagonalEvaluationComplexMap U ad D n P
  have hq : ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app P ≫
      (NatTrans.mapHomologicalComplex (diagonalEvaluationQuotient U ad D n)
        (.up ℤ)).app P) = q := by
    ext i : 1
    simp only [q, diagonalEvaluationComplexMap_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f]
    exact Category.id_comp _
  have h : η.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (D.ε.app P) ≫
        G.mapDerivedCategoryFactors.hom.app R = DerivedCategory.Q.map q :=
    (η.complexes P).trans (congrArg DerivedCategory.Q.map hq)
  have h' : DerivedCategory.Q.map q ≫ G.mapDerivedCategoryFactors.inv.app R =
      η.unit.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategory.map (D.ε.app P) := by
    apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app R)).1
    have hh : (DerivedCategory.Q.map q ≫ G.mapDerivedCategoryFactors.inv.app R) ≫
        G.mapDerivedCategoryFactors.hom.app R = DerivedCategory.Q.map q :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ DerivedCategory.Q.map q ≫ f)
          (Iso.inv_hom_id_app G.mapDerivedCategoryFactors R)).trans
            (Category.comp_id _))
    exact hh.trans (h.symm.trans (Category.assoc _ _ _).symm)
  have hk : G.mapDerivedCategory.map (D.ε.app P) ≫
      (diagonalPureEvaluationIso U H
        ((asIso (D.ε.app P)).symm ≪≫ D.T.mapIso e ≪≫ b) n).hom =
      G.mapDerivedCategory.map (D.T.map e.hom) ≫
        (diagonalPureEvaluationIso U H b n).hom := by
    simp only [diagonalPureEvaluationIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, asIso_inv, Functor.map_comp, Category.assoc]
    rw [← G.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
      G.mapDerivedCategory.map_id, Category.id_comp]
  change DerivedCategory.Q.map q ≫ G.mapDerivedCategoryFactors.inv.app R ≫
    (diagonalPureEvaluationIso U H
      ((asIso (D.ε.app P)).symm ≪≫ D.T.mapIso e ≪≫ b) n).hom = _
  rw [← Category.assoc, h', Category.assoc, hk]
  have hn := η.unit.naturality e.hom
  simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ (diagonalPureEvaluationIso U H b n).hom) hn.symm

private theorem pureEvaluationTriangle_of_resolution
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    {ℓ : ℕ} {L : A ⥤ B} (U : B ⥤ A) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (η : ∀ n, DiagonalEvaluationUnit U ad D n) (M : A) (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (hres : ∃ (P : CochainComplex A ℤ)
      (_e : DerivedCategory.Q.obj P ≅
        ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ IsIso (D.ε.app P))
    (hseq : ∀ (P : CochainComplex A ℤ),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) →
      ∀ n, ∃ hz : (ℓ ^ (n + 1) • 𝟙 P) ≫ diagonalEvaluationComplexMap U ad D n P = 0,
        (ShortComplex.mk _ _ hz).ShortExact) :
    PureEvaluationTriangle ℓ L U ad D η M H b := by
  let K := ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧
  obtain ⟨P, e, hP, hε⟩ := hres
  let := hε
  let R := (D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P
  let G (n : ℕ) := diagonalEvaluationForget U n
  let Q (n : ℕ) := ((G n).mapHomologicalComplex (.up ℤ)).obj R
  let q (n : ℕ) := diagonalEvaluationComplexMap U ad D n P
  let t (n : ℕ) := (NatTrans.mapHomologicalComplex (evaluationTransition U n) (.up ℤ)).app R
  choose hz hS using hseq P hP
  let k : DerivedCategory.Q.obj R ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧ :=
    (asIso (D.ε.app P)).symm ≪≫ D.T.mapIso e ≪≫ b
  let β (n : ℕ) : DerivedCategory.Q.obj (Q n) ≅
      ((DerivedCategory.singleFunctor A 0).obj (U.obj (H.obj (op n))))⟦(2 : ℤ)⟧ :=
    ((G n).mapDerivedCategoryFactors.app R).symm ≪≫ diagonalPureEvaluationIso U H k n
  have ht (n : ℕ) : q (n + 1) ≫ t n = q n := by
    ext i : 1
    simp only [q, diagonalEvaluationComplexMap_f, HomologicalComplex.comp_f,
      t, NatTrans.mapHomologicalComplex_app_f]
    change (ad.unit.app (P.X i) ≫ U.map ((D.ordinary.π (n + 1)).app (P.X i))) ≫
        U.map ((D.ordinary.E.obj (P.X i)).map (homOfLE (Nat.le_succ n)).op) =
      ad.unit.app (P.X i) ≫ U.map ((D.ordinary.π n).app (P.X i))
    rw [Category.assoc, ← U.map_comp, D.ordinary.transition]
  have hβ (n : ℕ) : DerivedCategory.Q.map (t n) ≫ (β n).hom =
      (β (n + 1)).hom ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (H.map (homOfLE (Nat.le_succ n)).op)))⟦(2 : ℤ)⟧' := by
    apply (cancel_epi ((G (n + 1)).mapDerivedCategoryFactors.hom.app R)).1
    simp only [β, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% (exactDerivedTransformation_app (evaluationTransition U n) R)]
    exact pureEvaluationIso_transition U H k n
  let v (n : ℕ) := (η n).unit.app K ≫ (diagonalPureEvaluationIso U H b n).hom
  have hv (n : ℕ) : DerivedCategory.Q.map (q n) ≫ (β n).hom = e.hom ≫ v n := by
    exact pureEvaluationIso_quotient U ad D n (η n) P e H b
  unfold PureEvaluationTriangle
  exact pure_multiplication_triangle_assembly ℓ P M (H ⋙ U) e Q q t hz hS ht β hβ v hv

/-- Evaluated reduction is the cofiber of prime-power multiplication, and its
cofiber boundaries have transition multiplier ell. This statement involves an arbitrary
integral sheaf M; it uses no roots, Tate line, or Kummer boundary.

Source: diagonal tower system proof, steps (2) and (3), the map of two-term resolutions
with components (ell,1)
(blueprint: lem-sfb-diagonal-pure-evaluation-triangle).

Proof: choose a flat-term K-flat resolution P of M[1]. Nonzero integer multiplication
is monic on every flat term and remains so after the exact p-adic extension.
The quotient universal property of D.ordinary, together with the canonical equality
Z_ell/ell^(n+1)=Z/ell^(n+1), identifies its underlying evaluated quotient with the
integral cokernel of ell^(n+1), carrying the scalar-adjunction unit to the quotient map.
The resulting degreewise short exact sequence gives the multiplication
triangle. Uniqueness of pointwise left derived functors makes D's counit invertible
on P, and the complexes equation of eta identifies the middle arrow with its quotient
unit. Transport through the resolution and the supplied b. The last arrow is a map
between single sheaves shifted twice, hence uniquely the shifted image of d_n by full
faithfulness. For successive levels the map of short exact sequences is (ell,1,quotient).
Naturality of the short-exact-sequence triangle gives d_(n+1) followed by ell equals
the underlying transition followed by d_n. The same resolution at every level is
essential; neither a family of unrelated triangles nor levelwise detection of derived
morphisms is used. This applies to M=0 and to n=0 without alteration. -/
theorem diagonal_pure_evaluation_triangle (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n)
    (M : DiagonalAb W) (H : DiagonalSystems ℓ W)
    (b : D.T.obj (((DerivedCategory.singleFunctor (DiagonalAb W) 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (DiagonalSystems ℓ W) 0).obj H)⟦(2 : ℤ)⟧) :
    PureEvaluationTriangle ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D η M H b := by
  exact pureEvaluationTriangle_of_resolution (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D η M H b
    (diagonal_reduction_resolution ℓ W D _)
    (diagonal_evaluation_complex_shortExact ℓ W D)

end AlgebraicGeometry.ProEtale
