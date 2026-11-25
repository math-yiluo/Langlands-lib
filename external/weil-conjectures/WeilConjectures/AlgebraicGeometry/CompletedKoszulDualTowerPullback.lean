/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.AlgebraicGeometry.CompletedPositiveKoszulPullback
import WeilConjectures.AlgebraicGeometry.FiniteFreeComplexDualPullback
import all WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat

/-! # The finite dual Koszul tower under completed inverse image

Source: Stacks Project, algebraization.tex, Tag 0A0E, and
sites-cohomology.tex, Tag 07A4.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe v u u' w w' b t

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

-- Assemble duality contravariantly: a positive comparison must be inverted.
private theorem dualizeAugmentedDiagram
    {E : Type u} [Category.{w} E] {E' : Type u'} [Category.{w'} E']
    {B : Type b} [Category.{t} B]
    (P : E ⥤ E') (HR : Eᵒᵖ ⥤ E) (HS : E'ᵒᵖ ⥤ E')
    (Free : E → Prop) (R : E) (S : E')
    (ηR : R ⟶ HR.obj (op R)) (ηS : S ⟶ HS.obj (op S))
    (u j : P.obj R ≅ S)
    (d : ∀ (X : E) (_ : Free X), P.obj (HR.obj (op X)) ≅ HS.obj (op (P.obj X)))
    (hd : ∀ (X X' : E) (hX : Free X) (hX' : Free X') (f : X' ⟶ X),
      P.map (HR.map f.op) ≫ (d X' hX').hom =
        (d X hX).hom ≫ HS.map (P.map f).op)
    (hR : Free R)
    (hη : P.map ηR ≫ (d R hR).hom = j.hom ≫ ηS ≫ HS.map u.hom.op)
    (X : B ⥤ E) (Y : B ⥤ E') (hX : ∀ m : B, Free (X.obj m))
    (e : X ⋙ P ≅ Y) (p : ∀ m : B, X.obj m ⟶ R) (q : ∀ m : B, Y.obj m ⟶ S)
    (hp : ∀ m : B, P.map (p m) ≫ u.hom = e.hom.app m ≫ q m) :
    ∃ h : X.op ⋙ HR ⋙ P ≅ Y.op ⋙ HS,
      ∀ m : B, P.map (ηR ≫ HR.map (p m).op) ≫ h.hom.app (op m) =
        j.hom ≫ ηS ≫ HS.map (q m).op := by
  let h : X.op ⋙ HR ⋙ P ≅ Y.op ⋙ HS :=
    NatIso.ofComponents
      (fun m ↦ d (X.obj m.unop) (hX m.unop) ≪≫
        HS.mapIso (e.app m.unop).symm.op) (by
      intro m n f
      change P.map (HR.map (X.map f.unop).op) ≫
          ((d (X.obj n.unop) (hX n.unop)).hom ≫ HS.map (e.inv.app n.unop).op) =
        ((d (X.obj m.unop) (hX m.unop)).hom ≫ HS.map (e.inv.app m.unop).op) ≫
          HS.map (Y.map f.unop).op
      rw [← Category.assoc,
        hd (X.obj m.unop) (X.obj n.unop) (hX m.unop) (hX n.unop) (X.map f.unop),
        Category.assoc, Category.assoc, ← HS.map_comp, ← HS.map_comp]
      congr 2
      exact (congrArg Quiver.Hom.op (e.inv.naturality f.unop)).symm)
  refine ⟨h, ?_⟩
  intro m
  change P.map (ηR ≫ HR.map (p m).op) ≫
      ((d (X.obj m) (hX m)).hom ≫ HS.map (e.inv.app m).op) = _
  rw [P.map_comp, Category.assoc, ← Category.assoc _ (d (X.obj m) (hX m)).hom,
    hd R (X.obj m) hR (hX m) (p m)]
  simp only [← Category.assoc]
  rw [hη]
  simp only [Category.assoc]
  have he : e.inv.app m ≫ P.map (p m) ≫ u.hom = q m := by
    rw [hp, Iso.inv_hom_id_app_assoc]
  rw [← HS.map_comp, ← HS.map_comp]
  simpa only [op_comp, Category.assoc] using
    congrArg (fun z ↦ j.hom ≫ ηS ≫ HS.map z.op) he

/-- Pullback identifies the bounded finite free dual Koszul tower, with its unit.
Only the Koszul complexes occur here; there is no arbitrary coefficient complex.

Source: Stacks Project, algebraization.tex, Tag 0A0E, finite Koszul calculation;
sites-cohomology.tex, Tag 07A4, tensor pullback.
(auxiliary; not a blueprint node).

Proof: the positive Koszul complex is the ordered tensor of rank-one two-term
complexes. Expand it into the finite free basis indexed by Boolean subsets. Its
dual has the dual basis, with the subset of cardinality k in degree -k. Module
inverse image along the invertible coefficient map preserves rank-one modules,
finite sums, and their scalar morphisms. Naturality of the constant-ring
comparison in the coefficient ring fixes each constant a_i: apply it to the
universal element of the polynomial ring Z[X] and all evaluation maps. The limit
projection equations for completedMap then identify the images of these constants
in the completions. Therefore the coordinate comparisons identify differentials,
with their ordered signs, and the transitions, which multiply selected coordinates
by a_i. This gives an isomorphism of towers. First use the canonical comparison
on the rank-one ring complex. The given j differs from it by an automorphism of
the target ring complex, hence multiplication by an invertible global section.
Multiply every dual coordinate by that section. This preserves differentials and
transitions and makes the coaugmentation equation hold: its empty coordinate is
identity, and every other coordinate is zero. For no generators the comparison
is the constant tower with value j. Zero scalars, repeated scalars and the zero
ring satisfy the identical formulas. -/
theorem completedKoszulDualTowerPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (A : Type v) [CommRing A] (I : Ideal A) [IsIso (completedMap F A I)]
    (r : ℕ) (a : Fin r → A)
    (j : ((pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)).obj
        (ringedSiteRingComplex (completed J A I)) ≅
      ringedSiteRingComplex (completed K A I)) :
    let P := (pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)
    ∃ e : ringedKoszulDualTower (completed J A I) r
          (fun i ↦ algebraSection (baseMap J A I true) (a i)) ⋙ P ≅
        ringedKoszulDualTower (completed K A I) r
          (fun i ↦ algebraSection (baseMap K A I true) (a i)),
      ∀ m : ℕ,
        P.map (ringedKoszulDualUnit (completed J A I) r
            (fun i ↦ algebraSection (baseMap J A I true) (a i)) m) ≫
            e.hom.app (op m) =
          j.hom ≫ ringedKoszulDualUnit (completed K A I) r
            (fun i ↦ algebraSection (baseMap K A I true) (a i)) m := by
  let R := completed J A I
  let S := completed K A I
  let P := (pull F (completedMap F A I)).mapHomologicalComplex (.up ℤ)
  let b : Fin r → (R.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ algebraSection (baseMap J A I true) (a i)
  let c : Fin r → (S.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ algebraSection (baseMap K A I true) (a i)
  let X := ringedKoszulDiagram R r b
  let Y := ringedKoszulDiagram S r c
  let HR := (homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)
  let HS := (homComplexFunctor (R := S)).flip.obj (ringedSiteRingComplex S)
  let Free := fun E : Cx R ↦ ∀ n : ℤ, ∃ (T : Type v) (_ : Fintype T),
    Nonempty (E.X n ≅ SheafOfModules.free (R := siteModuleRings R) T)
  have hX (m : ℕ) : Free (X.obj m) :=
    fun n ↦ koszulDiagram_finiteFree R r b m n
  have hR : Free (ringedSiteRingComplex R) :=
    fun n ↦ koszulDiagram_finiteFree R 0 (fun i ↦ Fin.elim0 i) 0 n
  obtain ⟨u, d, hd, hη⟩ :=
    finiteFreeComplexDualPullback F V adj (completedMap F A I) j
  obtain ⟨e, he⟩ := completedPositiveKoszulPullback F V adj A I r a u
  exact dualizeAugmentedDiagram P HR HS Free
    (ringedSiteRingComplex R) (ringedSiteRingComplex S)
    (ringedHomUnitEvaluationIso R (ringedSiteRingComplex R)).inv
    (ringedHomUnitEvaluationIso S (ringedSiteRingComplex S)).inv
    u j d hd hR (hη hR) X Y hX e
    (ringedKoszulProjection R r b) (ringedKoszulProjection S r c) he

end CategoryTheory.ConstantCompletion
