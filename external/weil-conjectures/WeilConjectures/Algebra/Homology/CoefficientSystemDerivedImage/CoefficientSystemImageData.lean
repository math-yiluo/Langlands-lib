/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedLeftAdjoint
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Direct image and evaluation of strict coefficient systems

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21,
and Lemma 4.10, printed pp. 23--24
(blueprint: lem-pur-coefficient-system-derived-comparison).

The index `n` denotes the positive exponent `n+1`. All systems, evaluation functors,
scalar extensions and adjoint transitions are the recorded coefficient-evaluation
interface. The structures below specify the geometric lifts and the comparison,
including their normalizations; they are conclusions, not hypotheses of the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d a b av bv
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

universe p pv q qv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_unit_of_counit
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {E : Type p} [Category.{pv} E] {D : Type q} [Category.{qv} D]
    {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
    {Fl : E ⥤ D} {Gl : D ⥤ E} (alevel : Fl ⊣ Gl)
    {EA : A ⥤ E} {EB : B ⥤ D}
    (alpha : Fs ⋙ EB ≅ EA ⋙ Fl) (beta : Gs ⋙ EA ≅ EB ⋙ Gl)
    (hcounit : ∀ M, alpha.hom.app (Gs.obj M) ≫ Fl.map (beta.hom.app M) ≫
      alevel.counit.app (EB.obj M) = EB.map (asys.counit.app M)) (H : A) :
    EA.map (asys.unit.app H) ≫ beta.hom.app (Fs.obj H) ≫
      Gl.map (alpha.hom.app H) = alevel.unit.app (EA.obj H) := by
  apply (alevel.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_symm_unit]
  simp only [Functor.map_comp]
  apply (cancel_epi (alpha.hom.app H)).mp
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc, Category.comp_id]
  have hn := alevel.counit.naturality (alpha.hom.app H)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [hn]
  have ha := alpha.hom.naturality (asys.unit.app H)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ha
  rw [← Category.assoc (alpha.hom.app H) (Fl.map (EA.map (asys.unit.app H))), ← ha]
  simp only [Category.assoc]
  have hc := congrArg (fun f ↦ f ≫ alpha.hom.app H) (hcounit (Fs.obj H))
  simp only [Category.assoc] at hc
  rw [hc, ← Category.assoc, ← EB.map_comp, asys.left_triangle_components, EB.map_id]
  exact Category.id_comp _

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

/-- The existing forgetful functor at a coefficient level.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
abbrev coefficientUnderlying (n : ℕ) :
    coefficientLevelModules (J := J) O ell n ⥤ Sheaf J (Type w) :=
  toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

/-- Constant coefficient generators, obtained from the actual ring-sheafification unit.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def coefficientConstantSection (n : ℕ)
    (x : O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) :
    (constantSheaf J (Type w)).obj PUnit ⟶
      (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj
        (coefficientQuotientSheaf (J := J) O ell n) :=
  ((sheafificationAdjunction J (Type w)).homEquiv _ _).symm
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{w+1}) ↦ x)) ≫
      whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{w}))

/-- Scalar restriction leaves the underlying sheaf of sets unchanged.
Source: Stacks 03CZ (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def coefficientRestrictionUnderlying {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := J) O ell h ⋙ coefficientUnderlying (J := J) O ell m ≅
      coefficientUnderlying (J := J) O ell n :=
  isoWhiskerRight (siteScalarUnderlyingIso
    (coefficientQuotientMap (J := J) O ell h))
      (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w}))

section DerivedAdjunction
variable {A : Type a} {B : Type b} [Category.{av} A] [Category.{bv} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)

/-- Exact inverse image and total right direct image, with their normalized adjunction.
The universal right-derived pair and its K-injective comparison fix the right functor;
the transpose equation fixes its adjunction relative to the ordinary one.
Source: Zheng, Lemma 4.10; Stacks 09T5, 0FND
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
structure CoefficientDerivedImage where
  inverse : DerivedCategory A ⥤ DerivedCategory B
  inverseFactors : DerivedCategory.Q ⋙ inverse ≅
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  direct : DerivedCategory B ⥤ DerivedCategory A
  directUnit : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ direct
  isRightDerived : direct.IsRightDerivedFunctor directUnit
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (directUnit.app I)
  adjunction : inverse ⊣ direct
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (inverseFactors.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I f) ≫ directUnit.app I
end DerivedAdjunction

section AbstractImages
universe ga gb gal gbl gav gbv galv gblv
variable {A : Type ga} [Category.{gav} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type gb} [Category.{gbv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {MA : ℕ → Type gal} [∀ n, Category.{galv} (MA n)] [∀ n, Abelian (MA n)]
  [∀ n, HasDerivedCategory.{d} (MA n)]
  {MB : ℕ → Type gbl} [∀ n, Category.{gblv} (MB n)] [∀ n, Abelian (MB n)]
  [∀ n, HasDerivedCategory.{d} (MB n)]

/-- Evaluation comparison data over arbitrary abelian categories.
Using category parameters keeps the generated recursors independent of the large
ringed-site presentations. The specialization below fixes all parameters.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
structure CoefficientEvaluationImageData
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (Flevel : ∀ n, MA n ⥤ MB n) (Glevel : ∀ n, MB n ⥤ MA n)
    [∀ n, (Flevel n).Additive] [∀ n, (Glevel n).Additive]
    (adjLevel : ∀ n, Flevel n ⊣ Glevel n)
    (eA : ∀ n, A ⥤ MA n) (eB : ∀ n, B ⥤ MB n)
    [∀ n, (eA n).Additive] [∀ n, (eB n).Additive]
    (EA : ∀ n, DerivedCategory A ⥤ DerivedCategory (MA n))
    (EB : ∀ n, DerivedCategory B ⥤ DerivedCategory (MB n))
    (factorsA : ∀ n, DerivedCategory.Q ⋙ EA n ≅
      (eA n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (factorsB : ∀ n, DerivedCategory.Q ⋙ EB n ≅
      (eB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (alpha : ∀ n, F ⋙ eB n ≅ eA n ⋙ Flevel n) where
  system : CoefficientDerivedImage F G adj
  level : ∀ n, CoefficientDerivedImage (Flevel n) (Glevel n) (adjLevel n)
  inverseEvaluation : ∀ n, system.inverse ⋙ EB n ≅
    EA n ⋙ (level n).inverse
  inverseEvaluation_rep : ∀ n H,
    (inverseEvaluation n).hom.app (DerivedCategory.Q.obj H) ≫
      (level n).inverse.map ((factorsA n).hom.app H) ≫
      (level n).inverseFactors.hom.app
        (((eA n).mapHomologicalComplex (.up ℤ)).obj H) =
    (EB n).map (system.inverseFactors.hom.app H) ≫
      (factorsB n).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj H) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (alpha n) (.up ℤ)).hom.app H)
  directEvaluation : ∀ n, system.direct ⋙ EA n ≅
    EB n ⋙ (level n).direct
  counit : ∀ n M,
    (inverseEvaluation n).hom.app (system.direct.obj M) ≫
      (level n).inverse.map ((directEvaluation n).hom.app M) ≫
      (level n).adjunction.counit.app ((EB n).obj M) =
    (EB n).map (system.adjunction.counit.app M)

variable
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (Flevel : ∀ n, MA n ⥤ MB n) (Glevel : ∀ n, MB n ⥤ MA n)
    [∀ n, (Flevel n).Additive] [∀ n, (Glevel n).Additive]
    (adjLevel : ∀ n, Flevel n ⊣ Glevel n)
    (eA : ∀ n, A ⥤ MA n) (eB : ∀ n, B ⥤ MB n)
    [∀ n, (eA n).Additive] [∀ n, (eB n).Additive]
    (EA : ∀ n, DerivedCategory A ⥤ DerivedCategory (MA n))
    (EB : ∀ n, DerivedCategory B ⥤ DerivedCategory (MB n))
    (factorsA : ∀ n, DerivedCategory.Q ⋙ EA n ≅
      (eA n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (factorsB : ∀ n, DerivedCategory.Q ⋙ EB n ≅
      (eB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (alpha : ∀ n, F ⋙ eB n ≅ eA n ⋙ Flevel n)

variable {F G adj Flevel Glevel adjLevel eA eB EA EB factorsA factorsB alpha} in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The evaluated unit identity follows from the evaluated counit identity.
Source: Zheng Lemma 4.10. Proof: transpose the proposed unit under the level
adjunction, precompose with the inverse-evaluation isomorphism, and use its
naturality. The evaluated counit identity reduces the result to the system
triangle identity. Injectivity of transposition gives the unit equation.
(blueprint: def-pur-coefficient-system-image-data). -/
theorem CoefficientEvaluationImageData.unit
    (E : CoefficientEvaluationImageData F G adj Flevel Glevel adjLevel eA eB
      EA EB factorsA factorsB alpha) (n : ℕ) (H : DerivedCategory A) :
    (EA n).map (E.system.adjunction.unit.app H) ≫
      (E.directEvaluation n).hom.app (E.system.inverse.obj H) ≫
      (E.level n).direct.map ((E.inverseEvaluation n).hom.app H) =
    (E.level n).adjunction.unit.app ((EA n).obj H) := by
  exact evaluation_unit_of_counit E.system.adjunction (E.level n).adjunction
    (E.inverseEvaluation n) (E.directEvaluation n) (E.counit n) H

/-- Coefficient comparison data for fixed evaluation images and scalar adjunctions.
All functors and flatness predicates are specialized to the actual coefficient data below.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
structure CoefficientScalarImageData
    (TA : ∀ {m n : ℕ}, n ≤ m → MA m ⥤ MA n)
    (RA : ∀ {m n : ℕ}, n ≤ m → MA n ⥤ MA m)
    [∀ m n (h : n ≤ m), (TA h).Additive] [∀ m n (h : n ≤ m), (RA h).Additive]
    (adjTA : ∀ {m n : ℕ} (h : n ≤ m), TA h ⊣ RA h)
    (KFlatA : ∀ n, CochainComplex (MA n) ℤ → Prop) (FlatA : ∀ n, MA n → Prop)
    (scalarA : ∀ {m n : ℕ} (h : n ≤ m),
      DerivedCoefficientScalarExtension (TA h) (RA h) (adjTA h) (KFlatA m))
    (TB : ∀ {m n : ℕ}, n ≤ m → MB m ⥤ MB n)
    (RB : ∀ {m n : ℕ}, n ≤ m → MB n ⥤ MB m)
    [∀ m n (h : n ≤ m), (TB h).Additive] [∀ m n (h : n ≤ m), (RB h).Additive]
    (adjTB : ∀ {m n : ℕ} (h : n ≤ m), TB h ⊣ RB h)
    (KFlatB : ∀ n, CochainComplex (MB n) ℤ → Prop)
    (scalarB : ∀ {m n : ℕ} (h : n ≤ m),
      DerivedCoefficientScalarExtension (TB h) (RB h) (adjTB h) (KFlatB m))
    (transitionA : ∀ {m n : ℕ} (h : n ≤ m), EA m ⟶ EA n ⋙ (scalarA h).restriction)
    (transitionB : ∀ {m n : ℕ} (h : n ≤ m), EB m ⟶ EB n ⋙ (scalarB h).restriction)
    (beta : ∀ {m n : ℕ} (h : n ≤ m), RA h ⋙ Flevel m ≅ Flevel n ⋙ RB h)
    (E : CoefficientEvaluationImageData F G adj Flevel Glevel adjLevel eA eB
      EA EB factorsA factorsB alpha) where
  tensor : ∀ {m n : ℕ} (h : n ≤ m),
    TA h ⋙ Flevel n ≅
      Flevel m ⋙ TB h
  tensor_unit : ∀ {m n : ℕ} (h : n ≤ m) M,
    (Flevel m).map ((adjTA h).unit.app M) ≫
      (beta h).hom.app ((TA h).obj M) ≫
      (RB h).map ((tensor h).hom.app M) =
    (adjTB h).unit.app ((Flevel m).obj M)
  derivedTensor : ∀ {m n : ℕ} (h : n ≤ m),
    (scalarA h).derived ⋙ (E.level n).inverse ≅
      (E.level m).inverse ⋙ (scalarB h).derived
  derivedTensor_rep : ∀ {m n : ℕ} (h : n ≤ m) P,
    KFlatA m P →
    (∀ i : ℤ, FlatA m (P.X i)) →
    (derivedTensor h).hom.app (DerivedCategory.Q.obj P) ≫
      (scalarB h).derived.map ((E.level m).inverseFactors.hom.app P) ≫
      (scalarB h).counit.app (((Flevel m).mapHomologicalComplex (.up ℤ)).obj P) =
    (E.level n).inverse.map ((scalarA h).counit.app P) ≫
      (E.level n).inverseFactors.hom.app
        (((TA h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app P)
  restrictedDirect : ∀ {m n : ℕ} (h : n ≤ m),
    (scalarB h).restriction ⋙ (E.level m).direct ≅
      (E.level n).direct ⋙ (scalarA h).restriction
  restrictedDirect_mate : ∀ {m n : ℕ} (h : n ≤ m) A B
    (f : (E.level n).inverse.obj ((scalarA h).derived.obj A) ⟶ B),
    (scalarA h).derivedAdj.homEquiv A ((E.level n).direct.obj B)
      ((E.level n).adjunction.homEquiv _ B f) =
    (E.level m).adjunction.homEquiv A ((scalarB h).restriction.obj B)
      ((scalarB h).derivedAdj.homEquiv ((E.level m).inverse.obj A) B
        ((derivedTensor h).inv.app A ≫ f)) ≫ (restrictedDirect h).hom.app B
  restrictedInverse : ∀ {m n : ℕ} (h : n ≤ m),
    (scalarA h).restriction ⋙ (E.level m).inverse ≅
      (E.level n).inverse ⋙ (scalarB h).restriction
  restrictedInverse_mate : ∀ {m n : ℕ} (h : n ≤ m) A,
    (E.level m).adjunction.homEquiv _ _ ((restrictedInverse h).hom.app A) =
      (scalarA h).restriction.map ((E.level n).adjunction.unit.app A) ≫
        (restrictedDirect h).inv.app ((E.level n).inverse.obj A)
  inverseTransition : ∀ {m n : ℕ} (h : n ≤ m) H,
    (transitionB h).app (E.system.inverse.obj H) ≫
      (scalarB h).restriction.map ((E.inverseEvaluation n).hom.app H) =
    (E.inverseEvaluation m).hom.app H ≫ (E.level m).inverse.map ((transitionA h).app H) ≫
      (restrictedInverse h).hom.app ((EA n).obj H)
  directTransition : ∀ {m n : ℕ} (h : n ≤ m) M,
    (transitionA h).app (E.system.direct.obj M) ≫
      (scalarA h).restriction.map ((E.directEvaluation n).hom.app M) =
    (E.directEvaluation m).hom.app M ≫ (E.level m).direct.map ((transitionB h).app M) ≫
      (restrictedDirect h).hom.app ((EB n).obj M)

/-- Formal descent conditions, parameterized by the already fixed construction data.
All predicates and functors are specialized below; no extra choice is introduced.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
structure CoefficientImageDescentData {gt : Type*}
    (EB : ∀ n, DerivedCategory B ⥤ DerivedCategory (MB n))
    (systemDirect : gt → DerivedCategory B ⥤ DerivedCategory A)
    (levelInverse : gt → ∀ n, DerivedCategory (MA n) ⥤ DerivedCategory (MB n))
    (counitIso : gt → DerivedCategory B → Prop)
    (normalizedA : DerivedCategory A → Prop) (normalizedB : DerivedCategory B → Prop) where
  construction : gt
  detectsIso : ∀ {M N : DerivedCategory B} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((EB n).map f)
  boundedBelow : ∀ M : DerivedCategory B,
    (∃ a : ℤ, M.IsGE a) → ∃ a : ℤ, ((systemDirect construction).obj M).IsGE a
  origin :
    (∀ n (A B : DerivedCategory (MA n)),
      (∃ a : ℤ, A.IsGE a) → (∃ b : ℤ, B.IsGE b) →
      Function.Bijective ((levelInverse construction n).map : (A ⟶ B) → _)) →
    ∀ M : DerivedCategory B,
      (∃ a : ℤ, M.IsGE a) →
      (∀ n, ∃ H : DerivedCategory (MA n),
        (∃ a : ℤ, H.IsGE a) ∧
        Nonempty ((levelInverse construction n).obj H ≅ (EB n).obj M)) →
      counitIso construction M ∧
        (normalizedB M → normalizedA ((systemDirect construction).obj M))

end AbstractImages

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

/-- The ordinary level and system images. The algebraic lift transports all operations;
constants are fixed on every coefficient generator, and the displayed Hom formula is
the underlying set-sheaf adjunction. Evaluation and transition equations fix the actual
levelwise system functors, on objects and maps, rather than arbitrary adjoint functors.
Source: Zheng, Construction 4.1, and the paragraph before Lemma 4.10
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
structure CoefficientSystemOrdinaryImage where
  singleton : L.obj ((constantSheaf J (Type w)).obj PUnit) ≅
    (constantSheaf K (Type w)).obj PUnit
  lift : ∀ n, AlgebraicInverseImage L
    (coefficientQuotientSheaf (J := J) O ell n)
    (coefficientQuotientSheaf (J := K) O ell n)
  constants : ∀ n x,
    L.map (coefficientConstantSection (J := J) O ell n x) ≫ (lift n).ringUnderlying.hom =
      singleton.hom ≫ coefficientConstantSection (J := K) O ell n x
  [inverseAdditive : ∀ n, (lift n).modules.Additive]
  inverseExact : ∀ n, PreservesFiniteLimits (lift n).modules ∧
    PreservesFiniteColimits (lift n).modules
  right : ∀ n, coefficientLevelModules (J := K) O ell n ⥤
    coefficientLevelModules (J := J) O ell n
  [rightAdditive : ∀ n, (right n).Additive]
  rightUnderlying : ∀ n, right n ⋙ coefficientUnderlying (J := J) O ell n ≅
    coefficientUnderlying (J := K) O ell n ⋙ V
  levelAdj : ∀ n, (lift n).modules ⊣ right n
  levelTranspose : ∀ n M N (f : (lift n).modules.obj M ⟶ N),
    (coefficientUnderlying (J := J) O ell n).map ((levelAdj n).homEquiv M N f) ≫
      (rightUnderlying n).hom.app N =
    adj.homEquiv _ _ ((lift n).moduleUnderlying.inv.app M ≫
      (coefficientUnderlying (J := K) O ell n).map f)
  restrictInverse : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := J) O ell h ⋙ (lift m).modules ≅
      (lift n).modules ⋙ coefficientRestriction (J := K) O ell h
  restrictInverseUnderlying : ∀ {m n : ℕ} (h : n ≤ m) M,
    (coefficientUnderlying (J := K) O ell m).map ((restrictInverse h).hom.app M) ≫
      (coefficientRestrictionUnderlying (J := K) O ell h).hom.app
        ((lift n).modules.obj M) ≫ (lift n).moduleUnderlying.hom.app M =
    (lift m).moduleUnderlying.hom.app ((coefficientRestriction (J := J) O ell h).obj M) ≫
      L.map ((coefficientRestrictionUnderlying (J := J) O ell h).hom.app M)
  inverse : CoefficientSystem (J := J) O ell ⥤ CoefficientSystem (J := K) O ell
  rightSystem : CoefficientSystem (J := K) O ell ⥤ CoefficientSystem (J := J) O ell
  [systemInverseAdditive : inverse.Additive]
  [systemRightAdditive : rightSystem.Additive]
  systemExact : PreservesFiniteLimits inverse ∧ PreservesFiniteColimits inverse
  inverseEvaluation : ∀ n, inverse ⋙ coefficientEvaluation (J := K) n ≅
    coefficientEvaluation (J := J) n ⋙ (lift n).modules
  rightEvaluation : ∀ n, rightSystem ⋙ coefficientEvaluation (J := J) n ≅
    coefficientEvaluation (J := K) n ⋙ right n
  inverseTransition : ∀ n M,
    ((inverse.obj M).transition n) ≫
      (coefficientRestriction (J := K) O ell (Nat.le_succ n)).map
        ((inverseEvaluation n).hom.app M) =
    (inverseEvaluation (n + 1)).hom.app M ≫ (lift (n + 1)).modules.map (M.transition n) ≫
      (restrictInverse (Nat.le_succ n)).hom.app (M.level n)
  systemAdj : inverse ⊣ rightSystem
  systemTranspose : ∀ M N (f : inverse.obj M ⟶ N) n,
    (coefficientEvaluation (J := J) n).map ((systemAdj.homEquiv M N) f) ≫
      (rightEvaluation n).hom.app N =
    (levelAdj n).homEquiv (M.level n) (N.level n)
      ((inverseEvaluation n).inv.app M ≫ (coefficientEvaluation (J := K) n).map f)

attribute [instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

/-- The evaluation data specialized to the prescribed coefficient-system functors.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
abbrev CoefficientEvaluationImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) :=
  CoefficientEvaluationImageData S.inverse S.rightSystem S.systemAdj
    (fun n ↦ (S.lift n).modules) S.right S.levelAdj
    (coefficientEvaluation (J := J)) (coefficientEvaluation (J := K))
    PY.evaluation PX.evaluation PY.evaluationFactors PX.evaluationFactors S.inverseEvaluation

/-- The scalar data specialized to the actual quotient tensors and scalar packages.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
abbrev CoefficientScalarImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell))
    (E : CoefficientEvaluationImage O ell L V adj S PY PX) :=
  CoefficientScalarImageData
    (F := S.inverse) (G := S.rightSystem) (adj := S.systemAdj)
    (Flevel := fun n ↦ (S.lift n).modules) (Glevel := S.right) (adjLevel := S.levelAdj)
    (eA := coefficientEvaluation (J := J)) (eB := coefficientEvaluation (J := K))
    (EA := PY.evaluation) (EB := PX.evaluation)
    (factorsA := PY.evaluationFactors) (factorsB := PX.evaluationFactors)
    (alpha := S.inverseEvaluation)
    (fun {_ _} h ↦ coefficientTensor (J := J) h)
    (fun {_ _} h ↦ coefficientRestriction (J := J) O ell h)
    (fun {_ _} h ↦ coefficientTensorAdj (J := J) h)
    (fun n ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell n))
    (fun n ↦ IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell n))
    (fun {_ _} h ↦ PY.scalar h)
    (fun {_ _} h ↦ coefficientTensor (J := K) h)
    (fun {_ _} h ↦ coefficientRestriction (J := K) O ell h)
    (fun {_ _} h ↦ coefficientTensorAdj (J := K) h)
    (fun n ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := K) O ell n))
    (fun {_ _} h ↦ PX.scalar h)
    (fun {_ _} h ↦ PY.transition h) (fun {_ _} h ↦ PX.transition h)
    (fun {_ _} h ↦ S.restrictInverse h) E

/-- Unbounded construction data, grouped to keep generated recursors small.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
structure CoefficientSystemUnboundedImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) where
  evaluation : CoefficientEvaluationImage O ell L V adj S PY PX
  scalar : CoefficientScalarImage O ell L V adj S PY PX evaluation

/-- Normalization means invertibility of the actual adjoint derived transitions.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-coefficient-system-derived-comparison). -/
def IsNormalizedCoefficientSystem
    (P : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (M : DerivedCategory (CoefficientSystem (J := J) O ell)) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m), IsIso
    (((P.scalar h).derivedAdj.homEquiv ((P.evaluation m).obj M)
      ((P.evaluation n).obj M)).symm ((P.transition h).app M))

set_option genInjectivity false in
set_option genSizeOfSpec false in
-- Elaborate the canonical comparison equations against both evaluation packages.
/-- The full derived comparison and its coherence on systems and all derived maps.
Every functor is tied to the ordinary geometric functors or to the universal derived
scalar extension; the two adjunction equations fix the evaluation comparison.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-coefficient-system-derived-comparison). -/
abbrev CoefficientSystemDerivedImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) :=
  CoefficientImageDescentData (gt := CoefficientSystemUnboundedImage O ell L V adj S PY PX)
    PX.evaluation (fun T ↦ T.evaluation.system.direct)
    (fun T n ↦ (T.evaluation.level n).inverse)
    (fun T M ↦ IsIso (T.evaluation.system.adjunction.counit.app M))
    (IsNormalizedCoefficientSystem O ell PY) (IsNormalizedCoefficientSystem O ell PX)

namespace CoefficientSystemDerivedImage
variable {O ell L V adj}
  {S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj}
  {PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)}
  {PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)}

/-- Detection of isomorphisms in the grouped representation.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev detectsIso (T : CoefficientSystemDerivedImage O ell L V adj S PY PX)
    {M N : DerivedCategory (CoefficientSystem (J := K) O ell)} :=
  CoefficientImageDescentData.detectsIso T (M := M) (N := N)

/-- Lower-bound preservation in the grouped representation.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev boundedBelow (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  CoefficientImageDescentData.boundedBelow T

/-- Essential-image and normalization descent in the grouped representation.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev origin (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  CoefficientImageDescentData.origin T

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev system
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.system

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev level
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.level

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev inverseEvaluation
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.inverseEvaluation

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev inverseEvaluation_rep
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.inverseEvaluation_rep

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev directEvaluation
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.directEvaluation

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev counit
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.counit

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev unit
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) :=
  T.construction.evaluation.unit

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev tensor
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.tensor h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev tensor_unit
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.tensor_unit h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev derivedTensor
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.derivedTensor h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev derivedTensor_rep
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.derivedTensor_rep h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev restrictedDirect
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.restrictedDirect h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev restrictedDirect_mate
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.restrictedDirect_mate h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev restrictedInverse
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.restrictedInverse h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev restrictedInverse_mate
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.restrictedInverse_mate h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev inverseTransition
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.inverseTransition h

/-- The original normalized image projection, through the grouped construction data.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: def-pur-coefficient-system-image-data). -/
abbrev directTransition
    (T : CoefficientSystemDerivedImage O ell L V adj S PY PX) {m n : ℕ} (h : n ≤ m) :=
  T.construction.scalar.directTransition h

end CoefficientSystemDerivedImage

end SheafOfModules
