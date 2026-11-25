/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
public import WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualNormalization

/-! # Etale presentations and scalar transport for a supplied algebraic tower

Source: Stacks Project, Tags 09C6, 09BV and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The lifted finite quotient ring at a level.
Source: Stacks Tag 09C6, with coefficient universes made explicit.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
abbrev finitePerfectAdicIsomorphismRing {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))

/-- Consecutive quotient homomorphism in the lifted coefficient universe.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
def finitePerfectAdicIsomorphismQuotient {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    finitePerfectAdicIsomorphismRing d (n + 1) →+* finitePerfectAdicIsomorphismRing d n :=
  (ULift.ringEquiv : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) ≃+*
    (A ⧸ d.ideal ^ (n + 1))).symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc d.ideal (n + 1)).comp
      (ULift.ringEquiv : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) ≃+*
        (A ⧸ d.ideal ^ (n + 1 + 1))).toRingHom)

/-- A finite-coefficient etale complex on a chart.
Source: Stacks Tags 09AL and 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
abbrev finitePerfectAdicIsomorphismComplex {A : Type t} [CommRing A]
    (Y : Scheme.{t}) (d : AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf Y.smallEtaleTopology
    (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n)))

/-- Etale finite-level data before sheafification and section evaluation.

The presheaf maps have their normalization equation only on etale generators.
The scalar-forgetting realization functors, coefficient interchange and two level
comparisons have their actual normalization identities. Transport of raw isomorphisms
and preservation of a supplied raw square are then constructed and proved below. Neither
evaluation on pro-etale sheaf sections nor its reduction square is contained in the datum.
Source: Stacks Tags 09C6, 09BV and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
structure FinitePerfectAdicIsomorphismPresentation
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) where
  C : ∀ n : ℕ, finitePerfectAdicIsomorphismComplex V.left d n
  K : ∀ n : ℕ, finitePerfectAdicIsomorphismComplex V.left d n
  boundedC : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (C n))
  lisseC : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (C n))
  boundedK : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (K n))
  lisseK : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) i).obj (K n))
  stalk : ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ V.left), Nonempty
      ((pointSmallEtale x).sheafFiber.obj (derivedLocalIsomorphismSheaf (C n) (K n)))
  dC : ∀ n : ℕ, C (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (finitePerfectAdicIsomorphismQuotient d n)).obj (C n)
  dK : ∀ n : ℕ, K (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (finitePerfectAdicIsomorphismQuotient d n)).obj (K n)
  p : ∀ n : ℕ, derivedLocalIsomorphismPresheaf (C (n + 1)) (K (n + 1)) ⟶
    derivedLocalIsomorphismPresheaf (C n) (K n)
  normalized : ∀ (n : ℕ) (U : V.left.Etale)
    (e : (localIsomorphismRestriction V.left
        (finitePerfectAdicIsomorphismRing d (n + 1)) U).obj (C (n + 1)) ≅
      (localIsomorphismRestriction V.left
        (finitePerfectAdicIsomorphismRing d (n + 1)) U).obj (K (n + 1))),
    e.hom ≫ etaleIsomorphismNormalizationArrow V.left
        (finitePerfectAdicIsomorphismQuotient d n) (dK n) U =
      etaleIsomorphismNormalizationArrow V.left
        (finitePerfectAdicIsomorphismQuotient d n) (dC n) U ≫
      (normalizationRestrict U.left.smallEtaleTopology
        (finitePerfectAdicIsomorphismQuotient d n)).map ((p n).app (op U) e).hom
  realization : ∀ (U : V.left.ProEt) (W : X.ProEt),
    (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (finitePerfectAdicIsomorphismRing d n))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W))
  scalar : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    normalizationRestrict (ProEt.topology U.left)
        (finitePerfectAdicIsomorphismQuotient d n) ⋙ realization U W f (n + 1) ≅
      realization U W f n
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (C n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (finitePerfectAdicIsomorphismQuotient d n) (dK n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
  model_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (finitePerfectAdicIsomorphismQuotient d n) (dC n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (C n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op

private theorem conjugate_normalization_square
    {CR CS D : Type*} [Category CR] [Category CS] [Category D]
    (H : CS ⥤ CR) (F : CR ⥤ D) (G : CS ⥤ D) (α : H ⋙ F ≅ G)
    {C K : CR} {C' K' : CS} (dC : C ⟶ H.obj C') (dK : K ⟶ H.obj K')
    {A A' B B' : D} (a : A ⟶ A') (b : B ⟶ B')
    (actual : F.obj K ≅ A) (actual' : G.obj K' ≅ A')
    (model : F.obj C ≅ B) (model' : G.obj C' ≅ B')
    (ha : F.map dK ≫ α.hom.app K' ≫ actual'.hom = actual.hom ≫ a)
    (hb : F.map dC ≫ α.hom.app C' ≫ model'.hom = model.hom ≫ b)
    (e : C ≅ K) (e' : C' ≅ K')
    (he : e.hom ≫ dK = dC ≫ H.map e'.hom) :
    b ≫ (model'.symm ≪≫ G.mapIso e' ≪≫ actual').hom =
      (model.symm ≪≫ F.mapIso e ≪≫ actual).hom ≫ a := by
  apply (cancel_epi model.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Category.assoc model.hom b, ← hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← α.hom.naturality_assoc e'.hom]
  change F.map dC ≫ F.map (H.map e'.hom) ≫ α.hom.app K' ≫ actual'.hom = _
  rw [← F.map_comp_assoc, ← he, F.map_comp, Category.assoc, ha]

/-- Apply the scalar-forgetting realization and the two specified level comparisons.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
def FinitePerfectAdicIsomorphismPresentation.transport
    {X : Scheme.{t}} {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    {M : DerivedCategory (CompletedAdicModules X d)} {V : X.Etale}
    {T : FinitePerfectAdicAlgebraTower d}
    (D : FinitePerfectAdicIsomorphismPresentation X d M V T)
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (e : (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.C n) ≅
      (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.K n)) :
    (finitePerfectAdicModelDiagram X d W T).obj (op n) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n) :=
  (D.model U W f n).symm ≪≫ (D.realization U W f n).mapIso e ≪≫ D.actual U W f n

/-- The two normalization identities transport a raw square to the actual diagrams.
Source: Stacks Tag 09C6; naturality of the coefficient comparison.
(blueprint: def-weil-pbc-finite-perfect-adic-isomorphism-presentation). -/
theorem FinitePerfectAdicIsomorphismPresentation.transport_square
    {X : Scheme.{t}} {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    {M : DerivedCategory (CompletedAdicModules X d)} {V : X.Etale}
    {T : FinitePerfectAdicAlgebraTower d}
    (D : FinitePerfectAdicIsomorphismPresentation X d M V T)
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (e : (localProEtaleComparison U.hom
        (finitePerfectAdicIsomorphismRing d (n + 1))).obj (D.C (n + 1)) ≅
      (localProEtaleComparison U.hom
        (finitePerfectAdicIsomorphismRing d (n + 1))).obj (D.K (n + 1)))
    (e' : (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.C n) ≅
      (localProEtaleComparison U.hom (finitePerfectAdicIsomorphismRing d n)).obj (D.K n))
    (he : e.hom ≫ localProEtaleNormalization U.hom
        (finitePerfectAdicIsomorphismQuotient d n) (D.dK n) =
      localProEtaleNormalization U.hom (finitePerfectAdicIsomorphismQuotient d n) (D.dC n) ≫
        (normalizationRestrict (ProEt.topology U.left)
          (finitePerfectAdicIsomorphismQuotient d n)).map e'.hom) :
    (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op ≫
        (D.transport U W f n e').hom =
      (D.transport U W f (n + 1) e).hom ≫
        (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
          (homOfLE (Nat.le_succ n)).op := by
  exact conjugate_normalization_square _ _ _ (D.scalar U W f n) _ _ _ _
    (D.actual U W f (n + 1)) (D.actual U W f n)
    (D.model U W f (n + 1)) (D.model U W f n)
    (D.actual_normalized U W f n) (D.model_normalized U W f n) e e' he

/-- Descend finite-level models and construct their etale normalization presheaf maps.
This supplies no pro-etale sheaf-section evaluation or evaluated reduction square.

Source: Stacks Project, Tag 09C6, finite quotient descent and normalized algebraic levels;
Tag 09BV, Isom presheaves; Tag 06YY, universal normalization arrows.
(blueprint: lem-weil-pbc-finite-perfect-adic-isomorphism-presentation).

Proof: descend the finite quotient complexes restricted to V by finite-ring derived
comparison. Lift the supplied perfect algebraic levels to the coefficient universe and
apply the exact constant functor to obtain C; use the descended quotient levels for K.
Separate local markings identify K with C on covering sieves. The perfect levels over
finite rings are bounded with finite cohomology; their exact constant realizations and
local identifications give boundedness and lisse cohomology for C and K. Every geometric
point lifts to each covering sieve, whose marking gives a local Isom section and hence
an inhabited stalk of its sheafification. Descend the actual consecutive quotient maps
by full faithfulness. The algebraic normalization and balancing of the strict derived
quotient tower make both consecutive arrows universal for scalar restriction. On each
etale slice, extend an isomorphism by scalars and conjugate by these two universal arrows.
Uniqueness of universal factorizations makes this construction natural in the slice and
proves the generator normalization square; this gives p. For transport, compare the
pulled descended K with the actual finite quotient, and the pulled constant C with the
realization of the supplied algebraic level. Forget quotient scalars, conjugate by these
comparisons, and apply exact slice restriction along W to U. The coefficient compatibility
of φ gives the two normalization identities relating these realized arrows to the
specified strict tower and model transitions. Naturality of the coefficient comparison
then proves transport_square separately, rather than assuming it in the presentation.
There is no inverse limit or simultaneous marking choice. The zero ring and empty chart
use the same constructions. -/
theorem finitePerfectAdic_isomorphism_presentation
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    Nonempty (FinitePerfectAdicIsomorphismPresentation X d M V T) := by
  classical
  obtain ⟨E⟩ := finitePerfectAdic_actual_normalization X d φ hφ hcompat M V T hperfect hmark
  have h (n : ℕ) := etaleUniversalNormalization_presheaf V.left
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
    (finitePerfectAdicEtaleConstant V.left T (n + 1)) (E.K (n + 1))
    (finitePerfectAdicEtaleConstant V.left T n) (E.K n)
    (finitePerfectAdicEtaleConstantTransition V.left T n) (E.dK n)
    (finitePerfectAdicEtaleConstant_normalization V.left T n) (E.universalK n)
  choose p hp using h
  exact ⟨{
    C := finitePerfectAdicEtaleConstant V.left T
    K := E.K
    boundedC := fun n ↦ (finitePerfectAdicEtaleConstant_cohomology
      V.left T n (hperfect n)).1
    lisseC := fun n ↦ (finitePerfectAdicEtaleConstant_cohomology
      V.left T n (hperfect n)).2
    boundedK := E.boundedK
    lisseK := E.lisseK
    stalk := E.stalk
    dC := finitePerfectAdicEtaleConstantTransition V.left T
    dK := E.dK
    p := p
    normalized := hp
    realization := E.realization
    scalar := E.scalar
    actual := E.actual
    model := E.model
    actual_normalized := E.actual_normalized
    model_normalized := E.model_normalized }⟩

end AlgebraicGeometry.Scheme
