/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralSupportFunctorNormalization
public import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlFrameworkOpenExchange

/-! # Normalized Weil open unit and the empty geometric fibre

Source: latest blueprint, chap-The-Deligne-Laumon-theorem-in-general,
lem-zl-morphism-open-closed-reduction.proof.md, Part 2, extension-by-zero sentence;
Stacks 09BN, 09BP and 099N
(blueprint: lem-zl-open-weil-unit-and-empty-fibre).

The adjunction-transpose equation fixes the comparison as an actual mate. The
integral unit is normalized by the published Roos realization and ordinary open
adjunction. Rationalization and common-stage compatibility concern those maps.
-/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  WeilConjectures.rationalDerivedPullback
  WeilConjectures.constructibleIntegralPullback
  WeilConjectures.integralPullbackScalarComparison
  WeilConjectures.rationalPullbackScalarComparison

universe u v uA uB vA vB uA' uB' vA' vB'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlOpenUnit

/-- The normalized equation and its adjunction transpose, with invertible open unit.
These are clauses about specified functors, not alternative coefficient categories.
Source: Part 2, normalized open unit; Stacks 03DI, 09BN
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
structure OpenData {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    (J : A ⥤ B) (P : B ⥤ A) (GU : A ⥤ A) (GX : B ⥤ B)
    (alpha : P ⋙ GU ≅ GX ⋙ P) where
  adj : J ⊣ P
  unit_iso : IsIso adj.unit
  beta : J ⋙ GX ≅ GU ⋙ J
  normalized : ∀ K : A,
    GU.map (adj.unit.app K) ≫ alpha.hom.app (J.obj K) ≫ P.map (beta.hom.app K) =
      adj.unit.app (GU.obj K)
  mate : ∀ K : A,
    beta.inv.app K = (adj.homEquiv (GU.obj K) (GX.obj (J.obj K))).symm
      (GU.map (adj.unit.app K) ≫ alpha.hom.app (J.obj K))

/-- Coefficient compatibility of the actual unit and beta; inversion gives the same
square for inverse units. All four edge comparisons are the specified scalar maps.
Source: Part 2; proposition-six-operations-change-coefficients
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def ScalarLaws
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
    {J : A ⥤ B} {P : B ⥤ A} {GU : A ⥤ A} {GX : B ⥤ B}
    {J' : A' ⥤ B'} {P' : B' ⥤ A'} {GU' : A' ⥤ A'} {GX' : B' ⥤ B'}
    {alpha : P ⋙ GU ≅ GX ⋙ P} {alpha' : P' ⋙ GU' ≅ GX' ⋙ P'}
    (N : OpenData J P GU GX alpha) (N' : OpenData J' P' GU' GX' alpha')
    (TU : A ⥤ A') (TX : B ⥤ B')
    (b : J ⋙ TX ≅ TU ⋙ J') (a : P ⋙ TU ≅ TX ⋙ P')
    (gU : GU ⋙ TU ≅ TU ⋙ GU') (gX : GX ⋙ TX ≅ TX ⋙ GX') : Prop :=
  (∀ K : A,
    TU.map (N.adj.unit.app K) ≫ a.hom.app (J.obj K) ≫ P'.map (b.hom.app K) =
      N'.adj.unit.app (TU.obj K)) ∧
  (∀ K : A,
    TX.map (N.beta.hom.app K) ≫ b.hom.app (GU.obj K) ≫ J'.map (gU.hom.app K) =
      gX.hom.app (J.obj K) ≫ GX'.map (b.hom.app K) ≫ N'.beta.hom.app (TU.obj K))

/-- Transport a scalar square through fixed identifications of its two transitions.
Source: coefficient passage (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def transportScalarSquare
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
    (P : B ⥤ A) (P' : B' ⥤ A')
    {TU SU : A ⥤ A'} {TX SX : B ⥤ B'}
    (eU : TU ≅ SU) (eX : TX ≅ SX) (c : P ⋙ SU ≅ SX ⋙ P') :
    P ⋙ TU ≅ TX ⋙ P' :=
  Functor.isoWhiskerLeft P eU ≪≫ c ≪≫ Functor.isoWhiskerRight eX.symm P'

attribute [local irreducible] transportScalarSquare

/-- Change the names of the finite operations in a fixed coefficient square.
Source: coefficient passage (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def transportOperationSquare
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
    {J J₀ : A ⥤ B} {J' J₀' : A' ⥤ B'} (TU : A ⥤ A') (TX : B ⥤ B')
    (hJ : J = J₀) (hJ' : J' = J₀') (b : J ⋙ TX ≅ TU ⋙ J') :
    J₀ ⋙ TX ≅ TU ⋙ J₀' :=
  (eqToIso (congrArg (fun F ↦ F ⋙ TX) hJ)).symm ≪≫ b ≪≫
    eqToIso (congrArg (fun F ↦ TU ⋙ F) hJ')

/-- Change the finite operation name in its fixed inclusion comparison.
Source: coefficient passage (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def transportInclusionSquare
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
    {J J₀ : A ⥤ B} (J' : A' ⥤ B') (TU : A ⥤ A') (TX : B ⥤ B')
    (hJ : J = J₀) (b : J ⋙ TX ≅ TU ⋙ J') : J₀ ⋙ TX ≅ TU ⋙ J' :=
  (eqToIso (congrArg (fun F ↦ F ⋙ TX) hJ)).symm ≪≫ b

attribute [local irreducible] transportOperationSquare transportInclusionSquare
  operationStageTransitionIso

section RationalComposition
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
open scoped TensorProduct

attribute [local semireducible] rationalDerivedPullback

private theorem pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pullback_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K J : sfIntegralConstructibleCategory l E Y) (a : K ⟶ J)
    (b : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((rationalDerivedPullback l E f).map
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E f).map a) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K J a b

private theorem composition_heq {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    HEq (localPullbackComposition l E h k K).hom
      ((sfRationalConstructibleLocalization l E X).map
        (((integralPullbackComposition l E).choose h k).hom.app K.obj)) := by
  simp only [localPullbackComposition, localPullbackObjectIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_map, ← Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem map_heq {C T : Type*} [Category C] [Category T]
    (Q : C ⥤ T) {U V U' V' : C} (hu : U = U') (hv : V = V')
    {f : U ⟶ V} {f' : U' ⟶ V'} (hf : HEq f f') : HEq (Q.map f) (Q.map f') := by
  subst U'
  subst V'
  exact heq_of_eq (congrArg Q.map (eq_of_heq hf))

private theorem tensor_natural {R : Type*} [CommRing R] {p : R}
    {C T : Type*} [Category C] [Preadditive C] [Linear R C]
    [Category T] [Preadditive T] [Linear R T]
    (F G : ScalarLocalization R C p ⥤ ScalarLocalization R T p)
    [F.Additive] [G.Additive]
    (e : ∀ K, F.obj K ⟶ G.obj K)
    (he : ∀ (K L : C) (a : K ⟶ L) (b : Localization.Away p),
      e ⟨K⟩ ≫ G.map (b ⊗ₜ[R] a) = F.map (b ⊗ₜ[R] a) ≫ e ⟨L⟩)
    (K L : ScalarLocalization R C p) (v : K ⟶ L) :
    e K ≫ G.map v = F.map v ≫ e L := by
  induction v using TensorProduct.inductionOn with
  | tmul b a => exact he K.obj L.obj a b
  | add a b ha hb =>
    rw [F.map_add, G.map_add, Preadditive.comp_add, Preadditive.add_comp, ha, hb]

private theorem raw_natural {R : Type*} [CommRing R] {p : R}
    {C T : Type*} [Category C] [Preadditive C] [Linear R C]
    [Category T] [Preadditive T] [Linear R T]
    (I J : C ⥤ T) (e : I ⟶ J)
    (F G : ScalarLocalization R C p ⥤ ScalarLocalization R T p)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ScalarLocalization.mk (I.obj K.obj))
    (hG : ∀ K, G.obj K = ScalarLocalization.mk (J.obj K.obj))
    (mF : ∀ (K L : C) (a : K ⟶ L) (b : Localization.Away p),
      HEq (F.map (b ⊗ₜ[R] a)) (b ⊗ₜ[R] I.map a))
    (mG : ∀ (K L : C) (a : K ⟶ L) (b : Localization.Away p),
      HEq (G.map (b ⊗ₜ[R] a)) (b ⊗ₜ[R] J.map a))
    (c : ∀ K, F.obj K ⟶ G.obj K)
    (hc : ∀ K, HEq (c K) ((1 : Localization.Away p) ⊗ₜ[R] e.app K.obj))
    (K L : ScalarLocalization R C p) (a : K ⟶ L) :
    c K ≫ G.map a = F.map a ≫ c L := by
  apply tensor_natural F G c _ K L a
  intro K L a b
  apply eq_of_heq
  apply (heq_comp (hF ⟨K⟩) (hG ⟨K⟩) (hG ⟨L⟩) (hc ⟨K⟩) (mG K L a b)).trans
  apply HEq.trans _
    (heq_comp (hF ⟨K⟩) (hF ⟨L⟩) (hG ⟨L⟩) (mF K L a b) (hc ⟨L⟩)).symm
  change HEq (ScalarLocalization.composition _ _ _ _ _ _
    (b ⊗ₜ[R] _) (1 ⊗ₜ[R] _))
    (ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[R] _) (b ⊗ₜ[R] _))
  simp only [ScalarLocalization.composition_tmul, mul_one, one_mul]
  exact heq_of_eq (congrArg (fun f ↦ b ⊗ₜ[R] f) (e.naturality a).symm)

private theorem composition_natural {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K J : sfRationalConstructibleCategory l E Z) (v : K ⟶ J) :
    (localPullbackComposition l E h k K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E k).map v) =
      (rationalDerivedPullback l E (h ≫ k)).map v ≫
        (localPullbackComposition l E h k J).hom := by
  let _ : (rationalDerivedPullback l E h).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E k).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E k).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E (h ≫ k)).Additive :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E (h ≫ k)).exists.choose_spec.1
  refine raw_natural (constructibleIntegralPullback l E (h ≫ k))
    (constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h)
    ((integralPullbackComposition l E).choose h k).hom
    (rationalDerivedPullback l E (h ≫ k))
    (rationalDerivedPullback l E k ⋙ rationalDerivedPullback l E h)
    (pullback_obj l E (h ≫ k)) ?_ (pullback_tmul l E (h ≫ k)) ?_
    (fun K ↦ (localPullbackComposition l E h k K).hom) ?_ K J v
  · intro K
    dsimp only [Functor.comp_obj]
    rw [pullback_obj, pullback_obj]
    rfl
  · intro K J a b
    exact (map_heq _ (pullback_obj l E k ⟨K⟩) (pullback_obj l E k ⟨J⟩)
      (pullback_tmul l E k K J a b)).trans
        (pullback_tmul l E h _ _ ((constructibleIntegralPullback l E k).map a) b)
  · intro K
    simpa only [sfRationalConstructibleLocalization, ScalarLocalization.localization]
      using composition_heq l E h k K

private theorem comparison_inv_natural {C T : Type*} [Category C] [Category T]
    {F G : C ⥤ T} (e : ∀ K, F.obj K ≅ G.obj K)
    (he : ∀ {K J} (v : K ⟶ J), (e K).hom ≫ G.map v = F.map v ≫ (e J).hom)
    {K J : C} (v : K ⟶ J) :
    (e K).inv ≫ F.map v = G.map v ≫ (e J).inv := by
  apply (cancel_epi (e K).hom).1
  simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg (fun f ↦ f ≫ (e J).inv) (he v).symm

private theorem equality_natural {C T : Type*} [Category C] [Category T]
    {I : Type*} (F : I → C ⥤ T) {i j : I} (e : i = j) {M J : C} (v : M ⟶ J) :
    eqToHom (congrArg (fun i ↦ (F i).obj M) e) ≫ (F j).map v =
      (F i).map v ≫ eqToHom (congrArg (fun i ↦ (F i).obj J) e) := by
  cases e
  simp

private theorem square_natural {U X : Scheme.{u}} (j : U ⟶ X)
    (gU : U ⟶ U) (gX : X ⟶ X) (h : gU ≫ j = j ≫ gX)
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    {K L : sfRationalConstructibleCategory l E X} (a : K ⟶ L) :
    (rationalDerivedPullback l E gU).map ((rationalDerivedPullback l E j).map a) ≫
        ((localPullbackComposition l E gU j L).symm ≪≫
          eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj L) h) ≪≫
          localPullbackComposition l E j gX L).hom =
      ((localPullbackComposition l E gU j K).symm ≪≫
          eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj K) h) ≪≫
          localPullbackComposition l E j gX K).hom ≫
        (rationalDerivedPullback l E j).map ((rationalDerivedPullback l E gX).map a) := by
  have ha := comparison_inv_natural
    (F := rationalDerivedPullback l E (gU ≫ j))
    (G := rationalDerivedPullback l E j ⋙ rationalDerivedPullback l E gU)
    (localPullbackComposition l E gU j)
    (fun v ↦ composition_natural l E gU j _ _ v) a
  have hb := composition_natural l E j gX K L a
  have he := @equality_natural
    (sfRationalConstructibleCategory l E X) (sfRationalConstructibleCategory l E U)
    _ _ (U ⟶ X) (fun f ↦ rationalDerivedPullback l E f) _ _ h K L a
  dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  symm
  simp only [Category.assoc, hb, reassoc_of% he]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫
      eqToHom (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj L) h) ≫
      (localPullbackComposition l E j gX L).hom) ha

end RationalComposition

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X₀ U₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

/-- The inherited open-immersion structure on the existing geometric-fibre map.
Source: Stacks 01JU (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance fiberOpen : IsOpenImmersion (zlFiberMap D j₀) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

/-- The canonical finite-type structure on a geometric fibre.
Source: Stacks 01T3 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance fiberFiniteType : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  MorphismProperty.pullback_snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) inferInstance

/-- The canonical quasi-compact structure on a geometric fibre.
Source: Stacks 01KJ (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance fiberQuasiCompact : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  MorphismProperty.pullback_snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) inferInstance

/-- Finite type on the explicit Over.pullback presentation, before folding geometricFiber.
Source: geometric base change (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance overPullFiniteType {B T : Scheme.{u}} (f : T ⟶ B) (Y : Over B)
    [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (((Over.pullback f).obj Y).left ↘ T) :=
  MorphismProperty.pullback_snd Y.hom f inferInstance

/-- Quasi-compactness on the explicit Over.pullback presentation.
Source: geometric base change (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance overPullQuasiCompact {B T : Scheme.{u}} (f : T ⟶ B) (Y : Over B)
    [QuasiCompact Y.hom] : QuasiCompact (((Over.pullback f).obj Y).left ↘ T) :=
  MorphismProperty.pullback_snd Y.hom f inferInstance

/-- The fibre morphism is over k by the actual second projection.
Source: base change convention (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance fiberOver : (zlFiberMap D j₀).IsOver (Spec (.of D.k)) :=
  ⟨Over.w ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀)⟩

/-- Every open in the finite-type geometric target is quasi-compact.
Source: Stacks 01T1 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
instance fiberMapQuasiCompact : QuasiCompact (zlFiberMap D j₀) :=
  letI : IsLocallyNoetherian (D.geometricFiber U₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber U₀).left ↘ Spec (.of D.k))
  letI : CompactSpace (D.geometricFiber U₀).left :=
    QuasiCompact.compactSpace_of_compactSpace ((D.geometricFiber U₀).left ↘ Spec (.of D.k))
  letI : IsNoetherian (D.geometricFiber U₀).left := {}
  @quasiCompact_of_noetherianSpace_source (D.geometricFiber U₀).left
    (D.geometricFiber X₀).left inferInstance (zlFiberMap D j₀)

/-- Integral compact support for the compactification (j,id), with its recorded action.
Only the geometric Noetherian instance is supplied here.
Source: Part 2; compact-support definition
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def integralJ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left ⥤
      sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left :=
  letI : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber X₀).left ↘ Spec (.of D.k))
  sfCompactSupportFiniteIntegralFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion (zlFiberMap D j₀)) E

/-- Rational compact support is the specified raw scalar extension of that action.
Source: Part 2; compact-support definition
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def rationalJ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    sfRationalConstructibleCategory l E (D.geometricFiber U₀).left ⥤
      sfRationalConstructibleCategory l E (D.geometricFiber X₀).left :=
  letI : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber X₀).left ↘ Spec (.of D.k))
  sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion (zlFiberMap D j₀)) E

/-- The literal normalized coefficient action, with the same open compactification.
Source: Part 2; def-weil-compact-support-coefficient-action
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev Action (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :=
  letI : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber X₀).left ↘ Spec (.of D.k))
  SfCompactSupportCoefficientAction l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
    (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))

/-- Integral pullback with the inherited prime-invertibility structures.
Source: Part 2; recorded integral operations
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev integralP (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ (zlFiberMap D j₀)
    (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)

/-- Integral Frobenius pullback, without a k-linearity hypothesis.
Source: Part 2; recorded integral operations
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev integralG (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ (D.geometricFrobenius X₀).asIso.hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- Rational open restriction, on the recorded coefficient category.
Source: Part 2 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev rationalP (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (zlFiberMap D j₀)
    (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)

/-- The integral square is the actual pullback-composition comparison.
Source: Part 2; Stacks 099N(5)
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def integralAlpha (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    integralP D l hl X₀ U₀ j₀ E ⋙ integralG D l hl U₀ E ≅
      integralG D l hl X₀ E ⋙ integralP D l hl X₀ U₀ j₀ E :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  (zlIntegralPullComp l E (D.geometricFrobenius U₀).asIso.hom (zlFiberMap D j₀)).symm ≪≫
    eqToIso (congrArg
      (fun f : (D.geometricFiber U₀).left ⟶ (D.geometricFiber X₀).left ↦
        @constructibleIntegralPullback l _ E _ _ _ _ _ f
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀))
      (zlFrobenius_naturality D j₀)) ≪≫
      zlIntegralPullComp l E (zlFiberMap D j₀) (D.geometricFrobenius X₀).asIso.hom

/-- Component of the rational pullback-composition square, localized from the
specified integral compositors.
Source: Part 2; local Frobenius composition convention
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def rationalAlphaComponent (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (sfWeilFrobeniusPullback D l hl U₀ E).obj
        ((rationalP D l hl X₀ U₀ j₀ E).obj K) ≅
      (rationalP D l hl X₀ U₀ j₀ E).obj
        ((sfWeilFrobeniusPullback D l hl X₀ E).obj K) :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  (localPullbackComposition l E (D.geometricFrobenius U₀).asIso.hom (zlFiberMap D j₀) K).symm ≪≫
    eqToIso (congrArg
      (fun f : (D.geometricFiber U₀).left ⟶ (D.geometricFiber X₀).left ↦
        (@rationalDerivedPullback l _ E _ _ _ _ _ f
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)).obj K)
      (zlFrobenius_naturality D j₀)) ≪≫
    localPullbackComposition l E (zlFiberMap D j₀) (D.geometricFrobenius X₀).asIso.hom K

set_option linter.unusedSectionVars false in
/-- Naturality of the specified comparison alpha.
Source: Part 2; Stacks 099N(5)
(blueprint: lem-zl-open-weil-unit-and-empty-fibre).
Proof: integral pullback composition is a natural isomorphism. Localizing its
components preserves its naturality on integral arrows and on pure Hom tensors;
additivity gives all arrows. The equality comparison is natural by equality
elimination. Compose these three naturality squares. -/
theorem rationalAlpha_natural (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {K L : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left} (a : K ⟶ L) :
    (sfWeilFrobeniusPullback D l hl U₀ E).map
        ((rationalP D l hl X₀ U₀ j₀ E).map a) ≫
        (rationalAlphaComponent D l hl X₀ U₀ j₀ E L).hom =
      (rationalAlphaComponent D l hl X₀ U₀ j₀ E K).hom ≫
        (rationalP D l hl X₀ U₀ j₀ E).map
          ((sfWeilFrobeniusPullback D l hl X₀ E).map a) := by
  simpa only [rationalAlphaComponent, rationalP, sfWeilFrobeniusPullback,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom] using
    @square_natural l _ E _ _ _ (D.geometricFiber U₀).left (D.geometricFiber X₀).left
      (zlFiberMap D j₀) (D.geometricFrobenius U₀).asIso.hom (D.geometricFrobenius X₀).asIso.hom
      (zlFrobenius_naturality D j₀) (sfWeilPrimeInvertible D l hl U₀)
      (sfWeilPrimeInvertible D l hl X₀) K L a

/-- Alpha with the normalized components and their naturality.
Source: Part 2 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def rationalAlpha (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    rationalP D l hl X₀ U₀ j₀ E ⋙ sfWeilFrobeniusPullback D l hl U₀ E ≅
      sfWeilFrobeniusPullback D l hl X₀ E ⋙ rationalP D l hl X₀ U₀ j₀ E :=
  NatIso.ofComponents (rationalAlphaComponent D l hl X₀ U₀ j₀ E)
    (fun a ↦ rationalAlpha_natural D l hl X₀ U₀ j₀ E a)

attribute [local irreducible] integralAlpha rationalAlpha rationalAlphaComponent
  sfWeilFrobeniusPullback

/-- The integral clauses concern the recorded functor and the actual completed pullback.
Source: Part 2 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev IntegralData (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  OpenData (integralJ D l hl X₀ U₀ j₀ E) (integralP D l hl X₀ U₀ j₀ E)
    (integralG D l hl U₀ E) (integralG D l hl X₀ E)
      (integralAlpha D l hl X₀ U₀ j₀ E)

/-- The rational clauses concern the raw localized functor.
Source: Part 2 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev RationalData (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  OpenData (rationalJ D l hl X₀ U₀ j₀ E) (rationalP D l hl X₀ U₀ j₀ E)
    (sfWeilFrobeniusPullback D l hl U₀ E) (sfWeilFrobeniusPullback D l hl X₀ E)
      (rationalAlpha D l hl X₀ U₀ j₀ E)

/-- The published Roos-normalized identification with ordinary extension by zero.
The proper identity factor is removed using its section-normalized derived comparison.
Source: Part 2; Stacks 09BN, 099N
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def integralOpenRealization (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    integralJ D l hl X₀ U₀ j₀ E ⋙ (sfIntegralConstructible l E (D.geometricFiber X₀).left).ι ≅
      (sfIntegralConstructible l E (D.geometricFiber U₀).left).ι ⋙
        IntegralSupportNormalization.ordinaryOpen l E (zlFiberMap D j₀) :=
  letI : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber X₀).left ↘ Spec (.of D.k))
  (sfQcqsCompactSupportRealization l E D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))).symm ≪≫
      Functor.isoWhiskerLeft (sfIntegralConstructible l E (D.geometricFiber U₀).left).ι
        (IntegralSupportNormalization.openIdentity l E (zlFiberMap D j₀))

/-- The integral adjunction unit is exactly the ordinary open unit under the actual
quotient-unit-normalized restriction comparison and the recorded support realization.
Source: Part 2; Stacks 09BN, 099N(5)
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def IntegralUnitNormalization (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (N : IntegralData D l hl X₀ U₀ j₀ E) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  letI : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.geometricFiber X₀).left ↘ Spec (.of D.k))
  ∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left,
    (N.adj.unit.app K).hom ≫
        (ZlFrameworkPbc.frameworkOpenPullRealization l E (zlFiberMap D j₀)).inv.app
          ((integralJ D l hl X₀ U₀ j₀ E).obj K) ≫
        (PurCompactSupport.pull (PurCompactSupport.completed l E) (zlFiberMap D j₀)).map
          ((integralOpenRealization D l hl X₀ U₀ j₀ E).hom.app K) =
      (PurCompactSupport.openDerivedAdjunction (PurCompactSupport.completed l E)
        (zlFiberMap D j₀)).unit.app K.obj

/-- Integral-to-rational passage retains the actual unit and beta, including inverses.
Source: Part 2, coefficient passage
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def Rationalization (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (N : IntegralData D l hl X₀ U₀ j₀ E) (R : RationalData D l hl X₀ U₀ j₀ E) : Prop :=
  (∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left,
    HEq (R.adj.unit.app ((sfRationalConstructibleLocalization l E
      (D.geometricFiber U₀).left).obj K))
      ((sfRationalConstructibleLocalization l E (D.geometricFiber U₀).left).map
        (N.adj.unit.app K))) ∧
  (∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left,
    HEq (R.beta.hom.app ((sfRationalConstructibleLocalization l E
      (D.geometricFiber U₀).left).obj K))
      ((sfRationalConstructibleLocalization l E (D.geometricFiber X₀).left).map
        (N.beta.hom.app K)))

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The specified rational pullback scalar square with stage transition notation.
This is just conjugation by the recorded transition identification.
Source: coefficient passage, proposition-six-operations-change-coefficients
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def rationalStageScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω E) f ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h ⋙
        rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient l Ω L) f :=
  transportScalarSquare
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f)
    (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
    (operationStageTransitionIso l Ω X E L h)
    (operationStageTransitionIso l Ω Y E L h)
    (rationalPullbackScalarComparison l (AlgebraicallyClosedCoefficients.Coefficient l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) f)

/-- Frobenius scalar change with the recorded stage-transition functors.
Source: coefficient passage (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def rationalFrobeniusStageScalar
    (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    sfWeilFrobeniusPullback D l hl X₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber X₀).left).T h ≅
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber X₀).left).T h ⋙
      sfWeilFrobeniusPullback D l hl X₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) := by
  unfold sfWeilFrobeniusPullback
  exact @rationalStageScalar l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).asIso.hom
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀) E L h

attribute [local irreducible] rationalFrobeniusStageScalar

/-- The common-stage clauses use precisely the specified action on literal pairs.
Source: Part 2 (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
abbrev CommonData (S : Action D l hl X₀ U₀ j₀ Ω) :=
  OpenData S.system.functor (zlPull D l hl Ω j₀)
    (sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (zlFrobeniusSquare D l hl Ω j₀)

/-- Stalk vanishing in every coefficient category, including arbitrary complexes
and all coefficient cohomology degrees of the specified point fibre.
The natural zero comparison is unique since each target object is zero.
Source: Part 2, outside-open sentence; Stacks 099N
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def EmptyFibre (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (_Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    frobeniusPointPrimeInvertible D l hl
  ∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left),
    Disjoint (Set.range x) (Set.range (zlFiberMap D j₀)) →
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@constructibleIntegralPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((integralJ D l hl X₀ U₀ j₀ E).obj K)).obj) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@rationalDerivedPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
          ((rationalJ D l hl X₀ U₀ j₀ E).obj K))) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left,
        IsZero ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj
            (S.system.functor.obj K))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfWeilComplex D l hl U₀ E) (a : ℤ),
        IsZero ((DerivedCategory.coefficientFdCohomology E a).obj
          (localPointComplex l E D hl X₀
            ((IsoAlgebra.mapOfNatIso (R E).beta).obj K) x))) ∧
      (∀ (K : sfCommonStageWeilComplex D l hl U₀ Ω) (a : ℤ),
        let N := (@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl)
          (sfWeilPrimeInvertible D l hl X₀)).obj (S.system.functor.obj K.carrier)
        IsZero ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) a).obj
          ((pointRationalFibre D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage)).obj N.obj)))

attribute [local irreducible] rationalStageScalar sfIntegralConstructible

/-- Actual scalar-unit and Frobenius-comparison equations at every pair of finite
coefficient fields, using the action's specified integral and rational comparisons.
Source: Part 2, common finite-field coefficient passage
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def FiniteScalarCompatibility (S : Action D l hl X₀ U₀ j₀ Ω)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      IntegralData D l hl X₀ U₀ j₀ E)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L),
    ∃ (a : integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ⋙
          integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
      (gU : integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber U₀).left E L h ⋙
          integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
      (gX : integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
            (D.geometricFiber X₀).left E L h ⋙
          integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω L)),
      (∀ K, a.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _ (zlFiberMap D j₀)
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) K) ∧
      (∀ K, gU.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _
        (D.geometricFrobenius U₀).asIso.hom
        (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀) K) ∧
      (∀ K, gX.app K = @integralPullbackScalarComparison l _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω E) _ _ _
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L) _ _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) _ _
        (D.geometricFrobenius X₀).asIso.hom
        (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀) K) ∧
      ScalarLaws
        (J := integralJ D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (P := integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GU := integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GX := integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (alpha := integralAlpha D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (J' := integralJ D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (P' := integralP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (GU' := integralG D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (GX' := integralG D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (alpha' := integralAlpha D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (I (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
        (I (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
        (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
          (D.geometricFiber U₀).left E L h)
        (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω
          (D.geometricFiber X₀).left E L h) (S.integralBeta h) a gU gX ∧
      ScalarLaws
        (J := rationalJ D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (P := rationalP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GU := sfWeilFrobeniusPullback D l hl U₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GX := sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (alpha := rationalAlpha D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (J' := rationalJ D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (P' := rationalP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (GU' := sfWeilFrobeniusPullback D l hl U₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (GX' := sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (alpha' := rationalAlpha D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
        (R (AlgebraicallyClosedCoefficients.Coefficient l Ω E))
        (R (AlgebraicallyClosedCoefficients.Coefficient l Ω L))
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber U₀).left).T h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber X₀).left).T h)
        (transportOperationSquare
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber U₀).left).T h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (D.geometricFiber X₀).left).T h)
          (S.finite_eq E) (S.finite_eq L) (S.system.β h))
        (@rationalStageScalar l _ Ω _ _ _ _ _ (zlFiberMap D j₀)
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀) E L h)
        (rationalFrobeniusStageScalar D l hl U₀ Ω E L h)
        (rationalFrobeniusStageScalar D l hl X₀ Ω E L h)

/-- The object equation of the recorded common-stage pullback.
Source: coefficient descent (blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def pullbackStageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).obj K) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
    ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))

/-- Inclusion of every literal finite stage preserves the actual unit and beta.
The pullback edges are the canonical object identifications of the recorded
common-stage construction; the support edge is the given coefficient action.
Source: Part 2, common-stage passage
(blueprint: lem-zl-open-weil-unit-and-empty-fibre). -/
def CommonStageCompatibility (S : Action D l hl X₀ U₀ j₀ Ω)
    (R : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      RationalData D l hl X₀ U₀ j₀ E)
    (Q : CommonData D l hl X₀ U₀ j₀ Ω S) : Prop :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (l : (D.geometricFiber U₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl U₀
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible D l hl X₀
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : rationalP D l hl X₀ U₀ j₀ (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ zlPull D l hl Ω j₀)
      (gU : sfWeilFrobeniusPullback D l hl U₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
      (gX : sfWeilFrobeniusPullback D l hl X₀
            (AlgebraicallyClosedCoefficients.Coefficient l Ω E) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙
          sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω),
      (∀ K : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (D.geometricFiber X₀).left, HEq (a.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (zlFiberMap D j₀)
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl X₀)
          E K).inv) ∧
      (∀ K : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (D.geometricFiber U₀).left, HEq (gU.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius U₀).asIso.hom
          (sfWeilPrimeInvertible D l hl U₀) (sfWeilPrimeInvertible D l hl U₀)
          E K).inv) ∧
      (∀ K : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (D.geometricFiber X₀).left, HEq (gX.hom.app K)
        (@pullbackStageIso l _ Ω _ _ _ _ _ (D.geometricFrobenius X₀).asIso.hom
          (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)
          E K).inv) ∧
      ScalarLaws
        (J := rationalJ D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (P := rationalP D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GU := sfWeilFrobeniusPullback D l hl U₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (GX := sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (alpha := rationalAlpha D l hl X₀ U₀ j₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
        (J' := S.system.functor) (P' := zlPull D l hl Ω j₀)
        (GU' := sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
        (GX' := sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
        (alpha' := zlFrobeniusSquare D l hl Ω j₀)
        (R (AlgebraicallyClosedCoefficients.Coefficient l Ω E)) Q
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        (GeneralAlgebraicallyClosedCoefficients.inclusion E)
        (transportInclusionSquare S.system.functor
          (GeneralAlgebraicallyClosedCoefficients.inclusion E)
          (GeneralAlgebraicallyClosedCoefficients.inclusion E)
          (S.finite_eq E) (S.system.ιCompFunctorIso E).symm) a gU gX

end WeilConjectures.ZlOpenUnit
