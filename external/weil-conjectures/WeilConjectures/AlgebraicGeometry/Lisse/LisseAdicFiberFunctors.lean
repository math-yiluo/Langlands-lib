/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberComparisons
public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientFiberEndomorphisms
public import WeilConjectures.CategoryTheory.Pseudofunctor.NormalizedFibreComparisons
import WeilConjectures.CategoryTheory.Sites.Point.Linear

/-!
# The fibre functors of lisse adic sheaves

The objects are the recorded integral, rational and algebraic fibres.

## References

* Deligne, Weil II (1.1.1) b)-d), SGA 5 VI
* Weil II (1.1.1) b)
* Weil II (1.1.1) c)
* Weil II (1.1.1) c), p.147
* Weil II (1.1.1) d)
* Weil II (1.1.1) d), pp.146-147
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type (d + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The integral fibre on objects and compatible families of maps. -/
noncomputable def lisseIntegralFiberFunctor :
    LisseIntegralSheaf l E Y ⥤ ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim

private lemma integralFiber_map_add {F G : LisseIntegralSheaf l E Y}
    (f g : F ⟶ G) :
    (lisseIntegralFiberFunctor l E Y y).map (f + g) =
      (lisseIntegralFiberFunctor l E Y y).map f +
        (lisseIntegralFiberFunctor l E Y y).map g := by
  apply limit.hom_ext
  intro j
  simp only [lisseIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringRight_obj_map, lim, limMap_π, Preadditive.add_comp]
  change _ ≫ ((pointSmallEtale y).ulift.{d + 1}.sheafFiber).map
    (f.hom.app j + g.hom.app j) = _
  let := Functor.additive_of_preserves_binary_products
    ((pointSmallEtale y).ulift.{d + 1}.sheafFiber
      (A := ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E)))
  rw [Functor.map_add, Preadditive.comp_add]
  rfl

private lemma integralFiber_map_smul {F G : LisseIntegralSheaf l E Y}
    (r : Padic.coefficientExtensionIntegers l E) (f : F ⟶ G) :
    (lisseIntegralFiberFunctor l E Y y).map (r • f) =
      r • (lisseIntegralFiberFunctor l E Y y).map f := by
  apply limit.hom_ext
  intro j
  simp only [lisseIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskeringRight_obj_map, lim, limMap_π, Linear.smul_comp]
  change _ ≫ ((pointSmallEtale y).ulift.{d + 1}.sheafFiber).map
    (r • f.hom.app j) = _
  rw [GrothendieckTopology.Point.sheafFiber_map_smul, Linear.comp_smul]
  rfl

private noncomputable def rationalFiberMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →ₗ[E]
      (lisseRationalFiber l E Y y F →ₗ[E] lisseRationalFiber l E Y y G) :=
  let R := Padic.coefficientExtensionIntegers l E
  let m : (F.integral ⟶ G.integral) →ₗ[R]
      ((lisseIntegralFiber l E Y y F.integral) →ₗ[R]
        (lisseIntegralFiber l E Y y G.integral)) :=
    { toFun f := ((lisseIntegralFiberFunctor l E Y y).map f).hom
      map_add' f g := congrArg ModuleCat.Hom.hom (integralFiber_map_add l E Y y f g)
      map_smul' r f := congrArg ModuleCat.Hom.hom (integralFiber_map_smul l E Y y r f) }
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • ((LinearMap.baseChangeHom R E _ _).comp m)
      map_add' a b := by ext; simp [add_smul]
      map_smul' a b := by ext; simp [mul_smul] }

private lemma rationalFiberMap_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    rationalFiberMap l E Y y F G (TensorProduct.tmul _ a f) =
      a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom := rfl

private lemma rationalFiberMap_id (F : LisseRationalSheaf l E Y) :
    rationalFiberMap l E Y y F F (TensorProduct.tmul _ 1 (𝟙 F.integral)) =
      LinearMap.id := by
  rw [rationalFiberMap_tmul]
  change 1 • LinearMap.baseChange E
    (((lisseIntegralFiberFunctor l E Y y).map (𝟙 F.integral)).hom) =
      (LinearMap.id :
        TensorProduct (Padic.coefficientExtensionIntegers l E) E
          ((lisseIntegralFiberFunctor l E Y y).obj F.integral) →ₗ[E] _)
  rw [(lisseIntegralFiberFunctor l E Y y).map_id]
  simp

private lemma rationalFiberMap_comp (F G H : LisseRationalSheaf l E Y)
    (f : F ⟶ G) (g : G ⟶ H) :
    rationalFiberMap l E Y y F H ((lisseRationalComposition l E Y).comp F G H f g) =
      (rationalFiberMap l E Y y G H g).comp (rationalFiberMap l E Y y F G f) := by
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      rw [(lisseRationalComposition l E Y).comp_tmul, rationalFiberMap_tmul,
        rationalFiberMap_tmul, rationalFiberMap_tmul, Functor.map_comp]
      change (a * b) • LinearMap.baseChange E
        ((((lisseIntegralFiberFunctor l E Y y).map g).hom).comp
          (((lisseIntegralFiberFunctor l E Y y).map f).hom)) = _
      rw [LinearMap.baseChange_comp, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, mul_comm a b]
    | add g h hg hh => simp [hg, hh, LinearMap.add_comp]
  | add f g hf hg => simp [hf, hg, LinearMap.comp_add]

/-- The rational fibre map is scalar extension of the integral map. -/
theorem lisseRationalFiberFunctor_exists :
    ∃ T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E,
      ∃ h : ∀ F, T.obj F = lisseRationalFiber l E Y y F,
        ∀ (F H : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ H.integral),
          T.map (TensorProduct.tmul _ a f) =
            eqToHom (h F) ≫ ModuleCat.ofHom
              (a • LinearMap.baseChange E ((lisseIntegralFiberFunctor l E Y y).map f).hom) ≫
                eqToHom (h H).symm := by
  let T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E :=
    { obj F := lisseRationalFiber l E Y y F
      map {F G} f := ModuleCat.ofHom (rationalFiberMap l E Y y F G f)
      map_id F := congrArg ModuleCat.ofHom (rationalFiberMap_id l E Y y F)
      map_comp {F G H} f g :=
        congrArg ModuleCat.ofHom (rationalFiberMap_comp l E Y y F G H f g) }
  refine ⟨T, (fun _ ↦ rfl), ?_⟩
  intro F G a f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg ModuleCat.ofHom (rationalFiberMap_tmul l E Y y F G a f)

/-- The rational fibre functor with its prescribed maps on pure tensors. -/
noncomputable def lisseRationalFiberFunctor : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E :=
  (lisseRationalFiberFunctor_exists l E Y y).choose

/-- Its object value is exactly the recorded rational fibre. -/
theorem lisseRationalFiberFunctor_obj (F : LisseRationalSheaf l E Y) :
    (lisseRationalFiberFunctor l E Y y).obj F = lisseRationalFiber l E Y y F := by
  exact (lisseRationalFiberFunctor_exists l E Y y).choose_spec.choose F

/-- The rational fibre functor has its prescribed action on integral pure tensors. -/
theorem lisseRationalFiberFunctor_map_spec :
    IsLisseRationalFiberFunctor Y y l E (lisseRationalFiberFunctor l E Y y)
      (lisseRationalFiberFunctor_obj l E Y y) :=
  (lisseRationalFiberFunctor_exists l E Y y).choose_spec.choose_spec

private def grothendieckFiberInclusion {B : Type*} [Category B]
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2}) (b : B) :
    P.obj ⟨b⟩ ⥤ Pseudofunctor.Grothendieck P where
  obj X := ⟨b, X⟩
  map {X Z} f := { base := 𝟙 b, fiber := (P.mapId ⟨b⟩).hom.toNatTrans.app X ≫ f }
  map_id X := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
    simp
  map_comp {X Z W} f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ (by simp) ?_
    simp [P.mapComp_id_left_hom_app, Bicategory.Strict.leftUnitor_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

section Algebraic

variable (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- The arrow on a fixed rational model in the coefficient localization. -/
noncomputable def lisseAlgebraicModelMap (E₀ : Padic.FiniteCoefficientFields l K)
    {F H : LisseRationalSheaf l E₀.val Y} (f : F ⟶ H) :
    lisseAlgebraicOfModel l Y K E₀ F ⟶ lisseAlgebraicOfModel l Y K E₀ H :=
  (lisseCoefficientCocartesian l Y K).Q.map
    { base := 𝟙 E₀
      fiber := ((lisseCoefficientDiagramData l Y K).diagram.mapId ⟨E₀⟩).hom.toNatTrans.app _ ≫
        (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.map f }

omit [IsAlgClosure ℚ_[l] K] in
/-- Fixed-model arrows preserve identities. -/
theorem lisseAlgebraicModelMap_id (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) :
    lisseAlgebraicModelMap l Y K E₀ (𝟙 F) = 𝟙 _ := by
  let T := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
    grothendieckFiberInclusion (lisseCoefficientDiagramData l Y K).diagram E₀ ⋙
      (lisseCoefficientCocartesian l Y K).Q
  exact T.map_id F

omit [IsAlgClosure ℚ_[l] K] in
/-- Fixed-model arrows preserve composition. -/
theorem lisseAlgebraicModelMap_comp (E₀ : Padic.FiniteCoefficientFields l K)
    {F H J : LisseRationalSheaf l E₀.val Y} (f : F ⟶ H) (g : H ⟶ J) :
    lisseAlgebraicModelMap l Y K E₀ (f ≫ g) =
      lisseAlgebraicModelMap l Y K E₀ f ≫ lisseAlgebraicModelMap l Y K E₀ g := by
  let T := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor ⋙
    grothendieckFiberInclusion (lisseCoefficientDiagramData l Y K).diagram E₀ ⋙
      (lisseCoefficientCocartesian l Y K).Q
  exact T.map_comp f g

/-- The canonical functor of a rational coefficient model into algebraic coefficients. -/
noncomputable def lisseAlgebraicModelFunctor (E₀ : Padic.FiniteCoefficientFields l K) :
    LisseRationalSheaf l E₀.val Y ⥤ LisseAlgebraicSheaf l Y K where
  obj := lisseAlgebraicOfModel l Y K E₀
  map := lisseAlgebraicModelMap l Y K E₀
  map_id := lisseAlgebraicModelMap_id l Y K E₀
  map_comp := lisseAlgebraicModelMap_comp l Y K E₀

omit [IsAlgClosure ℚ_[l] K] in
/-- The fibre of a displayed rational model is its specified scalar extension. -/
theorem lisseAlgebraicFiber_ofModel (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) :
    lisseAlgebraicFiber l Y K y (lisseAlgebraicOfModel l Y K E₀ F) =
      ModuleCat.of K (TensorProduct E₀.val K (lisseRationalFiber l E₀.val Y y F)) := by
  change ModuleCat.of K (TensorProduct E₀.val K
    (lisseRationalFiber l E₀.val Y y
      ((eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor.obj
        ((eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.obj F))))
    = _
  have cancel (C D : Cat.{d + 1, d + 2}) (h : C = D) (X : D) :
      (eqToHom h).toFunctor.obj ((eqToHom h.symm).toFunctor.obj X) = X := by
    cases h
    rfl
  exact congrArg (fun X ↦ ModuleCat.of K (TensorProduct E₀.val K
    (lisseRationalFiber l E₀.val Y y X)))
    (cancel _ (Cat.of (LisseRationalSheaf l E₀.val Y))
      ((lisseCoefficientDiagramData l Y K).obj_eq E₀) F)

/-- Fibre on one coefficient category, transported through its recorded category equality. -/
noncomputable def lisseCanonicalCoefficientModelFiberFunctor
    (E₀ : Padic.FiniteCoefficientFields l K) :
    (lisseCoefficientDiagramData l Y K).diagram.obj ⟨E₀⟩ ⥤ ModuleCat.{d + 1} K :=
  (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
    lisseRationalFiberFunctor l E₀.val Y y ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)

section Canonical

attribute [local irreducible] lisseRationalFiberFunctor lisseIntegralFiberFunctor
  lisseIntegralFiber

/-- The explicit rational scalar comparison on the recorded coefficient categories. -/
noncomputable def lisseCanonicalRawCoefficientComparison
    {E₀ L₀ : Padic.FiniteCoefficientFields l K} (f : E₀ ⟶ L₀) :
    lisseCanonicalCoefficientModelFiberFunctor l Y y K E₀ ≅
      ((lisseCoefficientDiagramData l Y K).diagram.map f.toLoc).toFunctor ⋙
        lisseCanonicalCoefficientModelFiberFunctor l Y y K L₀ :=
  lisseCoefficientFiberRawComparison l Y K
    (fun E₀ ↦ lisseRationalFiberFunctor l E₀.val Y y) E₀ L₀ f
    (lisseRationalFiberComparisonNatIso Y y l E₀.val L₀.val
      (IntermediateField.inclusion (leOfHom f)) K
      (algebraMap E₀.val K) (algebraMap L₀.val K) (by ext z; rfl)
      _ _ (lisseRationalFiberFunctor_obj l E₀.val Y y)
      (lisseRationalFiberFunctor_obj l L₀.val Y y)
      (lisseRationalFiberFunctor_map_spec l E₀.val Y y)
      (lisseRationalFiberFunctor_map_spec l L₀.val Y y))

/-- Restriction from the least coefficient field detects natural endomorphisms. -/
theorem lisseCanonicalCoefficientEndomorphisms (E₀ : Padic.FiniteCoefficientFields l K) :
    Function.Bijective (fun u : lisseCanonicalCoefficientModelFiberFunctor l Y y K E₀ ⟶
        lisseCanonicalCoefficientModelFiberFunctor l Y y K E₀ ↦
      Functor.whiskerLeft ((lisseCoefficientDiagramData l Y K).diagram.map
        (homOfLE (show Padic.finiteCoefficientBase l K ≤ E₀ from
          show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor u) :=
  lisseCoefficientFiberEndomorphisms_whisker_bijective l Y y K
    (fun E₀ ↦ lisseRationalFiberFunctor l E₀.val Y y)
    (fun E₀ ↦ lisseRationalFiberFunctor_obj l E₀.val Y y)
    (fun E₀ ↦ lisseRationalFiberFunctor_map_spec l E₀.val Y y) E₀

/-- The coefficient-pair fibre functor constructed from uniquely normalized comparisons. -/
@[irreducible]
noncomputable def lisseCanonicalCoefficientFiberFunctor :
    Pseudofunctor.Grothendieck (lisseCoefficientDiagramData l Y K).diagram ⥤
      ModuleCat.{d + 1} K :=
  Pseudofunctor.normalizedGrothendieckFiberFunctor (Padic.finiteCoefficientBase l K)
    (fun E₀ ↦ show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)
    (lisseCoefficientDiagramData l Y K).diagram
    (lisseCanonicalCoefficientModelFiberFunctor l Y y K)
    (fun {_ _} f ↦ lisseCanonicalRawCoefficientComparison l Y y K f)
    (lisseCanonicalCoefficientEndomorphisms l Y y K)

/-- The concrete coefficient functor inverts the cocartesian coefficient arrows. -/
theorem lisseCanonicalCoefficientFiberFunctor_inverts :
    (lisseCoefficientCocartesian l Y K).IsInvertedBy
      (lisseCanonicalCoefficientFiberFunctor l Y y K) := by
  intro X Z f hf
  have : IsIso f.fiber := hf
  unfold lisseCanonicalCoefficientFiberFunctor
    Pseudofunctor.normalizedGrothendieckFiberFunctor
  dsimp only
  infer_instance

/-- The algebraic fibre induced by the concrete normalized coefficient construction. -/
@[irreducible]
noncomputable def lisseAlgebraicFiberFunctor :
    LisseAlgebraicSheaf l Y K ⥤ ModuleCat.{d + 1} K :=
  Localization.Construction.lift (lisseCanonicalCoefficientFiberFunctor l Y y K)
    (lisseCanonicalCoefficientFiberFunctor_inverts l Y y K)

/-- Its object value is the recorded algebraic fibre. -/
theorem lisseAlgebraicFiberFunctor_obj (F : LisseAlgebraicSheaf l Y K) :
    (lisseAlgebraicFiberFunctor l Y y K).obj F = lisseAlgebraicFiber l Y K y F := by
  unfold lisseAlgebraicFiberFunctor lisseCanonicalCoefficientFiberFunctor
    Pseudofunctor.normalizedGrothendieckFiberFunctor
    lisseCanonicalCoefficientModelFiberFunctor
  change ModuleCat.of K (TensorProduct (lisseAlgebraicPair l Y K F).base.val K
    ((lisseRationalFiberFunctor l (lisseAlgebraicPair l Y K F).base.val Y y).obj
      (lisseCoefficientPairModel l Y K (lisseAlgebraicPair l Y K F)))) = _
  exact congrArg (fun V : ModuleCat.{d + 1} (lisseAlgebraicPair l Y K F).base.val ↦
    ModuleCat.of K (TensorProduct (lisseAlgebraicPair l Y K F).base.val K V))
      (lisseRationalFiberFunctor_obj l (lisseAlgebraicPair l Y K F).base.val Y y _)

attribute [local semireducible] lisseCanonicalCoefficientFiberFunctor
  Pseudofunctor.normalizedGrothendieckFiberFunctor

end Canonical

end Algebraic
end AlgebraicGeometry.Scheme
