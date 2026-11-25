/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseRationalScalarFiberMaps
public import Mathlib.LinearAlgebra.Span.Basic
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientHomBaseChange
import Mathlib.Algebra.Module.LocalizedModule.Int
import WeilConjectures.CategoryTheory.Sites.Point.Linear

/-! Finite coefficient descent of lisse rational sheaves.

## References

* Deligne, Weil II (1.1.1) c)-d), pp. 146-147
-/

@[expose] public section
set_option autoImplicit false
universe d
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
private lemma fractionCommonPure
    {R B M : Type*} [CommRing R] [IsDomain R] [Field B] [Algebra R B]
    [IsFractionRing R B] [AddCommGroup M] [Module R M]
    (x y : B ⊗[R] M) : ∃ a : B, ∃ m n : M,
      x = a ⊗ₜ[R] m ∧ y = a ⊗ₜ[R] n := by
  obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (TensorProduct.mk R B M 1) (fun b : Bool ↦ if b then x else y)
  obtain ⟨m, hm⟩ := hs true
  obtain ⟨n, hn⟩ := hs false
  have hs0 : algebraMap R B s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  have cancel (z : B ⊗[R] M) (m : M)
      (hm : (1 : B) ⊗ₜ[R] m = (s : R) • z) :
      z = (algebraMap R B s)⁻¹ ⊗ₜ[R] m := by
    rw [← algebraMap_smul B] at hm
    have hv := congrArg (fun w : B ⊗[R] M ↦ (algebraMap R B s)⁻¹ • w) hm.symm
    simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one] using hv
  exact ⟨_, m, n, cancel x m (by simpa using hm), cancel y n (by simpa using hn)⟩

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type (d + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

private noncomputable def coefficientIntegralFiberFunctor :
    LisseIntegralSheaf l E Y ⥤ ModuleCat.{d + 1} (Padic.coefficientExtensionIntegers l E) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim

private lemma integralFiber_map_add {F G : LisseIntegralSheaf l E Y}
    (f g : F ⟶ G) :
    (coefficientIntegralFiberFunctor l E Y y).map (f + g) =
      (coefficientIntegralFiberFunctor l E Y y).map f +
        (coefficientIntegralFiberFunctor l E Y y).map g := by
  apply limit.hom_ext
  intro j
  simp only [coefficientIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
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
    (coefficientIntegralFiberFunctor l E Y y).map (r • f) =
      r • (coefficientIntegralFiberFunctor l E Y y).map f := by
  apply limit.hom_ext
  intro j
  simp only [coefficientIntegralFiberFunctor, Functor.comp_map, ObjectProperty.ι_map,
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
    { toFun f := ((coefficientIntegralFiberFunctor l E Y y).map f).hom
      map_add' f g := congrArg ModuleCat.Hom.hom (integralFiber_map_add l E Y y f g)
      map_smul' r f := congrArg ModuleCat.Hom.hom (integralFiber_map_smul l E Y y r f) }
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • ((LinearMap.baseChangeHom R E _ _).comp m)
      map_add' a b := by ext; simp [add_smul]
      map_smul' a b := by ext; simp [mul_smul] }

private lemma rationalFiberMap_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    rationalFiberMap l E Y y F G (TensorProduct.tmul _ a f) =
      a • LinearMap.baseChange E ((coefficientIntegralFiberFunctor l E Y y).map f).hom := rfl

@[instance_reducible]
private noncomputable def coefficientRationalHomModule (F G : LisseRationalSheaf l E Y) :
    Module E (F ⟶ G) :=
  inferInstanceAs (Module E (lisseRationalHom l E Y F G))

attribute [local instance] coefficientRationalHomModule

private lemma fiberMap_eq
    (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
    (hT : ∀ F, T.obj F = lisseRationalFiber l E Y y F)
    (hspec : IsLisseRationalFiberFunctor Y y l E T hT)
    (F G : LisseRationalSheaf l E Y) (f : F ⟶ G) :
    T.map f = eqToHom (hT F) ≫ ModuleCat.ofHom
      (rationalFiberMap l E Y y F G f) ≫ eqToHom (hT G).symm := by
  have : IsFractionRing (Padic.coefficientExtensionIntegers l E) E :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.1
  obtain ⟨a, m, n, hf, _⟩ := fractionCommonPure
    (R := Padic.coefficientExtensionIntegers l E) (B := E)
    (M := F.integral ⟶ G.integral) f 0
  rw [hf, rationalFiberMap_tmul]
  exact hspec F G a m

private lemma fiberMap_add
    (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
    (hT : ∀ F, T.obj F = lisseRationalFiber l E Y y F)
    (hspec : IsLisseRationalFiberFunctor Y y l E T hT)
    (F G : LisseRationalSheaf l E Y) (f g : F ⟶ G) :
    T.map (f + g) = T.map f + T.map g := by
  rw [fiberMap_eq l E Y y T hT hspec,
    fiberMap_eq l E Y y T hT hspec F G f,
    fiberMap_eq l E Y y T hT hspec F G g]
  simp only [map_add, ModuleCat.ofHom_add, Preadditive.comp_add, Preadditive.add_comp]

private lemma fiberMap_smul
    (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
    (hT : ∀ F, T.obj F = lisseRationalFiber l E Y y F)
    (hspec : IsLisseRationalFiberFunctor Y y l E T hT)
    (F G : LisseRationalSheaf l E Y) (a : E) (f : F ⟶ G) :
    T.map (a • (f : lisseRationalHom l E Y F G)) = a • T.map f := by
  rw [fiberMap_eq l E Y y T hT hspec,
    fiberMap_eq l E Y y T hT hspec F G f]
  rw [(rationalFiberMap l E Y y F G).map_smul]
  change _ ≫ (a • ModuleCat.ofHom (rationalFiberMap l E Y y F G f)) ≫ _ = _
  with_unfolding_all
    simp only [Linear.comp_smul, Linear.smul_comp]

private lemma extend_map_smul {R A : Type (d + 1)} [CommRing R] [CommRing A]
    (r : R →+* A) {M N : ModuleCat.{d + 1} R} (a : R) (f : M ⟶ N) :
    (ModuleCat.extendScalars r).map (a • f) =
      r a • (ModuleCat.extendScalars r).map f := by
  let := r.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change TensorProduct.tmul R (1 : A) (a • f m) =
    TensorProduct.tmul R (r a * 1) (f m)
  rw [TensorProduct.tmul_smul]
  rfl

private lemma extend_map_add {R A : Type (d + 1)} [CommRing R] [CommRing A]
    (r : R →+* A) {M N : ModuleCat.{d + 1} R} (f g : M ⟶ N) :
    (ModuleCat.extendScalars r).map (f + g) =
      (ModuleCat.extendScalars r).map f + (ModuleCat.extendScalars r).map g := by
  let := r.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change TensorProduct.tmul R (1 : A) (f m + g m) =
    TensorProduct.tmul R (1 : A) (f m) + TensorProduct.tmul R (1 : A) (g m)
  exact TensorProduct.tmul_add _ _ _

private lemma fiberMap_mem_span
    (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
    (hT : ∀ F, T.obj F = lisseRationalFiber l E Y y F)
    (hspec : IsLisseRationalFiberFunctor Y y l E T hT)
    {K : Type (d + 1)} [Field K] (r : E →+* K)
    (F G : LisseRationalSheaf l E Y)
    (A : Set (lisseRationalHom l E Y F G))
    (W : Submodule K ((ModuleCat.extendScalars r).obj (T.obj F) ⟶
      (ModuleCat.extendScalars r).obj (T.obj G)))
    (hW : ∀ f ∈ A, (ModuleCat.extendScalars r).map (T.map f) ∈ W)
    (f : lisseRationalHom l E Y F G) (hf : f ∈ Submodule.span E A) :
    (ModuleCat.extendScalars r).map (T.map f) ∈ W := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact hW f hf
  | zero =>
      have h0 : T.map (0 : F ⟶ G) = 0 := by
        simpa using fiberMap_smul l E Y y T hT hspec F G 0 (0 : F ⟶ G)
      have he0 : (ModuleCat.extendScalars r).map (0 : T.obj F ⟶ T.obj G) = 0 := by
        simpa using extend_map_smul r 0 (0 : T.obj F ⟶ T.obj G)
      rw [h0, he0]
      exact W.zero_mem
  | add f g hf hg ef eg =>
      rw [fiberMap_add l E Y y T hT hspec F G f g, extend_map_add]
      exact W.add_mem ef eg
  | smul a f hf ef =>
      rw [fiberMap_smul l E Y y T hT hspec F G a f, extend_map_smul]
      exact W.smul_mem (r a) ef

private lemma coefficientSpan_from_hom_span
    (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (hS : ∀ (E₀ : Padic.FiniteCoefficientFields l K)
      (F : LisseRationalSheaf l E₀.val Y), (S E₀).obj F = lisseRationalFiber l E₀.val Y y F)
    (hmap : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      IsLisseRationalFiberFunctor Y y l E₀.val (S E₀) (hS E₀))
    (E₀ : Padic.FiniteCoefficientFields l K)
    (hcoef :
      let P := (lisseCoefficientDiagramData l Y K).diagram
      let T := (P.map (homOfLE
        (show Padic.finiteCoefficientBase l K ≤ E₀ from
          show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
      let Q := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor
      ∀ (A B : P.obj ⟨Padic.finiteCoefficientBase l K⟩) (f : T.obj A ⟶ T.obj B),
        (Q.map f : lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B))) ∈
          Submodule.span
            (M := lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B)))
            E₀.val (Set.range (fun g : A ⟶ B ↦
            (Q.map (T.map g) :
              lisseRationalHom l E₀.val Y (Q.obj (T.obj A)) (Q.obj (T.obj B)))))) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let T := (P.map (homOfLE
      (show Padic.finiteCoefficientBase l K ≤ E₀ from
        show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
    let J := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
      S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    ∀ (A B : P.obj ⟨Padic.finiteCoefficientBase l K⟩) (f : T.obj A ⟶ T.obj B),
      J.map f ∈ Submodule.span K (Set.range (fun g : A ⟶ B ↦ J.map (T.map g))) := by
  dsimp only
  intro A B f
  let P := (lisseCoefficientDiagramData l Y K).diagram
  let T := (P.map (homOfLE
    (show Padic.finiteCoefficientBase l K ≤ E₀ from
      show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
  let Q := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor
  let J := Q ⋙ S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
  let W := Submodule.span K (Set.range (fun g : A ⟶ B ↦ J.map (T.map g)))
  exact fiberMap_mem_span l E₀.val Y y (S E₀) (hS E₀) (hmap E₀)
    (algebraMap E₀.val K) (Q.obj (T.obj A)) (Q.obj (T.obj B))
    (Set.range (fun g : A ⟶ B ↦ Q.map (T.map g))) W
    (by
      intro z hz
      obtain ⟨g, rfl⟩ := hz
      exact Submodule.subset_span ⟨g, rfl⟩)
    (Q.map f) (hcoef A B f)

variable (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Maps of scalar-extended sheaves act on geometric fibres in the scalar span of
maps from the least coefficient category. -/
theorem lisseCoefficientRestriction_hom_span
    {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (hS : ∀ (E₀ : Padic.FiniteCoefficientFields l K)
      (F : LisseRationalSheaf l E₀.val Y), (S E₀).obj F = lisseRationalFiber l E₀.val Y y F)
    (hmap : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      IsLisseRationalFiberFunctor Y y l E₀.val (S E₀) (hS E₀))
    (E₀ : Padic.FiniteCoefficientFields l K) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let T := (P.map (homOfLE
      (show Padic.finiteCoefficientBase l K ≤ E₀ from
        show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
    let J := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
      S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    ∀ (A B : P.obj ⟨Padic.finiteCoefficientBase l K⟩) (f : T.obj A ⟶ T.obj B),
      J.map f ∈ Submodule.span K (Set.range (fun g : A ⟶ B ↦ J.map (T.map g))) := by
  exact coefficientSpan_from_hom_span (l := l) (Y := Y) (y := y) K S hS hmap E₀
    (lisseCoefficientHomBaseChange_span l Y K E₀)

end AlgebraicGeometry.Scheme
