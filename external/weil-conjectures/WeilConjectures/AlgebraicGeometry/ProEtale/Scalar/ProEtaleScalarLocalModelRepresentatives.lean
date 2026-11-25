/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelSurjectiveClosedReflection
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import all WeilConjectures.Algebra.Homology.SixFunctors.LocallyPrescribedModulesSmall
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Small families of integral scalar local models

The site has objects in `Type (u + 1)` and morphisms in `Type u`; its module sections
and the representative index set live in `Type (u + 1)`. Scalar matrix quotients are
constructed before applying the existing constant-module scalar-extension functor.

## Main declarations

* `sfbScalarPresentationModule`: the actual quotient by a finite scalar matrix.
* `sfbIntegralScalarPresentationModel`: its existing scalar-extension realization.
* `proetale_scalar_local_model_representatives`: representatives and scalar matrix labels.

## References

* Stacks Tag 0518, finite presentations
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The actual scalar quotient `A^n / range q`, with a universe lift for the existing
scalar-model functor. The labels `(m, n, q)` form `Σ m n: ℕ, Matrix (Fin n) (Fin m) A`. -/
def sfbScalarPresentationModule (A : Type u) [CommRing A] (m n : ℕ)
    (q : Matrix (Fin n) (Fin m) A) : ModuleCat.{u + 1} A :=
  ModuleCat.of A (ULift.{u + 1} ((Fin n → A) ⧸ LinearMap.range q.mulVecLin))

/-- The scalar-extension model of the actual quotient by a scalar matrix. The topology
and coefficient ring are exactly those of `integralModelCondensedCoefficients`. -/
def sfbIntegralScalarPresentationModel (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (U : Scheme.{u}) (m n : ℕ)
    (q : Matrix (Fin n) (Fin m) (Padic.coefficientExtensionIntegers l E)) :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralModelCondensedCoefficients l E).X U) :=
  letI := spectralNorm.normedField (Padic l) E
  (FiniteConstantModel.modelFunctor (Padic.coefficientExtensionIntegers l E) U).obj
    (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.lowerStar
  Mod.extendScalarsIsoComapInv upperStarIsoLocalizationRestriction
  CondensedRing.upperStarLowerStarAdjunction

private theorem pullback_jointly_faithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (a b : M ⟶ N)
    (h : ∀ i, (CondensedRing.upperStar Λ (C.f i)).map a =
      (CondensedRing.upperStar Λ (C.f i)).map b) : a = b := by
  have (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
  have hm (i : C.I₀) :
      (upperStar Ab.{u + 1} (C.f i)).map a.hom =
        (upperStar Ab.{u + 1} (C.f i)).map b.hom := by
    let φ := condensedPullbackHom Λ (C.f i)
    let H := (upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj Λ T)
    let e := Mod.extendScalarsIsoComapInv φ
    have he : (Mod.comap (asIso φ).inv).map (H.map a) =
        (Mod.comap (asIso φ).inv).map (H.map b) := by
      have hx : (Mod.extendScalars φ).map (H.map a) =
          (Mod.extendScalars φ).map (H.map b) := by
        simpa only [CondensedRing.upperStar, Functor.comp_map] using h i
      exact (cancel_epi (e.hom.app (H.obj M))).mp
        ((e.hom.naturality (H.map a)).symm.trans
          ((congrArg (fun k ↦ k ≫ e.hom.app (H.obj N)) hx).trans
            (e.hom.naturality (H.map b))))
    exact congrArg Mod.Hom.hom he
  have hr (i : C.I₀) :
      (localizationRestriction Ab.{u + 1} (C.f i) inferInstance).map a.hom =
        (localizationRestriction Ab.{u + 1} (C.f i) inferInstance).map b.hom := by
    let e := upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f i) inferInstance
    apply (cancel_epi (e.hom.app M.X)).mp
    rw [← e.hom.naturality, ← e.hom.naturality, hm i]
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  obtain ⟨V⟩ := V
  let cv : (Scheme.ProEt.topology T).Cover V :=
    ⟨_, Scheme.ProEt.ofArrows_baseChange_mem_topology V C.f C.mem₀⟩
  apply N.X.property.hom_ext cv
  intro Z
  obtain ⟨W, f, hf⟩ := Z
  obtain ⟨_, d, _, ⟨i⟩, rfl⟩ := hf
  let p := d.left ≫ pullback.snd V.hom (C.f i)
  have hp : p ≫ C.f i = W.hom := by
    dsimp [p]
    rw [Category.assoc, ← pullback.condition]
    exact MorphismProperty.Over.w d
  have : WeaklyEtale p := by
    have : WeaklyEtale (p ≫ C.f i) := hp ▸ W.prop
    exact WeaklyEtale.of_comp p (C.f i)
  let W' : (C.X i).ProEt := Scheme.ProEt.mk p
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (C.f i))).obj W' ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by
      change 𝟙 W.left ≫ W.hom = p ≫ C.f i
      simpa only [Category.id_comp] using hp.symm)
  have hi := congrArg (fun k ↦ k.hom.app (Opposite.op W')) (hr i)
  have he : a.hom.hom.app (Opposite.op W) = b.hom.hom.app (Opposite.op W) := by
    apply (cancel_epi (M.X.obj.map e.inv.op)).mp
    rw [a.hom.hom.naturality, b.hom.hom.naturality]
    exact congrArg (fun k ↦ k ≫ N.X.obj.map e.inv.op) hi
  change a.hom.hom.app (Opposite.op V) ≫
    N.X.obj.map (d ≫ Scheme.ProEt.baseChangeHom (C.f i) V).op = _
  rw [← a.hom.hom.naturality, ← b.hom.hom.naturality, he]

private theorem isoNonempty_trans {C : Type*} [Category* C] {X Y Z : C}
    (h : Nonempty (X ≅ Y)) (k : Nonempty (Y ≅ Z)) : Nonempty (X ≅ Z) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := k
  exact ⟨e.trans f⟩

private theorem isoNonempty_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} (h : Nonempty (X ≅ Y)) :
    Nonempty (F.obj X ≅ F.obj Y) := by
  obtain ⟨e⟩ := h
  exact ⟨F.mapIso e⟩

private theorem finitePointCodes
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃ (I : Type (u + 1))
      (F : I → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ),
      ∀ P, Mod.IsFinitelyPresented Λ P → ∃ i, Nonempty (P ≅ F i) := by
  let I := Σ n m : ℕ, (Mod.finiteFree Λ m ⟶ Mod.finiteFree Λ n)
  refine ⟨I, fun i ↦ cokernel i.2.2, ?_⟩
  rintro P ⟨n, m, f, e⟩
  exact ⟨⟨n, m, f⟩, e⟩

private theorem mono_product_adjuncts
    {A : Type*} [Category* A] {I : Type*} {B : I → Type*}
    [∀ i, Category* (B i)] (F : ∀ i, A ⥤ B i) (G : ∀ i, B i ⥤ A)
    (adj : ∀ i, F i ⊣ G i)
    (hfaith : ∀ {L M : A} (a b : L ⟶ M), (∀ i, (F i).map a = (F i).map b) → a = b)
    (M : A) (models : ∀ i, B i) (e : ∀ i, (F i).obj M ≅ models i)
    [HasProduct (fun i ↦ (G i).obj (models i))] :
    Mono (Pi.lift (fun i ↦ (adj i).homEquiv M (models i) (e i).hom)) := by
  constructor
  intro L a b hab
  apply hfaith a b
  intro i
  have h : a ≫ (adj i).homEquiv M (models i) (e i).hom =
      b ≫ (adj i).homEquiv M (models i) (e i).hom := by
    simpa only [Category.assoc, Pi.lift_comp_π] using
      congrArg (fun z ↦ z ≫ Pi.π (fun i ↦ (G i).obj (models i)) i) hab
  apply (cancel_mono (e i).hom).1
  apply ((adj i).homEquiv L (models i)).injective
  exact ((adj i).homEquiv_naturality_left a (e i).hom).trans
    (h.trans ((adj i).homEquiv_naturality_left b (e i).hom).symm)

private theorem small_cover_adjunction_models
    {A : Type*} [Category* A] [LocallySmall.{u + 1} A] [WellPowered.{u + 1} A]
    [HasProducts.{u} A] {Cov : Type (u + 1)} {I : Cov → Type u}
    {B : ∀ C, I C → Type*} [∀ C i, Category* (B C i)]
    (F : ∀ C i, A ⥤ B C i) (G : ∀ C i, B C i ⥤ A)
    (adj : ∀ C i, F C i ⊣ G C i)
    (hfaith : ∀ C {L N : A} (a b : L ⟶ N),
      (∀ i, (F C i).map a = (F C i).map b) → a = b)
    (Label : Type (u + 1)) (model : ∀ C i, Label → B C i)
    (P : ObjectProperty A)
    (loc : ∀ M, P M → ∃ C, ∀ i, ∃ q, Nonempty ((F C i).obj M ≅ model C i q)) :
    ObjectProperty.EssentiallySmall.{u + 1} P := by
  classical
  let Code := Σ C : Cov, (I C → Label)
  let family (k : Code) (i : I k.1) := (G k.1 i).obj (model k.1 i (k.2 i))
  let Q (k : Code) := ∏ᶜ (family k)
  let R (k : Code) : ObjectProperty A := fun M ↦ ∃ f : M ⟶ Q k, Mono f
  have hR (k : Code) : ObjectProperty.EssentiallySmall.{u + 1} (R k) :=
    SheafOfModules.essentiallySmall_embeds (𝟭 A) (Functor.FullyFaithful.id A) (Q k)
  let (k : Code) : ObjectProperty.EssentiallySmall.{u + 1} (R k) := hR k
  apply ObjectProperty.EssentiallySmall.of_le (Q := ⨆ k, R k)
  intro M hM
  obtain ⟨C, hC⟩ := loc M hM
  choose q e using hC
  let k : Code := ⟨C, q⟩
  let φ : M ⟶ Q k := Pi.lift (f := family k)
    (fun i ↦ (adj C i).homEquiv M (model C i (q i)) (e i).some.hom)
  have hφ : Mono φ := mono_product_adjuncts
    (F C) (G C) (adj C) (hfaith C) M (fun i ↦ model C i (q i)) (fun i ↦ (e i).some)
  exact (show R k M from ⟨φ, hφ⟩) |> le_iSup R k M

attribute [local irreducible] CondensedRing.upperStar

private theorem internalModules_grothendieck
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (T : Scheme.{u}) : IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  Mod.isGrothendieckAbelian _

attribute [local instance] internalModules_grothendieck

private theorem internalModules_limits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (T : Scheme.{u}) : HasLimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) := by
  infer_instance

private theorem internalModules_wellPowered
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (T : Scheme.{u}) : WellPowered.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) := by
  infer_instance

private theorem pointCode_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (U : Scheme.{u})
    (Label : Type (u + 1))
    (repr : Label → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hrepr : ∀ P, Mod.IsFinitelyPresented Λ P → ∃ q, Nonempty (P ≅ repr q))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (h : ∃ P, Mod.IsFinitelyPresented Λ P ∧
      Nonempty (M ≅ ((upperStarFromPoint U).mapMod Λ).obj P)) :
    ∃ q, Nonempty (M ≅ ((upperStarFromPoint U).mapMod Λ).obj (repr q)) := by
  obtain ⟨P, hP, he⟩ := h
  obtain ⟨q, hq⟩ := hrepr P hP
  exact ⟨q, isoNonempty_trans he (isoNonempty_map ((upperStarFromPoint U).mapMod Λ) hq)⟩

private theorem coverPointCodes
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {T : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (Label : Type (u + 1))
    (repr : Label → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hrepr : ∀ P, Mod.IsFinitelyPresented Λ P → ∃ q, Nonempty (P ≅ repr q))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hC : ∀ i : C.I₀, ∃ P, Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((CondensedRing.upperStar Λ (C.f i)).obj M ≅
        ((upperStarFromPoint (C.X i)).mapMod Λ).obj P)) :
    ∀ i : C.I₀, ∃ q, Nonempty ((CondensedRing.upperStar Λ (C.f i)).obj M ≅
      ((upperStarFromPoint (C.X i)).mapMod Λ).obj (repr q)) :=
  fun i ↦ pointCode_exists Λ (C.X i) Label repr hrepr _ (hC i)

set_option backward.isDefEq.respectTransparency false in
private theorem finitePointModels_small
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty.EssentiallySmall.{u + 1} (HasFiniteConstantLocalModel Λ T) := by
  classical
  have := internalModules_limits Λ T
  have := internalModules_wellPowered Λ T
  obtain ⟨Label, repr, hrepr⟩ := finitePointCodes Λ
  exact small_cover_adjunction_models
    (A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (Cov := Scheme.Cover.{u} Scheme.proetalePrecoverage T) (I := fun C ↦ C.I₀)
    (B := fun C i ↦ Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
      (condensedRingObj Λ (C.X i)))
    (fun C i ↦ CondensedRing.upperStar Λ (C.f i))
    (fun C i ↦ CondensedRing.lowerStar Λ (C.f i))
    (fun C i ↦ CondensedRing.upperStarLowerStarAdjunction Λ (C.f i))
    (fun C _ _ a b hab ↦ pullback_jointly_faithful Λ C a b hab) Label
    (fun C i q ↦ ((upperStarFromPoint (C.X i)).mapMod Λ).obj (repr q))
    (HasFiniteConstantLocalModel Λ T) (by
      rintro M ⟨C, hC⟩
      exact ⟨C, coverPointCodes Λ C Label repr hrepr M hC⟩)

private theorem scalarPresentation_exists (A : Type u) [CommRing A]
    (P : ModuleCat.{u + 1} A) [Module.FinitePresentation A P] :
    ∃ (m n : ℕ) (q : Matrix (Fin n) (Fin m) A),
      Nonempty (P ≅ sfbScalarPresentationModule A m n q) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin A P
  obtain ⟨m, g, hg⟩ := K.fg_iff_exists_fin_linearMap.mp hK
  let q := LinearMap.toMatrix' g
  have hq : LinearMap.range q.mulVecLin = K := by
    change LinearMap.range (Matrix.toLin' q) = K
    simpa only [q, Matrix.toLin'_toMatrix'] using hg
  refine ⟨m, n, q, ⟨?_⟩⟩
  exact (e.trans ((Submodule.quotEquivOfEq _ _ hq).symm.trans
    ULift.moduleEquiv.symm)).toModuleIso

private theorem scalarPresentation_finite (A : Type u) [CommRing A]
    (m n : ℕ) (q : Matrix (Fin n) (Fin m) A) :
    Module.FinitePresentation A (sfbScalarPresentationModule A m n q) := by
  have : Module.FinitePresentation A ((Fin n → A) ⧸ LinearMap.range q.mulVecLin) :=
    Module.finitePresentation_of_surjective (LinearMap.range q.mulVecLin).mkQ
      (Submodule.mkQ_surjective _) (by simp)
  exact Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm

private theorem point_scalarPresentation_iff (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (U : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) U)) :
    (∃ P, Mod.IsFinitelyPresented (Profinite.continuousCoefficientRingObj A) P ∧
      Nonempty (M ≅ ((upperStarFromPoint U).mapMod
        (Profinite.continuousCoefficientRingObj A)).obj P)) ↔
      ∃ (m n : ℕ) (q : Matrix (Fin n) (Fin m) A),
        Nonempty (M ≅ (FiniteConstantModel.modelFunctor A U).obj
          (sfbScalarPresentationModule A m n q)) := by
  classical
  let Λ := Profinite.continuousCoefficientRingObj A
  let F := (upperStarFromPoint U).mapMod Λ
  constructor
  · rintro ⟨P, hP, he⟩
    obtain ⟨N, hN, heN⟩ := (continuousScalarFinitePresentation A P).mp hP
    have := hN
    obtain ⟨m, n, q, heQ⟩ := scalarPresentation_exists A N
    refine ⟨m, n, q, ?_⟩
    change Nonempty (M ≅ F.obj
      ((continuousScalarFunctor A).obj (sfbScalarPresentationModule A m n q)))
    exact isoNonempty_trans he (isoNonempty_trans (isoNonempty_map F heN)
      (isoNonempty_map F (isoNonempty_map (continuousScalarFunctor A) heQ)))
  · rintro ⟨m, n, q, he⟩
    let Q := sfbScalarPresentationModule A m n q
    let P := (continuousScalarFunctor A).obj Q
    have hQ : Module.FinitePresentation A Q := scalarPresentation_finite A m n q
    have hP : Mod.IsFinitelyPresented Λ P :=
      (continuousScalarFinitePresentation A P).mpr ⟨Q, hQ, ⟨Iso.refl _⟩⟩
    exact ⟨P, hP, he⟩

/-- A small family of modules with finite constant scalar local models exhausts that
class up to isomorphism. The second conjunct identifies the local condition using
precisely the quotients indexed by scalar matrices, without matrices of local sections. -/
theorem proetale_scalar_local_model_representatives
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    (∃ (I : Type (u + 1))
      (F : I → Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (integralModelCondensedCoefficients l E).X T)),
      (∀ t : I, HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X
        T (F t)) ∧
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integralModelCondensedCoefficients l E).X T),
        HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T M →
          ∃ t : I, Nonempty (M ≅ F t)) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (integralModelCondensedCoefficients l E).X T),
      HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T M ↔
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : 𝒰.I₀,
          ∃ (m n : ℕ)
            (q : Matrix (Fin n) (Fin m) (Padic.coefficientExtensionIntegers l E)),
            Nonempty
              ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X
                (𝒰.f i)).obj M ≅
                sfbIntegralScalarPresentationModel l E (𝒰.X i) m n q)) := by
  classical
  constructor
  · let P := HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X T
    have : ObjectProperty.EssentiallySmall.{u + 1} P :=
      finitePointModels_small _ T
    obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
    let F : Shrink.{u + 1} (Subtype Q) → _ := fun i ↦ ((equivShrink _).symm i).val
    refine ⟨_, F, fun i ↦ hQP _ ((equivShrink _).symm i).property, ?_⟩
    intro M hM
    obtain ⟨N, hN, e⟩ := hPQ M hM
    exact ⟨equivShrink _ ⟨N, hN⟩, by simpa only [F, Equiv.symm_apply_apply] using e⟩
  · intro M
    let := spectralNorm.normedField (Padic l) E
    let A := Padic.coefficientExtensionIntegers l E
    constructor
    · rintro ⟨C, hC⟩
      exact ⟨C, fun i ↦ (point_scalarPresentation_iff A (C.X i) _).mp (hC i)⟩
    · rintro ⟨C, hC⟩
      exact ⟨C, fun i ↦ (point_scalarPresentation_iff A (C.X i) _).mpr (hC i)⟩

end AlgebraicGeometry.ProEtale
