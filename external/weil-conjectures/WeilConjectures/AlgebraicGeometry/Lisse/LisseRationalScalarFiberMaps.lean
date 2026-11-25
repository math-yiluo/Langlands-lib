/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseIntegralScalarFiberIsomorphism
import Mathlib.RingTheory.Localization.BaseChange

/-! # Rational scalar comparison of geometric fibres

## References

* Weil II (1.1.1) c), d), pp. 146-147
* Weil II (1.1.1) c)
* Weil II (1.1.1) c), d)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe d
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

private lemma fractionTensorPure {R B : Type*} [CommRing R] [IsDomain R] [Field B]
    [Algebra R B] [IsFractionRing R B]
    (M : Type*) [AddCommGroup M] [Module R M] (z : B ⊗[R] M) :
    ∃ a : B, ∃ m : M, z = a ⊗ₜ[R] m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R)
    (TensorProduct.mk R B M 1) z
  have hs0 : algebraMap R B s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  refine ⟨(algebraMap R B s)⁻¹, m, ?_⟩
  rw [Submonoid.smul_def, ← algebraMap_smul B] at hs
  have h : (algebraMap R B s) • z = (1 : B) ⊗ₜ[R] m := hs
  have hv := congrArg (fun x : B ⊗[R] M ↦ (algebraMap R B s)⁻¹ • x) h
  simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one] using hv

/-- Compare extension along an algebra map with its usual tensor product. -/
def tensorAlgebraIso {R A : Type (d + 1)} [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{d + 1} R) :
    (ModuleCat.extendScalars (algebraMap R A)).obj M ≅
      ModuleCat.of A (A ⊗[R] M) := by
  let e : ((ModuleCat.restrictScalars (algebraMap R A)).obj
      (ModuleCat.of A A)) ≃ₗ[R] A :=
    { toFun := fun a ↦ a
      invFun := fun a ↦ a
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r a ↦ (@Algebra.smul_def R A _ _ _ r a).symm }
  let q := TensorProduct.congr e (LinearEquiv.refl R M)
  let qA : (ModuleCat.extendScalars (algebraMap R A)).obj M ≃ₗ[A]
      (A ⊗[R] M) :=
    { q.toEquiv with
      map_add' := q.map_add
      map_smul' := by
        intro a z
        induction z using TensorProduct.inductionOn with
        | tmul b m => rfl
        | add x z hx hz =>
          change q (a • x) = a • q x at hx
          change q (a • z) = a • q z at hz
          change q (a • (x + z)) = a • q (x + z)
          rw [smul_add, q.map_add, q.map_add, hx, hz, smul_add] }
  exact qA.toModuleIso

/-- Scalar extension written with the given algebra module structure. -/
def algebraTensorFunctor {R A : Type (d + 1)} [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat.{d + 1} R ⥤ ModuleCat.{d + 1} A where
  obj M := ModuleCat.of A (A ⊗[R] M)
  map f := ModuleCat.ofHom (LinearMap.baseChange A f.hom)
  map_id M := by ext a; rfl
  map_comp f g := by ext a; rfl

/-- The usual algebra tensor product is naturally isomorphic to extension of scalars. -/
def tensorAlgebraNatIso {R A : Type (d + 1)} [CommRing R] [CommRing A] [Algebra R A] :
    ModuleCat.extendScalars (algebraMap R A) ≅ algebraTensorFunctor (R := R) (A := A) :=
  NatIso.ofComponents (fun M ↦ tensorAlgebraIso M) (by
    intro M N f
    ext a
    rfl)

private lemma scalarExtension_map_smul {R A : Type (d + 1)} [CommRing R] [CommRing A]
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

private lemma mapEqCancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (h : X = Y) {Z : D} (g : F.obj Y ⟶ Z) :
    F.map (eqToHom h.symm) ≫ F.map (eqToHom h) ≫ g = g := by
  rw [← F.map_comp_assoc, eqToHom_trans, eqToHom_refl, F.map_id, Category.id_comp]

variable (Y : Scheme.{d}) {Ω : Type d} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (l : ℕ) [Fact l.Prime]
  (E : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L : Type (d + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (K : Type (d + 1)) [Field K]
  (j : E →+* K) (k : L →+* K) (hjk : k.comp ι.toRingHom = j)

/-- The defining pure-tensor formula for a rational geometric fibre functor. -/
def IsLisseRationalFiberFunctor
    (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
    (h : ∀ F, T.obj F = lisseRationalFiber l E Y y F) : Prop :=
  let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  ∀ (F G : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ G.integral),
    T.map (TensorProduct.tmul _ a f) =
      eqToHom (h F) ≫ ModuleCat.ofHom
        (a • LinearMap.baseChange E
          (show lisseIntegralFiber l E Y y F.integral →ₗ[
              Padic.coefficientExtensionIntegers l E] lisseIntegralFiber l E Y y G.integral
            from (I.map f).hom)) ≫ eqToHom (h G).symm

/-- Integral scalar extension followed by rational coefficient extension is natural. -/
def lisseIntegralScalarFiberKNatIso :
    let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    I ⋙ ModuleCat.extendScalars (algebraMap (Padic.coefficientExtensionIntegers l E) E) ⋙
      ModuleCat.extendScalars j ≅
    (lisseIntegralScalarExtensionData l E Y L ι).functor ⋙ J ⋙
      ModuleCat.extendScalars (algebraMap (Padic.coefficientExtensionIntegers l L) L) ⋙
        ModuleCat.extendScalars k := by
  let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let Q := (lisseIntegralScalarExtensionData l E Y L ι).functor
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let α := lisseIntegerInclusion l E L ι
  let i := algebraMap R E
  let t := algebraMap S L
  let r := j.comp i
  let s := k.comp t
  have hα : s.comp α = r := by
    ext a
    change k (α a : L) = j (a : E)
    have ha : (α a : L) = ι (a : E) :=
      (lisseIntegerInclusion_exists l E L ι).choose_spec a
    rw [ha]
    exact congrArg (fun f : E →+* K ↦ f (a : E)) hjk
  let eR := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} r)
  let eS := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} s).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} s)
  let c : I ⋙ ModuleCat.ringExtendScalars.{d + 1, d + 1} α ≅ Q ⋙ J :=
    NatIso.ofComponents (fun F ↦ by
      have := lisseIntegralScalarFiberComparison_isIso Y y l E L ι F
      exact asIso (lisseIntegralScalarFiberComparison Y y l E L ι F))
      (fun f ↦ lisseIntegralScalarFiberComparison_naturality Y y l E L ι f)
  let eα : ModuleCat.ringExtendScalars.{d + 1, d + 1} r ≅
      ModuleCat.ringExtendScalars.{d + 1, d + 1} α ⋙
        ModuleCat.ringExtendScalars.{d + 1, d + 1} s :=
    eqToIso (congrArg (fun f : R →+* K ↦
      ModuleCat.ringExtendScalars.{d + 1, d + 1} f) hα.symm) ≪≫
        (ModuleCat.ringExtensionComp.{d + 1, d + 1} α s).symm
  exact Functor.isoWhiskerLeft I (ModuleCat.extendScalarsComp.{d + 1, d + 1} i j).symm ≪≫
    Functor.isoWhiskerLeft I eR.symm ≪≫ Functor.isoWhiskerLeft I eα ≪≫
      (Functor.associator I _ _).symm ≪≫
        Functor.isoWhiskerRight c (ModuleCat.ringExtendScalars.{d + 1, d + 1} s) ≪≫
          Functor.associator Q J _ ≪≫
            Functor.isoWhiskerLeft Q (Functor.isoWhiskerLeft J eS) ≪≫
              Functor.isoWhiskerLeft Q
                (Functor.isoWhiskerLeft J (ModuleCat.extendScalarsComp.{d + 1, d + 1} t k))

/-- The integral comparison after rationalization, with standard tensor module structures. -/
def lisseIntegralRationalFiberKNatIso :
    let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    I ⋙ algebraTensorFunctor (A := E) ⋙ ModuleCat.extendScalars j ≅
    (lisseIntegralScalarExtensionData l E Y L ι).functor ⋙ J ⋙
      algebraTensorFunctor (A := L) ⋙ ModuleCat.extendScalars k := by
  let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let Q := (lisseIntegralScalarExtensionData l E Y L ι).functor
  exact Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight tensorAlgebraNatIso.symm (ModuleCat.extendScalars j)) ≪≫
    lisseIntegralScalarFiberKNatIso Y y l E L ι K j k hjk ≪≫
    Functor.isoWhiskerLeft Q (Functor.isoWhiskerLeft J
      (Functor.isoWhiskerRight tensorAlgebraNatIso (ModuleCat.extendScalars k)))

/-- The rational scalar comparison is built from integral scalar comparison and
associativity of scalar extension. -/
def lisseRationalScalarFiberIso (F : LisseRationalSheaf l E Y) :
    (ModuleCat.extendScalars j).obj (lisseRationalFiber l E Y y F) ≅
      (ModuleCat.extendScalars k).obj (lisseRationalFiber l L Y y
        ((lisseRationalScalarExtension l E Y L ι).obj F)) := by
  unfold lisseRationalScalarExtension lisseIntegralScalarExtension
  exact (lisseIntegralRationalFiberKNatIso Y y l E L ι K j k hjk).app F.integral
set_option maxRecDepth 2000
/-- Naturality of the rational comparison on integral morphisms. -/
theorem lisseRationalScalarFiberIso_integral_naturality
    (F G : LisseRationalSheaf l E Y) (f : F.integral ⟶ G.integral) :
    let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
    (ModuleCat.extendScalars j).map (ModuleCat.ofHom
        (LinearMap.baseChange E (I.map f).hom)) ≫
      (lisseRationalScalarFiberIso Y y l E L ι K j k hjk G).hom =
    (lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom ≫
      (ModuleCat.extendScalars k).map (ModuleCat.ofHom
        (LinearMap.baseChange L
          (J.map ((lisseIntegralScalarExtension l E Y L ι).map f)).hom)) := by
  with_unfolding_all
    exact (lisseIntegralRationalFiberKNatIso Y y l E L ι K j k hjk).hom.naturality f

variable
  (T : LisseRationalSheaf l E Y ⥤ ModuleCat.{d + 1} E)
  (U : LisseRationalSheaf l L Y ⥤ ModuleCat.{d + 1} L)
  (hT : ∀ F, T.obj F = lisseRationalFiber l E Y y F)
  (hU : ∀ F, U.obj F = lisseRationalFiber l L Y y F)

/-- Objectwise comparison for any functors with the prescribed geometric fibres. -/
def lisseRationalFiberComparison (F : LisseRationalSheaf l E Y) :
    (T ⋙ ModuleCat.extendScalars j).obj F ≅
      (lisseRationalScalarExtension l E Y L ι ⋙ U ⋙ ModuleCat.extendScalars k).obj F :=
  (ModuleCat.extendScalars j).mapIso (eqToIso (hT F)) ≪≫
    lisseRationalScalarFiberIso Y y l E L ι K j k hjk F ≪≫
      ((ModuleCat.extendScalars k).mapIso
        (eqToIso (hU ((lisseRationalScalarExtension l E Y L ι).obj F)))).symm

-- Transporting both fibre objects expands the two nested scalar-extension functors.
/-- Rational fibre comparisons are natural for all rational morphisms.
Clear a common denominator to write a morphism
as a single pure tensor. The defining morphism formulas reduce naturality to integral
naturality; its scalar coefficient acts through the same embedding into K on both sides. -/
theorem lisseRationalFiberComparison_naturality
    (mT : IsLisseRationalFiberFunctor Y y l E T hT)
    (mU : IsLisseRationalFiberFunctor Y y l L U hU)
    {F G : LisseRationalSheaf l E Y} (f : F ⟶ G) :
    (T ⋙ ModuleCat.extendScalars j).map f ≫
        (lisseRationalFiberComparison Y y l E L ι K j k hjk T U hT hU G).hom =
      (lisseRationalFiberComparison Y y l E L ι K j k hjk T U hT hU F).hom ≫
        (lisseRationalScalarExtension l E Y L ι ⋙ U ⋙
          ModuleCat.extendScalars k).map f := by
  have : IsFractionRing (Padic.coefficientExtensionIntegers l E) E :=
    (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.1
  obtain ⟨a, g, rfl⟩ := fractionTensorPure (F.integral ⟶ G.integral) f
  have hQ := (lisseRationalScalarExtensionData l E Y L ι).map_tmul F G a g
  change (lisseRationalScalarExtension l E Y L ι).map
    (TensorProduct.tmul _ a g) = _ at hQ
  dsimp only [Functor.comp_map]
  rw [mT F G a g, hQ, mU _ _ (ι a) _]
  simp only [lisseRationalFiberComparison, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, Iso.symm_hom, Functor.mapIso_inv, eqToIso.inv, Functor.map_comp,
    Category.assoc]
  simp only [mapEqCancel]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  let I := ObjectProperty.ι (IsLisseIntegralDiagram l E Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let J := ObjectProperty.ι (IsLisseIntegralDiagram l L Y) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber ⋙ lim
  let F' := (lisseRationalScalarExtension l E Y L ι).obj F
  let G' := (lisseRationalScalarExtension l E Y L ι).obj G
  let gE : lisseRationalFiber l E Y y F ⟶ lisseRationalFiber l E Y y G :=
    ModuleCat.ofHom (LinearMap.baseChange E
      (show lisseIntegralFiber l E Y y F.integral →ₗ[
          Padic.coefficientExtensionIntegers l E] lisseIntegralFiber l E Y y G.integral
        from (I.map g).hom))
  let gL : lisseRationalFiber l L Y y F' ⟶ lisseRationalFiber l L Y y G' :=
    ModuleCat.ofHom (LinearMap.baseChange L
      (show lisseIntegralFiber l L Y y F'.integral →ₗ[
          Padic.coefficientExtensionIntegers l L] lisseIntegralFiber l L Y y G'.integral
        from (J.map ((lisseIntegralScalarExtension l E Y L ι).map g)).hom))
  with_unfolding_all
    change (ModuleCat.extendScalars j).map (a • gE) ≫
        (lisseRationalScalarFiberIso Y y l E L ι K j k hjk G).hom =
      (lisseRationalScalarFiberIso Y y l E L ι K j k hjk F).hom ≫
        (ModuleCat.extendScalars k).map ((ι a) • gL)
  rw [scalarExtension_map_smul, scalarExtension_map_smul]
  have ha : k (ι a) = j a := congrArg (fun r : E →+* K ↦ r a) hjk
  rw [ha, Linear.smul_comp, Linear.comp_smul]
  with_unfolding_all
    exact congrArg (fun f ↦ j a • f)
      (lisseRationalScalarFiberIso_integral_naturality Y y l E L ι K j k hjk F G g)

/-- The natural comparison after extending both rational fibres to K. -/
def lisseRationalFiberComparisonNatIso
    (mT : IsLisseRationalFiberFunctor Y y l E T hT)
    (mU : IsLisseRationalFiberFunctor Y y l L U hU) :
    T ⋙ ModuleCat.extendScalars j ≅
      lisseRationalScalarExtension l E Y L ι ⋙ U ⋙ ModuleCat.extendScalars k :=
  NatIso.ofComponents (fun F ↦
    lisseRationalFiberComparison Y y l E L ι K j k hjk T U hT hU F)
      (fun f ↦ lisseRationalFiberComparison_naturality
        Y y l E L ι K j k hjk T U hT hU mT mU f)

end
end AlgebraicGeometry.Scheme
