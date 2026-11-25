/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement

/-!
# Normalization of continuous lisse coefficients

Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

private noncomputable def coefficientLiftAlgEquiv (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] : ULift.{u} E ≃ₐ[ℚ_[l]] E :=
  { ULift.ringEquiv with commutes' := fun _ ↦ rfl }

private theorem coefficientLiftAbsoluteValue (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (x : ULift.{u} E) :
    Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E) x =
      Padic.coefficientExtensionAbsoluteValue l E x.down := by
  change spectralNorm ℚ_[l] (ULift.{u} E) x = spectralNorm ℚ_[l] E x.down
  unfold spectralNorm
  rw [← minpoly.algEquiv_eq (coefficientLiftAlgEquiv l E) x]
  rfl

private noncomputable def coefficientWithAbsLiftRingEquiv (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E)) ≃+* E :=
  (WithAbs.equiv _).trans ULift.ringEquiv

private theorem coefficientWithAbsLift_isometry (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := spectralNorm.normedField ℚ_[l] E
    Isometry (coefficientWithAbsLiftRingEquiv.{u} l E) := by
  let := spectralNorm.normedField ℚ_[l] E
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact (coefficientLiftAbsoluteValue l E x.ofAbs).symm

private theorem coefficientIntegers_mem (l : ℕ) [Fact l.Prime] (E : Type*) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (x : E) :
    x ∈ Padic.coefficientExtensionIntegers l E ↔
      Padic.coefficientExtensionAbsoluteValue l E x ≤ 1 :=
  Padic.mem_coefficientExtensionIntegers l E x


private noncomputable def coefficientWithAbsLiftIntegerRingEquiv (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    latticeCoefficientIntegers l (ULift.{u} E) ≃+* Padic.coefficientExtensionIntegers l E :=
  (coefficientWithAbsLiftRingEquiv l E).restrict _ _ (by
    intro x
    change x.ofAbs ∈ Padic.coefficientExtensionIntegers l (ULift.{u} E) ↔ _
    rw [Padic.mem_coefficientExtensionIntegers, Padic.mem_coefficientExtensionIntegers,
      coefficientLiftAbsoluteValue]
    rfl)

private theorem coefficientWithAbsLiftInteger_isometry (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := spectralNorm.normedField ℚ_[l] E
    Isometry (coefficientWithAbsLiftIntegerRingEquiv.{u} l E) := by
  let := spectralNorm.normedField ℚ_[l] E
  intro x y
  exact coefficientWithAbsLift_isometry l E x.val y.val

private noncomputable def continuousMapRingEquiv {K : Type v} {E : Type w}
    [CommRing K] [CommRing E] [TopologicalSpace K] [TopologicalSpace E]
    [IsTopologicalRing K] [IsTopologicalRing E]
    (e : K ≃+* E) (he : Continuous e) (hi : Continuous e.symm)
    (V : Type*) [TopologicalSpace V] : C(V, K) ≃+* C(V, E) :=
  { e.toRingHom.compLeftContinuous V he with
    invFun := e.symm.toRingHom.compLeftContinuous V hi
    left_inv f := by ext x; exact e.symm_apply_apply (f x)
    right_inv f := by ext x; exact e.apply_symm_apply (f x) }

private noncomputable def coefficientFieldSheafIso (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    latticeCoefficientSheaf X
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E))) ≅
      lisseFieldSheaf l E X := by
  letI := spectralNorm.normedField ℚ_[l] E
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E)) ≃ᵢ E :=
    { (coefficientWithAbsLiftRingEquiv l E).toEquiv with
      isometry_toFun := coefficientWithAbsLift_isometry l E }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (coefficientWithAbsLiftRingEquiv l E)
      e.continuous e.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V V' f
  rfl

private noncomputable def coefficientIntegerSheafIso (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l (ULift.{u} E)) ≅
      lisseIntegerSheaf l E X := by
  letI := spectralNorm.normedField ℚ_[l] E
  let e : latticeCoefficientIntegers l (ULift.{u} E) ≃ᵢ
      Padic.coefficientExtensionIntegers l E :=
    { (coefficientWithAbsLiftIntegerRingEquiv l E).toEquiv with
      isometry_toFun := coefficientWithAbsLiftInteger_isometry l E }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv
      (coefficientWithAbsLiftIntegerRingEquiv l E)
      e.continuous e.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V V' f
  rfl

private theorem coefficientSheafIso_square (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    integralLatticeCoefficientMap X l (ULift.{u} E) ≫ (coefficientFieldSheafIso l E X).hom =
      (coefficientIntegerSheafIso l E X).hom ≫ lisseIntegerToField l E X := by
  apply Sheaf.hom_ext
  ext V s
  rfl

private noncomputable def coefficientUnitIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (e : S ≅ R) :
    (SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.restrictScalarsIsoOfEquiv
    ((((sheafToPresheaf J RingCat).mapIso e).app V).ringCatIsoToRingEquiv)) ?_
  intro V V' f
  ext s
  change e.inv.hom.app V' (R.obj.map f s) = S.obj.map f (e.inv.hom.app V s)
  exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) s

/-- Restricting scalars along an isomorphism of coefficient sheaves preserves finite local
freeness. The same local cover and finite generating sets give the transported free
presentations.
Source: Bhatt--Scholze, Proposition 6.8.4(6), identification of lattice coefficients.
(auxiliary; not a blueprint node) -/
theorem finiteLocallyFree_restrict {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u + 1}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (e : S ≅ R)
    (L : SheafOfModules.{u + 1} R) [h : L.IsFiniteLocallyFree] :
    ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj L).IsFiniteLocallyFree := by
  classical
  obtain ⟨q, hq, hf⟩ := h.exists_localGeneratorsData
  have := hq
  let ρ (V : C) : S.over V ⟶ R.over V :=
    ((Over.forget V).sheafPushforwardContinuous RingCat.{u + 1} (J.over V) J).map e.hom
  have hpush (V : C) :
      (SheafOfModules.pushforward (F := 𝟭 (Over V))
        (R := R.over V) (S := S.over V) (ρ V)).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso
      (F := 𝟭 (Over V)) (R := R.over V) (S := S.over V) (ρ V)
  let q' : ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj L).LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i ↦ by
        have := hpush (q.X i)
        exact (q.generators i).map
          (SheafOfModules.pushforward (F := 𝟭 (Over (q.X i)))
          (R := R.over (q.X i)) (S := S.over (q.X i)) (ρ (q.X i)))
          (coefficientUnitIso (J.over (q.X i))
            (((Over.forget (q.X i)).sheafPushforwardContinuous RingCat.{u + 1}
              (J.over (q.X i)) J).mapIso e)).symm }
  have : q'.IsLocallyFreeData := by
    constructor
    intro i
    have := hpush (q.X i)
    dsimp [q']
    infer_instance
  apply SheafOfModules.IsFiniteLocallyFree.mk
  refine ⟨q', inferInstance, ?_⟩
  constructor
  intro i
  have := hpush (q.X i)
  have := hf.isFiniteType i
  dsimp [q']
  infer_instance

private noncomputable def coefficientNormalizedModule (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X))) :
    SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E)))) :=
  (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientFieldSheafIso l E X).hom)).obj L

private theorem coefficientNormalizedModule_finiteLocallyFree (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    [L.IsFiniteLocallyFree] : (coefficientNormalizedModule l E X L).IsFiniteLocallyFree := by
  let J := Scheme.ProEt.topology X
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (lisseFieldSheaf l E X)
  let S := latticeModuleRing X
    (WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E)))
  let e : S ≅ R := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (coefficientFieldSheafIso l E X)
  exact finiteLocallyFree_restrict J R S e L

/-- The lifted `WithAbs` coefficient presentation is isomorphic to the original
spectral-norm presentation. Its coefficient square commutes, and transporting modules
along the rational isomorphism preserves finite local freeness.
Source: Bhatt--Scholze, Definition 6.8.1 and Proposition 6.8.4(6).
(auxiliary; not a blueprint node)

Proof: the lift algebra equivalence preserves minimal polynomials, hence the spectral
absolute value. It gives an isometric ring equivalence from the `WithAbs` lift to E.
The valuation rings agree under it by their characterization as absolute value at most
one. Postcomposition with these equivalences gives isomorphisms on continuous
functions, naturally in the test scheme, and their square commutes pointwise.
For finite local freeness, restrict scalars along the rational isomorphism. Transport
the module's local free generators on the original cover. On each covering slice the
pushforward is along the identity functor and an invertible coefficient morphism, so
it preserves colimits and identifies the unit modules. The transported generating
sets remain finite and their free presentations remain isomorphisms. -/
theorem lisse_coefficient_normalization (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ eA : latticeCoefficientSheaf X (latticeCoefficientIntegers l (ULift.{u} E)) ≅
        lisseIntegerSheaf l E X,
      ∃ eE : latticeCoefficientSheaf X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} E))) ≅
            lisseFieldSheaf l E X,
        integralLatticeCoefficientMap X l (ULift.{u} E) ≫ eE.hom =
          eA.hom ≫ lisseIntegerToField l E X ∧
        SheafOfModules.IsFiniteLocallyFree
          ((SheafOfModules.pushforward (F := 𝟭 X.ProEt)
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eE.hom)).obj L) := by
  have := hL
  exact ⟨coefficientIntegerSheafIso l E X, coefficientFieldSheafIso l E X,
    coefficientSheafIso_square l E X,
    coefficientNormalizedModule_finiteLocallyFree l E X L⟩

end AlgebraicGeometry.ProEtale
