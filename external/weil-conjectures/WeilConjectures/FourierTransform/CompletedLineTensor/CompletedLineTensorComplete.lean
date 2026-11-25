/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteUnrestrictedIso
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedDirectImagePreservesCompleteness
public import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence

/-! # Tensor by a signed line preserves derived completeness

Source: Bhatt--Scholze, Definition 3.5.2; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
-/

@[expose] public noncomputable section

universe uC vC r m

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}}

set_option backward.isDefEq.respectTransparency false in
/-- Tensor with a fixed right factor commutes with multiplication by a global section.
Source: Stacks, Section 03EK (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on sectionwise pure tensors `(s • x) ⊗ y = s • (x ⊗ y)`. The sheafification unit
commutes with multiplication by `s`, and maps out of a sheafification are determined
by their composite with the unit. -/
theorem siteSheafTensorRight_map_sectionsSMul
    (N M : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (s : RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    (siteSheafTensorRight N).map
        (⟨PresheafOfModules.sectionsSMul (S := A.obj) M.val s⟩ : M ⟶ M) =
      ⟨PresheafOfModules.sectionsSMul (S := A.obj) ((siteSheafTensorRight N).obj M).val s⟩ := by
  let := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  let := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)
  have ht : siteTensorHom (PresheafOfModules.sectionsSMul (S := A.obj) M.val s) N.val =
      PresheafOfModules.sectionsSMul (S := A.obj) (siteTensorPresheaf M.val N.val) s := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    exact (TensorProduct.smul_tmul' (R := A.obj.obj U) (R' := A.obj.obj U) (s.1 U) x y).symm
  have hn := adj.unit.naturality
    (siteTensorHom (PresheafOfModules.sectionsSMul (S := A.obj) M.val s) N.val)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [ht] at hn
  apply (adj.homEquiv _ _).injective
  refine (adj.homEquiv_unit _ _ _).trans (Eq.trans ?_ (adj.homEquiv_unit _ _ _).symm)
  refine hn.symm.trans ?_
  exact (PresheafOfModules.sectionsSMul_naturality (adj.unit.app _) s).symm

end SheafOfModules

set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

/-- The uniformizer sections, as a compatible family of global sections.
Source: Stacks 0A0E (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def uniformizerSection :
    RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙ forget₂ CommRingCat RingCat) :=
  ⟨fun U ↦ integralCompletionScalarValue l E X U, fun f ↦ integralScalar_natural l E X f⟩

/-- Tensor by a signed line commutes with multiplication by the uniformizer on complexes.
Source: Stacks 03EK, 0A0E (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: in every degree the uniformizer endomorphism is multiplication by a global
section, and sheaf tensor commutes with such multiplications. -/
theorem complex_map_koszulScalar (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) (P : CochainComplex (integralTowerModules l E X) ℤ)
    (q : ℤ) (U : X.ProEtᵒᵖ) (x : ((((complex l E X L m).obj P).X q).val.obj U)) :
    ((((complex l E X L m).map (integralKoszulScalar l E X P).asHom).f q).val.app U) x =
      integralCompletionScalarValue l E X U • x := by
  have hμ : (integralKoszulScalar l E X P).asHom.f q =
      ⟨PresheafOfModules.sectionsSMul (S := (completedIntegralCommRingSheafUnrestricted l E X).obj)
        (P.X q).val (uniformizerSection l E X)⟩ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext y
    exact ((integralKoszulScalar_existsUnique l E X P).exists.choose_spec q V y).trans rfl
  have h := SheafOfModules.siteSheafTensorRight_map_sectionsSMul (power l E X L m) (P.X q)
    (uniformizerSection l E X)
  simp only [complex, Functor.mapHomologicalComplex_map_f, hμ]
  erw [h]
  rfl

/-- Signed line tensor is an equivalence, so it preserves countable products.
Source: Stacks 03EO (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem sheaf_preservesProducts (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ) (sheaf l E X L m) := by
  let f : sheaf l E X L (-m) ⋙ sheaf l E X L m ≅ 𝟭 _ := by
    simpa only [neg_neg] using evaluation l E X L (-m)
  let : (sheaf l E X L m).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (sheaf l E X L m) (sheaf l E X L (-m))
      (evaluation l E X L m).symm f).isEquivalence_functor
  infer_instance

/-- Tensor by a signed line preserves the specified augmented quotient-tower completeness.
Source: Bhatt--Scholze, Definition 3.5.2; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: choose a representative P of K, and let mu be multiplication by the uniformizer.
Completeness of K makes the principal completion unit of mu a quasi-isomorphism. The exact
tensor functor sends it to an isomorphism, commutes with the cone tower and countable
products (it is an equivalence), and sends mu to multiplication by the uniformizer.
So the twist of K is isomorphic to a principal completion, which is locally complete
by the local criterion; the datum-independent Roos equivalence concludes. -/
theorem complete (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E X ((tensor l E X L m).obj K) := by
  obtain ⟨D, hl, -⟩ := id hK
  have : Fact D.p.Prime := ⟨D.prime⟩
  have := sheaf_preservesProducts l E X L m
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let μ := integralKoszulScalar l E X P
  have : QuasiIso (CochainComplex.PrincipalCone.unit μ) :=
    (complete_iff_principalUnit D.p l hl.symm E X P).mp
      (isDerivedCompleteUnrestricted_of_iso l E X e.symm hK)
  let a : (tensor l E X L m).obj K ≅
      DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (End.of ((complex l E X L m).map μ.asHom))) :=
    (tensor l E X L m).mapIso e.symm ≪≫
      (tensor l E X L m).mapIso (asIso (DerivedCategory.Q.map
        (CochainComplex.PrincipalCone.unit μ))) ≪≫
      (sheaf l E X L m).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso (principalMapIso (sheaf l E X L m) μ)
  have hc := (IntegralPrincipalCone.localCriterion l E X
    (integralCompletionScalarValue l E X) (integralScalar_natural l E X)
    ((complex l E X L m).obj P) (End.of ((complex l E X L m).map μ.asHom))
    (complex_map_koszulScalar l E X L m P) _ (Iso.refl _)).1
  exact (complete_iff_local D.p l hl.symm E X _).mpr
    (integralLocallyComplete_iso l E X _ a.symm hc)

end CompletedLineTensor
end WeilConjectures
