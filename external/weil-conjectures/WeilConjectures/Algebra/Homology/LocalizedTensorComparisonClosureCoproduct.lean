/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonRepresentativeSquare
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian

/-! # Coproduct closure of the localized tensor comparison predicate

Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.
(blueprint: lem-pc-localized-tensor-comparison-closure-coproducts).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

private theorem acyclic_coproduct {A : Type u} [CommRing A] {I : Type u}
    (L : I → CochainComplex (ModuleCat.{u} A) ℤ) (hL : ∀ j, (L j).Acyclic) :
    (∐ L).Acyclic := by
  let Z : I → CochainComplex (ModuleCat.{u} A) ℤ := fun _ ↦ HomologicalComplex.zero
  let f : ∀ j, Z j ⟶ L j := fun _ ↦ 0
  have hf (j : I) : QuasiIso (f j) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt (f j) i
      ((HomologicalComplex.acyclic_of_isZero _ HomologicalComplex.isZero_zero) i)).2
        (hL j i)
  have hq : QuasiIso (Limits.Sigma.map f) :=
    MorphismProperty.colimMap
      (W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
      (show Discrete.functor Z ⟶ Discrete.functor L from
        Discrete.natTrans fun j ↦ f j.as) (fun ⟨j⟩ ↦ hf j)
  have hz : IsZero (∐ Z) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Limits.Sigma.hom_ext
    intro j
    exact HomologicalComplex.isZero_zero.eq_of_src _ _
  intro i
  exact (quasiIsoAt_iff_exactAt (Limits.Sigma.map f) i
    ((HomologicalComplex.acyclic_of_isZero _ hz) i)).1 inferInstance

private theorem kFlat_coproduct {A : Type u} [CommRing A] {I : Type u}
    (U : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : ∀ j (V : CochainComplex (ModuleCat.{u} A) ℤ), V.Acyclic →
      (CochainComplex.mapBifunctor V (U j) (curriedTensor _)).Acyclic) :
    ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V (∐ U) (curriedTensor _)).Acyclic := by
  intro V hV
  let T := ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj V
  have hsum := acyclic_coproduct (fun j ↦ T.obj (U j)) (fun j ↦ hU j V hV)
  have e := PreservesCoproduct.iso T U
  intro i
  exact (hsum i).of_iso e.symm

private theorem exists_kFlat_representative {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (X : DerivedCategory (ModuleCat.{u} A)) :
    ∃ U : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj U ≅ X) ∧
      ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
        (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic := by
  classical
  let K := DerivedCategory.Q.objPreimage X
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  let U := Λ.resolutionFunctor.obj K
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  refine ⟨U, ⟨asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K)) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩, ?_⟩
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hk
  intro V hV
  have hV' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic V).2 hV
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V U (curriedTensor _))).1 (hk _ hV').2

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- The localized tensor comparison predicate is closed under coproducts.
Source: Stacks Project, Tags 0DJA(1), 0BYJ and 09PB.

Proof: Choose K-flat representatives U_j of the summands using the functorial
flat resolution. Tensor commutes with sums; exactness of module sums shows that
their sum is K-flat. The derived module direct-sum theorem identifies its image
under Q with the specified coproduct S. Choose a base-derived model for each
U_j tensor Q and one for their sum tensor Q. The direct-sum comparison square
identifies the latter comparison, up to source and target isomorphisms, with
the coproduct of the summand comparisons. Each summand comparison is invertible
by the given predicate. Sigma.map preserves these isomorphisms, so cancellation
of the source comparison isomorphism proves invertibility on the sum in every
degree. For any K-flat representative V of S and any model, apply the existing
representative-square theorem to V and the sum; its two isomorphisms transport
invertibility to V. This gives exactly the all-representatives and all-models
predicate. The constructions include an empty family: the coproduct of zero
complexes and every coproduct comparison used above are zero-object maps.
(blueprint: lem-pc-localized-tensor-comparison-closure-coproducts). -/
theorem localizedTensorComparisonProperty_closure_coproducts
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
      (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S),
      CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι) →
      (∀ i, localizedTensorComparisonProperty R A B C Q N t (G i)) →
      localizedTensorComparisonProperty R A B C Q N t S := by
  classical
  intro I G S ι hι hG
  choose U eU hU using fun j ↦ exists_kFlat_representative (G j)
  let eU := fun j ↦ (eU j).some
  let a : Discrete.functor (fun j ↦ DerivedCategory.Q.obj (U j)) ≅
      Discrete.functor G := Discrete.natIso (fun j ↦ eU j.as)
  let c := (Cocone.precompose a.hom).obj (Cofan.mk S ι)
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv a _).symm hι
  have hsum := (derivedModuleDirectSums A I U).some
  let eS : DerivedCategory.Q.obj (∐ U) ≅ S := hsum.coconePointUniqueUpToIso hc
  have hUS := kFlat_coproduct U hU
  let m := fun j ↦ (nonempty_baseDerivedTensorCohomologyModel R A B (U j ⊗ Q) C).some
  obtain ⟨mS⟩ := nonempty_baseDerivedTensorCohomologyModel R A B ((∐ U) ⊗ Q) C
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  have hα (i : ℤ) : IsIso (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t)) i) := by
    let α := fun j ↦ (m j).localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U j) Q).inv ≫ (F.obj (U j) ◁ t)) i
    have (j : I) : IsIso (α j) := hG j (U j) ⟨eU j⟩ (hU j) (m j) i
    obtain ⟨e, d, hsquare⟩ := exists_localizedTensorComparison_direct_sum_square
      R A B C Q N t U m mS i
    have : IsIso (e.hom ≫ (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
        ((Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t)) i)) := by
      rw [← hsquare]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  intro V hV0 hV mV i
  obtain ⟨eV⟩ := hV0
  obtain ⟨e, d, hsquare⟩ := exists_localizedTensorComparison_representative_square
    R A B C Q N t hQ V (∐ U) hV hUS (eV ≪≫ eS.symm) mV mS i
  have := hα i
  have : IsIso ((mV.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) i) ≫ d.hom) := by
    rw [hsquare]
    infer_instance
  exact IsIso.of_isIso_comp_right _ d.hom

/-- Fixed representative, model, and degree component of coproduct closure.
Source: Stacks Project, Tag 0DJA(1), coproduct component of the localizing argument.
Proof: apply the proved all-representatives coproduct closure theorem to the
given cocone and summand predicates, then specialize to U, e, hU, mU and i.
(blueprint: lem-pc-localized-tensor-comparison-closure-coproducts-fixed-degree). -/
theorem localizedTensorComparisonProperty_closure_coproducts_fixed_degree
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {I : Type u} (G : I → DerivedCategory (ModuleCat.{u} A))
    (S : DerivedCategory (ModuleCat.{u} A)) (ι : ∀ i, G i ⟶ S)
    (hc : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk S ι))
    (hs : ∀ i, localizedTensorComparisonProperty R A B C Q N t (G i))
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : Nonempty (DerivedCategory.Q.obj U ≅ S))
    (hU : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  exact localizedTensorComparisonProperty_closure_coproducts
    R A B C Q N t hQ G S ι hc hs U e hU mU i


end ModuleCat
