/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Open extension preserves finite constructibility and cohomological intervals

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.7, open factor
* Stacks Project, Tags 09AH and 09BN
* Bhatt--Scholze, Lemma 6.7.7, preservation by the open factor
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem locallyConstant_universes_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheafOfUniverses Y A F) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses Y A G := by
  obtain ⟨I, U, f, hc, ht⟩ := hF
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := ht i
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ eM⟩⟩

private theorem locallyConstant_universes_of_isZero (Y : Scheme.{u}) (A : Type u)
    [CommRing A] (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheafOfUniverses Y A F := by
  obtain ⟨I, U, f, hc, ht⟩ := locallyConstant_of_isZero Y A F hF
  exact ⟨I, U, f, hc, fun i ↦ ⟨(ht i).choose, trivial, (ht i).choose_spec⟩⟩

private theorem pullback_extension_isZero {U W X : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A] (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Set.range j ∩ Set.range g = ∅)
    (H : proEtaleRingModules U (proEtaleConstantRing U A)) :
    IsZero (proEtaleConstantModulePullback g A ((sfIntrinsicExtensionByZero j A).obj H)) := by
  let L := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let P := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g
  have hz := ProEtale.isZero_upperStar_openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j g hjg
    ((sfIntrinsicModuleEquivalence U A).inverse.obj H)
  have hz' := (sfIntrinsicModuleEquivalence W A).functor.map_isZero hz
  exact (hz'.of_iso ((sfIntrinsicTransportComp A L P).symm.app H)).of_iso
    ((openSquarePullbackModel A g).app _)

private noncomputable def restriction_extension_iso {T U X : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A] (j : U ⟶ X) [IsOpenImmersion j] (s : T ⟶ U)
    (H : proEtaleRingModules U (proEtaleConstantRing U A)) :
    proEtaleConstantModulePullback (s ≫ j) A ((sfIntrinsicExtensionByZero j A).obj H) ≅
      proEtaleConstantModulePullback s A H := by
  have : (sfIntrinsicExtensionByZero j A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  exact (openSquarePullbackModel A (s ≫ j)).app _ ≪≫
    (sfIntrinsicPullbackComp A s j).app _ ≪≫
    (sfIntrinsicPullback A s).mapIso
      (asIso ((sfIntrinsicOpenAdjunction A j).unit.app H)).symm ≪≫
    (openSquarePullbackModel A s).symm.app H

private theorem extend_stratification {U V Z : Scheme.{u}} [IsNoetherian V]
    (j : U ⟶ V) [IsOpenImmersion j] (S : FiniteLocallyClosedStratification U)
    (i : Z ⟶ V) [IsClosedImmersion i] (hi : Set.range i = (Set.range j)ᶜ)
    (omitted : Set (Option (Fin S.n)))
    (hempty : ∀ q ∈ omitted, match q with
      | none => IsEmpty Z
      | some k => IsEmpty (S.domain k))
    (P : (T : Scheme.{u}) → (T ⟶ V) → Prop)
    (h₀ : P Z i) (hS : ∀ k, P (S.domain k) (S.immersion k ≫ j)) :
    ∃ (T : FiniteLocallyClosedStratification V)
      (e : Fin T.n ≃ {q : Option (Fin S.n) // q ∉ omitted}),
      (∀ k, Topology.IsConstructible (T.stratum k)) ∧
      (∀ k, match (e k).val with
        | none => Nonempty (Over.mk (T.immersion k) ≅ Over.mk i)
        | some a => Nonempty (Over.mk (T.immersion k) ≅ Over.mk (S.immersion a ≫ j))) ∧
      ∀ k, P (T.domain k) (T.immersion k) := by
  classical
  let D : Option (Fin S.n) → Over V := fun q ↦ match q with
    | none => Over.mk i
    | some a => Over.mk (S.immersion a ≫ j)
  have himm : ∀ q, IsImmersion (D q).hom := by
    rintro (_ | a)
    · exact inferInstanceAs (IsImmersion i)
    · have := S.isImmersion a
      exact inferInstanceAs (IsImmersion (S.immersion a ≫ j))
  have hdisj : Pairwise (Function.onFun Disjoint (fun q ↦ Set.range (D q).hom)) := by
    rintro (_ | a) (_ | b) hab
    · exact (hab rfl).elim
    · apply Set.disjoint_left.mpr
      rintro x hx ⟨z, rfl⟩
      change (S.immersion b ≫ j) z ∈ Set.range i at hx
      rw [hi] at hx
      exact hx ⟨S.immersion b z, rfl⟩
    · apply Set.disjoint_left.mpr
      rintro x ⟨z, rfl⟩ hx
      change (S.immersion a ≫ j) z ∈ Set.range i at hx
      rw [hi] at hx
      exact hx ⟨S.immersion a z, rfl⟩
    · apply Set.disjoint_left.mpr
      rintro x ⟨z, rfl⟩ ⟨w, hw⟩
      have he := j.isOpenEmbedding.injective hw
      exact Set.disjoint_left.mp
        (S.pairwise_disjoint_stratum (fun h ↦ hab (congrArg some h)))
        ((S.range_immersion a) ▸ Set.mem_range_self z)
        ((S.range_immersion b) ▸ ⟨w, he⟩)
  have hcov : ∀ x : V, ∃ q, x ∈ Set.range (D q).hom := by
    intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hx
      have hy : y ∈ ⋃ a, S.stratum a := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      rw [← S.range_immersion a] at ha
      obtain ⟨z, rfl⟩ := ha
      exact ⟨some a, z, rfl⟩
    · exact ⟨none, hi.symm ▸ hx⟩
  let Q := {q : Option (Fin S.n) // q ∉ omitted}
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  let T : FiniteLocallyClosedStratification V :=
    { n := Fintype.card Q
      stratum := fun k ↦ Set.range (D (e k).val).hom
      domain := fun k ↦ (D (e k).val).left
      immersion := fun k ↦ (D (e k).val).hom
      isImmersion := fun k ↦ himm _
      range_immersion := fun _ ↦ rfl
      isLocallyClosed_stratum := fun k ↦ by
        have := himm (e k).val
        exact (D (e k).val).hom.isLocallyClosed_range
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨q, z, rfl⟩ := hcov x
        have hq : q ∉ omitted := by
          intro hq
          have hz : IsEmpty (D q).left := by
            cases q with
            | none => exact hempty none hq
            | some a => exact hempty (some a) hq
          exact hz.false z
        refine Set.mem_iUnion.mpr ⟨e.symm ⟨q, hq⟩, ?_⟩
        rw [e.apply_symm_apply]
        exact ⟨z, rfl⟩
      pairwise_disjoint_stratum := fun a b hab ↦ hdisj
        (fun h ↦ hab (e.injective (Subtype.ext h))) }
  refine ⟨T, e, fun k ↦ ?_, ?_, ?_⟩
  · exact (T.isLocallyClosed_stratum k).isConstructible_of_noetherianSpace
  · intro k
    change match (e k).val with
      | none => Nonempty (Over.mk (D (e k).val).hom ≅ Over.mk i)
      | some a => Nonempty (Over.mk (D (e k).val).hom ≅
          Over.mk (S.immersion a ≫ j))
    cases (e k).val <;> exact ⟨Iso.refl _⟩
  · intro k
    change P (D (e k).val).left (D (e k).val).hom
    cases (e k).val with
    | none => exact h₀
    | some a => exact hS a

set_option linter.unusedVariables false in
/-- Open extension preserves bounded finite-torsion constructibility and each supplied
cohomological interval. -/
theorem open_finite_constructibility_interval
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U V : Scheme.{u}} [IsNoetherian V] (j : U ⟶ V) [IsOpenImmersion j]
    (_hl : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (a b : ℤ) (_hab : a ≤ b)
    (C : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n))
    (_hC : intrinsicFiniteTorsionConstructible l E n hn U C)
    (_hC_support : proEtaleCohomologicalSupport C ⊆ Set.Icc a b) :
    (fun [hfin : Finite (Padic.coefficientExtensionRing l E n)]
      [hU : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
      [hV : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] ↦
      intrinsicFiniteTorsionConstructible l E n hn V
        ((sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
        C) ∧
        proEtaleCohomologicalSupport
          ((sfIntrinsicExtensionByZero j
            (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
          C) ⊆ Set.Icc a b ∧
        (∀ r : ℤ, Nonempty
          (((DerivedCategory.homologyFunctor
            (proEtaleRingModules V
              (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                ((sfIntrinsicExtensionByZero j
                  (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                C)) ≅
            (sfIntrinsicExtensionByZero j
              (Padic.coefficientExtensionRing l E n)).obj
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) ∧
        (∀ (r : ℤ) (S : FiniteLocallyClosedStratification U),
          (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
          (∀ k : Fin S.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
            (S.domain k) (Padic.coefficientExtensionRing l E n)
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) →
          (∀ (k : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (x : Spec (.of Ω) ⟶ S.domain k),
            Finite (proEtaleGeometricModuleStalk x
              (proEtaleConstantRing (S.domain k) (Padic.coefficientExtensionRing l E n))
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C)))) →
          ∀ (Z : Scheme.{u}) (i : Z ⟶ V) [IsClosedImmersion i] [IsReduced Z],
            Set.range i = (Set.range j)ᶜ →
            (∀ omitted : Set (Option (Fin S.n)),
              (∀ q ∈ omitted, match q with
                | none => IsEmpty Z
                | some h => IsEmpty (S.domain h)) →
              ∃ (T : FiniteLocallyClosedStratification V)
                  (e : Fin T.n ≃ {q : Option (Fin S.n) // q ∉ omitted}),
                (∀ k : Fin T.n, Topology.IsConstructible (T.stratum k)) ∧
                (∀ k : Fin T.n, match (e k).val with
                  | none => Nonempty (Over.mk (T.immersion k) ≅ Over.mk i)
                  | some h => Nonempty (Over.mk (T.immersion k) ≅
                      Over.mk (S.immersion h ≫ j))) ∧
                (∀ k : Fin T.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
                  (T.domain k) (Padic.coefficientExtensionRing l E n)
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules V
                          (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))) ∧
                (∀ (k : Fin T.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                  (x : Spec (.of Ω) ⟶ T.domain k),
                  Finite (proEtaleGeometricModuleStalk x
                    (proEtaleConstantRing (T.domain k) (Padic.coefficientExtensionRing l E n))
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules V
                          (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))))) ∧
            IsZero (proEtaleConstantModulePullback i (Padic.coefficientExtensionRing l E n)
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules V
                  (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                    ((sfIntrinsicExtensionByZero j
                      (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                    C)))))
      (hfin := Padic.finite_coefficientExtensionRing l E n hn)
      (hU := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} U)
      (hV := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} V) := by
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} U
  let : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} V
  let A : Type u := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F := sfIntrinsicExtensionByZero.{u} j A
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · apply _hC.1.subset
      intro r hr hz
      exact hr (F.isZero_homologyFunctor_mapDerivedCategory_obj (X := C) hz)
    · intro r
      rw [proEtaleModuleRestriction_constructible_iff]
      exact ProEtale.isConstructible_of_iso
        ((proEtaleModuleRestriction V A).mapIso
          ((F.mapDerivedCategoryHomologyFunctorIso r).app C))
        ((proEtaleModuleRestriction_constructible_iff V A _).mp
          (extension_constructible j A _ (_hC.2 r)))
  · intro r hr
    apply _hC_support
    intro hz
    exact hr (F.isZero_homologyFunctor_mapDerivedCategory_obj (X := C) hz)
  · intro r
    exact ⟨(F.mapDerivedCategoryHomologyFunctorIso r).symm.app C⟩
  · intro r S _hS hl hs Z i _ _ hi
    let H := (DerivedCategory.homologyFunctor
      (proEtaleRingModules U (proEtaleConstantRing U A)) r).obj C
    let K := (DerivedCategory.homologyFunctor
      (proEtaleRingModules V (proEtaleConstantRing V A)) r).obj
        (F.mapDerivedCategory.obj C)
    let eH : K ≅ F.obj H := (F.mapDerivedCategoryHomologyFunctorIso r).symm.app C
    have hz : IsZero (proEtaleConstantModulePullback i A K) := by
      have hz' := pullback_extension_isZero A j i (by
        rw [hi]
        exact Set.inter_compl_self _) H
      exact hz'.of_iso ((proEtaleConstantRingPullback A i).mapIso eH)
    refine ⟨?_, hz⟩
    intro omitted hempty
    let P := fun (T : Scheme.{u}) (s : T ⟶ V) ↦
      IsLocallyConstantProEtaleModuleSheafOfUniverses T A
        (proEtaleConstantModulePullback s A K) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T A)
          (proEtaleConstantModulePullback s A K))
    have h₀ : P Z i := ⟨locallyConstant_universes_of_isZero Z A _ hz,
      fun Ω _ _ x ↦ finite_stalk_of_isZero Z A _ hz x⟩
    have hstrata : ∀ k, P (S.domain k) (S.immersion k ≫ j) := by
      intro k
      let er : proEtaleConstantModulePullback (S.immersion k ≫ j) A K ≅
          proEtaleConstantModulePullback (S.immersion k) A H :=
        (proEtaleConstantRingPullback A (S.immersion k ≫ j)).mapIso eH ≪≫
          restriction_extension_iso A j (S.immersion k) H
      refine ⟨locallyConstant_universes_of_iso _ A er.symm (hl k), ?_⟩
      intro Ω _ _ x
      have := hs k Ω x
      exact finite_stalk_of_iso _ A er.symm x
    obtain ⟨T, e, hc, he, hP⟩ :=
      extend_stratification j S i hi omitted hempty P h₀ hstrata
    exact ⟨T, e, hc, he, fun k ↦ (hP k).1, fun k ↦ (hP k).2⟩

end AlgebraicGeometry.Scheme
