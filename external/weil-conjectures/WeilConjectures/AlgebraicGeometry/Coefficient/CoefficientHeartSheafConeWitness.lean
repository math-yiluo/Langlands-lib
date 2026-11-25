/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # The sheaf part of coefficient generation
Source: blueprint generation, Single sheaves paragraph.
(blueprint: lem-sfb-coefficient-heart-sheaf-cone-witness)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def constructionValid {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    {n : ℕ} (F : Fin n → C) : Prop :=
  ∀ r, G (F r) ∨ ∃ i j, i < r ∧ j < r ∧ R (F i) (F j) (F r)

private def constructionWitness {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    (K : C) : Prop :=
  ∃ (N : ℕ) (F : Fin (N + 1) → C), F (Fin.last N) = K ∧ constructionValid G R F

private theorem constructionValid_append {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {m n : ℕ} {F : Fin m → C} {H : Fin n → C}
    (hF : constructionValid G R F) (hH : constructionValid G R H) :
    constructionValid G R (Fin.append F H) := by
  intro r
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r
  · rcases hF r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.castAdd n, j.castAdd n, ?_, ?_, ?_⟩
      · exact hi
      · exact hj
      · simpa using h
  · rcases hH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.natAdd m, j.natAdd m, ?_, ?_, ?_⟩
      · simpa using hi
      · simpa using hj
      · simpa using h

private theorem constructionWitness_generator {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : G K) : constructionWitness G R K := by
  exact ⟨0, fun _ ↦ K, rfl, fun _ ↦ Or.inl hK⟩

private theorem constructionWitness_step {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {A B K : C}
    (hA : constructionWitness G R A) (hB : constructionWitness G R B)
    (hK : R A B K) : constructionWitness G R K := by
  obtain ⟨m, F, hF, hvF⟩ := hA
  obtain ⟨n, H, hH, hvH⟩ := hB
  refine ⟨(m + 1) + (n + 1), Fin.snoc (Fin.append F H) K, by simp, ?_⟩
  intro r
  refine Fin.lastCases ?_ (fun r ↦ ?_) r
  · right
    refine ⟨((Fin.last m).castAdd (n + 1)).castSucc,
      ((Fin.last n).natAdd (m + 1)).castSucc, ?_, ?_, ?_⟩
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_last _
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left,
        Fin.append_right, hF, hH] using hK
  · rcases constructionValid_append hvF hvH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨i.castSucc, j.castSucc, hi, hj, by simpa using h⟩

private def coneRelation {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (U V W : DerivedCategory A) : Prop :=
  ∃ (n : ℤ) (f : U ⟶ V) (g : V ⟶ W⟦n⟧) (h : W⟦n⟧ ⟶ U⟦(1 : ℤ)⟧),
    Pretriangulated.Triangle.mk f g h ∈ distTriang _

private theorem constructionWitness_triangle {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop)
    (T : Pretriangulated.Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : constructionWitness G (coneRelation (A := A)) T.obj₁)
    (h₂ : constructionWitness G (coneRelation (A := A)) T.obj₂) :
    constructionWitness G (coneRelation (A := A)) T.obj₃ := by
  apply constructionWitness_step h₁ h₂
  let e := (shiftFunctorZero (DerivedCategory A) ℤ).app T.obj₃
  refine ⟨0, T.mor₁, T.mor₂ ≫ e.inv, e.hom ≫ T.mor₃, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT
  exact Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp)

private theorem constructionWitness_filtration {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop) (m : ℕ)
    (B : Fin (m + 1) → A) (f : ∀ a : Fin m, B a.castSucc ⟶ B a.succ)
    (hf : ∀ a, Mono (f a)) (n : ℤ) (hz : IsZero (B 0))
    (hzero : ∀ Z : DerivedCategory A, IsZero Z → constructionWitness G (coneRelation (A := A)) Z)
    (hg : ∀ a, G ((((DerivedCategory.singleFunctor A 0).obj (cokernel (f a)))⟦n⟧)
      ⟦(-1 : ℤ)⟧)) :
    constructionWitness G (coneRelation (A := A))
      (((DerivedCategory.singleFunctor A 0).obj (B (Fin.last m)))⟦n⟧) := by
  have tower (k : ℕ) (hk : k < m + 1) :
      constructionWitness G (coneRelation (A := A))
        (((DerivedCategory.singleFunctor A 0).obj (B ⟨k, hk⟩))⟦n⟧) := by
    induction k with
    | zero =>
      exact hzero _ ((shiftFunctor _ n).map_isZero
        ((DerivedCategory.singleFunctor A 0).map_isZero hz))
    | succ k ih =>
      let a : Fin m := ⟨k, by omega⟩
      have : Mono (f a) := hf a
      let S := ShortComplex.mk (f a) (cokernel.π (f a)) (cokernel.condition (f a))
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f a))
          inferInstance inferInstance
      let T := (shiftFunctor (Pretriangulated.Triangle (DerivedCategory A)) n).obj
        hS.singleTriangle
      have hT : T ∈ distTriang _ :=
        Pretriangulated.Triangle.shift_distinguished _ hS.singleTriangle_distinguished n
      exact constructionWitness_triangle G T.invRotate
        (Pretriangulated.inv_rot_of_distTriang T hT)
        (constructionWitness_generator (hg a)) (ih (by omega))
  exact tower m (Nat.lt_succ_self _)

private theorem constructionWitness_iso {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop)
    (hzero : ∀ Z : DerivedCategory A, IsZero Z →
      constructionWitness G (coneRelation (A := A)) Z)
    {U V : DerivedCategory A} (e : U ≅ V)
    (hU : constructionWitness G (coneRelation (A := A)) U) :
    constructionWitness G (coneRelation (A := A)) V := by
  let T := Pretriangulated.Triangle.mk (0 : 0 ⟶ U) e.hom 0
  have hT : T ∈ distTriang _ := by
    apply Pretriangulated.isomorphic_distinguished _
      (Pretriangulated.contractible_distinguished₁ U)
    exact Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by simp [T]) (by change e.hom ≫ e.inv = 𝟙 U ≫ 𝟙 U; simp) (by simp [T])
  exact constructionWitness_triangle G T hT (hzero _ (isZero_zero _)) hU

private theorem constructionWitness_subobject_filtration {A : Type w}
    [Category.{v} A] [Abelian A] [HasDerivedCategory A]
    (G : DerivedCategory A → Prop) (M : A) (m : ℕ)
    (B : Fin (m + 1) → Subobject M) (hb : B 0 = ⊥) (ht : B (Fin.last m) = ⊤)
    (hle : ∀ a : Fin m, B a.castSucc ≤ B a.succ) (n : ℤ)
    (hzero : ∀ Z : DerivedCategory A, IsZero Z →
      constructionWitness G (coneRelation (A := A)) Z)
    (hg : ∀ a : Fin m, G
      ((((DerivedCategory.singleFunctor A 0).obj
        (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a))))⟦n⟧)⟦(-1 : ℤ)⟧)) :
    constructionWitness G (coneRelation (A := A))
      (((DerivedCategory.singleFunctor A 0).obj M)⟦n⟧) := by
  have hz : IsZero (B 0 : A) :=
    (isZero_zero A).of_iso (Subobject.isoOfEq _ _ hb ≪≫ Subobject.botCoeIsoZero)
  have hw := constructionWitness_filtration G m (fun k ↦ (B k : A))
    (fun a ↦ Subobject.ofLE _ _ (hle a)) (fun a ↦ inferInstance) n hz hzero hg
  have e : (B (Fin.last m) : A) ≅ M :=
    Subobject.isoOfEq _ _ ht ≪≫ Subobject.underlyingIso (𝟙 M)
  exact constructionWitness_iso G hzero
    ((shiftFunctor _ n).mapIso ((DerivedCategory.singleFunctor A 0).mapIso e)) hw

variable (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ₀] [IsCommMonObj Λ₀]

private def mapRegularIso {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

private def pointFiniteFreeIso (X : Scheme.{u}) (r : ℕ) :
    ((upperStarFromPoint X).mapMod Λ₀).obj (Mod.finiteFree Λ₀ r) ≅
      Mod.finiteFree (condensedRingObj Λ₀ X) r := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : ((upperStarFromPoint X).mapMod Λ₀).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ((upperStarFromPoint X).mapMod Λ₀).mapBiproduct
      (fun _ : Fin r ↦ Mod.regular Λ₀) ≪≫
    biproduct.mapIso (fun _ ↦ mapRegularIso (upperStarFromPoint X) Λ₀)

private theorem lisse_finiteModel (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (hM : IsLisseCoefficientModule Λ₀ M) : HasFiniteConstantLocalModel Λ₀ X M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := hU i
  refine ⟨Mod.finiteFree Λ₀ r, ⟨r, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨?_⟩⟩
  exact e ≪≫ (pointFiniteFreeIso Λ₀ (U.X i) r).symm

private def forgetStratification {X : Scheme.{u}} (P : Scheme.Stratification X) :
    X.FiniteLocallyClosedStratification :=
  { n := P.n
    stratum := P.stratum
    isLocallyClosed_stratum := P.isLocallyClosed_stratum
    iUnion_stratum_eq_univ := P.iUnion_stratum_eq_univ
    pairwise_disjoint_stratum := P.pairwise_disjoint_stratum
    domain := P.domain
    immersion := P.immersion
    isImmersion := P.isImmersion
    range_immersion := P.range_immersion }

private theorem adapted_forget {X : Scheme.{u}}
    (P : ∀ S : Scheme.{u}, (S ⟶ X) → Prop) (R : Scheme.Stratification X)
    (hR : ∀ a, P (R.domain a) (R.immersion a)) :
    ∀ a, P ((forgetStratification R).domain a) ((forgetStratification R).immersion a) :=
  hR

private theorem refine_lisse (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (P : X.FiniteLocallyClosedStratification)
    (hP : ∀ a : Fin P.n, HasFiniteConstantLocalModel Λ₀ (P.domain a)
      ((CondensedRing.upperStar Λ₀ (P.immersion a)).obj M))
    (hc : CoefficientHeartStratificationAssertions Λ₀ X) :
    ∃ Q : X.FiniteLocallyClosedStratification,
      (∀ a : Fin Q.n, HasFiniteConstantLocalModel Λ₀ (Q.domain a)
        ((CondensedRing.upperStar Λ₀ (Q.immersion a)).obj M)) ∧
      ∀ k : Fin (Q.n + 1),
        IsOpen (⋃ a : Fin Q.n, ⋃ (_ : a.val < k.val), Q.stratum a) := by
  obtain ⟨Q, hQP, _, hQopen⟩ := hc.1 1 (fun _ ↦ P)
  have hQlisse := hc.2.1.2 P Q M hP (fun a ↦ hQP 0 a)
  exact ⟨Q, fun a ↦ lisse_finiteModel Λ₀ _ _ (hQlisse a), hQopen⟩

private theorem constructible_stratified (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))
    (hM : IsConstantModelConstructible Λ₀ X M) : IsFiniteConstantStratified Λ₀ X M := by
  rw [IsConstantModelConstructible, ite_eq_left
    (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)] at hM
  exact hM

private theorem common_lisse_refinement
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₀) X))
    (hM : IsConstantModelConstructible (Λ₀) X M)
    (hc : CoefficientHeartStratificationAssertions Λ₀ X) :
    ∃ Q : X.FiniteLocallyClosedStratification,
      (∀ a : Fin Q.n, HasFiniteConstantLocalModel Λ₀ (Q.domain a)
        ((CondensedRing.upperStar Λ₀ (Q.immersion a)).obj M)) ∧
      ∀ k : Fin (Q.n + 1),
        IsOpen (⋃ a : Fin Q.n, ⋃ (_ : a.val < k.val), Q.stratum a) := by
  obtain ⟨P, hP⟩ := constructible_stratified Λ₀ X M hM
  exact refine_lisse Λ₀ X M (forgetStratification P)
    (adapted_forget
      (fun S a ↦ HasFiniteConstantLocalModel Λ₀ S ((CondensedRing.upperStar Λ₀ a).obj M))
      P hP) hc

private theorem coefficientHeart_lisse_filtration (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hM : IsConstantModelConstructible (coefficientHeartRingObj Λ) X M)
 :
    ∃ (Q : X.FiniteLocallyClosedStratification) (B : Fin (Q.n + 1) → Subobject M),
      B 0 = ⊥ ∧ B (Fin.last Q.n) = ⊤ ∧
      ∃ hle : ∀ a : Fin Q.n, B a.castSucc ≤ B a.succ,
        ∀ a : Fin Q.n,
          Nonempty (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a)) ≅
            (coefficientHeartLocallyClosedExtension (coefficientHeartRingObj Λ)
              (Q.immersion a) (Q.isImmersion a)).obj
                ((CondensedRing.upperStar (coefficientHeartRingObj Λ)
                  (Q.immersion a)).obj M)) ∧
          IsLisseCoefficientModule (coefficientHeartRingObj Λ)
            ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (Q.immersion a)).obj M) := by
  obtain ⟨Q, hQmodel, hQopen⟩ := common_lisse_refinement (coefficientHeartRingObj Λ)
    X M hM (coefficientHeart_commonStratification ℓ Λ X hΛ)
  let V : Fin (Q.n + 1) → X.Opens :=
    fun k ↦ ⟨⋃ a : Fin Q.n, ⋃ (_ : a.val < k.val), Q.stratum a, hQopen k⟩
  refine ⟨Q, fun k ↦ coefficientHeartFiltrationStep (coefficientHeartRingObj Λ) M (V k), ?_⟩
  exact (coefficientHeart_filtration ℓ Λ hΛ X M hM Q hQmodel V (fun _ ↦ rfl)).2

private theorem locallyClosedExtension_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    IsZero ((coefficientHeartLocallyClosedExtension Λ a ha).obj 0) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact (CondensedRing.lowerStar Λ a.imageι).map_isZero
    ((CondensedRing.openImmersionLowerShriek Λ a.toImage).map_isZero (isZero_zero _))

/-- A shifted constructible sheaf has a finite cone witness from shifted lisse
extensions. The conclusion also permits an isomorphic choice of its derived object.

Source: blueprint generation, Single sheaves paragraph, and Stacks Tag 0152
(blueprint: lem-sfb-coefficient-heart-sheaf-cone-witness).

Proof: refine an adapted finite stratification to have open prefixes, using common
stratification. Apply coefficientHeart_filtration to its prefixes. The bottom image
subobject is zero, the top is the sheaf, and the successive cokernels are the specified
locally closed extensions of lisse restrictions. Each inclusion is mono, so its
cokernel sequence is short exact. The degree-zero distinguished triangle and inverse
rotation express the next step as a cone of the shifted quotient into the preceding
step. Start with the zero lisse module on X, concatenate witnesses, and append these
cones. Shift the entire finite diagram by n, transporting generators by shift-addition
isomorphisms and using the signed shifted distinguished triangle. Finally transport
the last vertex by the given isomorphism. An empty filtration gives the zero object;
non-strict steps and zero quotients are permitted. -/
theorem coefficientHeart_sheaf_cone_witness (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hM : IsConstantModelConstructible (coefficientHeartRingObj Λ) X M)
    (n : ℤ) (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X)))
    (hK : Nonempty (K ≅ ((DerivedCategory.singleFunctor _ 0).obj M)⟦n⟧)) :
    ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X))),
      F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
        (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
          IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
            Nonempty (F r ≅ ((DerivedCategory.singleFunctor _ 0).obj
              ((coefficientHeartLocallyClosedExtension
                (coefficientHeartRingObj Λ) a ha).obj L))⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
            (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (coefficientHeartRingObj Λ) X)
  let D := DerivedCategory A
  let G : D → Prop := fun W ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) S))
      (m : ℤ), IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
        Nonempty (W ≅ ((DerivedCategory.singleFunctor A 0).obj
          ((coefficientHeartLocallyClosedExtension (coefficientHeartRingObj Λ) a ha).obj L))⟦m⟧)
  let R : D → D → D → Prop := coneRelation (A := A)
  change constructionWitness G R K
  have hzL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) (0 : A) := by
    refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
      (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
    refine ⟨0, ⟨?_⟩⟩
    apply IsZero.iso
    · exact (CondensedRing.upperStar (coefficientHeartRingObj Λ) _).map_isZero (isZero_zero _)
    · rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      intro j
      exact Fin.elim0 j
  have hzExt : IsZero ((coefficientHeartLocallyClosedExtension (coefficientHeartRingObj Λ) (𝟙 X)
      (by infer_instance)).obj (0 : A)) := by
    exact locallyClosedExtension_zero (coefficientHeartRingObj Λ) (𝟙 X) inferInstance
  have zero_witness (Z : D) (hz : IsZero Z) : constructionWitness G R Z := by
    apply constructionWitness_generator
    refine ⟨X, 𝟙 X, inferInstance, 0, 0, hzL, ⟨?_⟩⟩
    exact hz.iso ((shiftFunctor D (0 : ℤ)).map_isZero
      ((DerivedCategory.singleFunctor A 0).map_isZero hzExt))
  obtain ⟨Q, B, hbot, htop, hle, hquot⟩ :=
    coefficientHeart_lisse_filtration ℓ Λ hΛ X M hM
  have tower : constructionWitness G R
      (((DerivedCategory.singleFunctor A 0).obj M)⟦n⟧) := by
    apply constructionWitness_subobject_filtration G M Q.n B hbot htop hle n zero_witness
    intro a
    obtain ⟨⟨e⟩, hL⟩ := hquot a
    refine ⟨Q.domain a, Q.immersion a, Q.isImmersion a,
      (CondensedRing.upperStar (coefficientHeartRingObj Λ) (Q.immersion a)).obj M, n + -1, hL, ⟨?_⟩⟩
    exact (shiftFunctor D (-1 : ℤ)).mapIso
        ((shiftFunctor D n).mapIso ((DerivedCategory.singleFunctor A 0).mapIso e)) ≪≫
      (shiftFunctorAdd D n (-1 : ℤ)).symm.app _
  obtain ⟨eK⟩ := hK
  exact constructionWitness_iso G zero_witness eK.symm tower

end AlgebraicGeometry.ProEtale
