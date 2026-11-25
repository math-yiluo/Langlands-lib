/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons

/-! # Compatible comparison isomorphisms for an ordinary evaluation map

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ, 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem shortExact_of_retraction {C : Type*} [Category C] [Abelian C]
    {S T : ShortComplex C} (i : S ⟶ T) (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)
    (hT : T.ShortExact) : S.ShortExact := by
  have h₁ : i.τ₁ ≫ r.τ₁ = 𝟙 S.X₁ := congrArg ShortComplex.Hom.τ₁ hir
  have h₂ : i.τ₂ ≫ r.τ₂ = 𝟙 S.X₂ := congrArg ShortComplex.Hom.τ₂ hir
  have h₃ : i.τ₃ ≫ r.τ₃ = 𝟙 S.X₃ := congrArg ShortComplex.Hom.τ₃ hir
  have hm : RetractArrow S.f T.f :=
    { i := Arrow.homMk i.τ₁ i.τ₂ i.comm₁₂
      r := Arrow.homMk r.τ₁ r.τ₂ r.comm₁₂
      retract := by ext <;> assumption }
  have he : RetractArrow S.g T.g :=
    { i := Arrow.homMk i.τ₂ i.τ₃ i.comm₂₃
      r := Arrow.homMk r.τ₂ r.τ₃ r.comm₂₃
      retract := by ext <;> assumption }
  have : Mono S.f := (MorphismProperty.monomorphisms C).of_retract hm hT.mono_f
  have : Epi S.g := (MorphismProperty.epimorphisms C).of_retract he hT.epi_g
  apply ShortComplex.ShortExact.mk' _ (inferInstance : Mono S.f)
    (inferInstance : Epi S.g)
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2
  rw [← ShortComplex.homologyMap_id, ← hir, ShortComplex.homologyMap_comp]
  rw [((T.exact_iff_isZero_homology).1 hT.exact).eq_of_tgt
    (ShortComplex.homologyMap i), CategoryTheory.Limits.zero_comp]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Resolving the internal-Hom carriers requires extra elaboration steps.
private theorem exact_hom_of_retract {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (ι : E ⟶ B) (π : B ⟶ E) (hιπ : ι ≫ π = 𝟙 E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hzB : SheafOfModules.homObjMap (R := R) (𝟙 B) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 B) S.g = 0)
    (hB : (ShortComplex.mk _ _ hzB).ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  have hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0 := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R) (𝟙 E) (𝟙 E) S.f S.g,
      S.zero, Category.id_comp]
    ext V φ
    rfl
  let T := ShortComplex.mk _ _ hzB
  let SE := ShortComplex.mk _ _ hz
  let i : SE ⟶ T :=
    { τ₁ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) π (𝟙 S.X₃)
      comm₁₂ := by simp [SE, T, SheafOfModules.homObjMap_comp_homObjMap]
      comm₂₃ := by simp [SE, T, SheafOfModules.homObjMap_comp_homObjMap] }
  let r : T ⟶ SE :=
    { τ₁ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₁)
      τ₂ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₂)
      τ₃ := SheafOfModules.homObjMap (R := R) ι (𝟙 S.X₃)
      comm₁₂ := by simp [SE, T, SheafOfModules.homObjMap_comp_homObjMap]
      comm₂₃ := by simp [SE, T, SheafOfModules.homObjMap_comp_homObjMap] }
  have hir : i ≫ r = 𝟙 SE := by
    apply ShortComplex.hom_ext <;>
      simp [i, r, SE, SheafOfModules.homObjMap_comp_homObjMap, hιπ]
  exact ⟨hz, shortExact_of_retraction i r hir hB⟩

-- Unpack the finite-free retraction on an abstract site before specializing to an open.
private theorem exact_hom_of_finiteFree_retract {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (R : Sheaf J CommRingCat.{u})
    (E : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hE : ∃ m : ℕ,
      ∃ (ι : E ⟶ SheafOfModules.free
          (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin m))
          ⟶ E), ι ≫ π = 𝟙 E)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 E) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 E) S.g) hz).ShortExact := by
  obtain ⟨m, ι, π, hιπ⟩ := hE
  let B := SheafOfModules.free
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin m))
  obtain ⟨hz, hfree, _⟩ := SheafOfModules.finiteFreeInternalHomExact.{u}
    (R := R) m B (Iso.refl B) S hS
  exact exact_hom_of_retract R E B ι π hιπ S hz hfree

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The finite-free retractions use the localized and internal-Hom carrier presentations.
private theorem strictlyPerfect_hom_quasiIso (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ)
    (hP : Scheme.IsStrictlyPerfect X U P)
    {F I : CochainComplex (localEvaluationModules X U) ℤ} (η : F ⟶ I)
    [QuasiIso η] :
    QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map η) := by
  apply quasiIso_homComplex_map_of_bounded_exact_terms
    ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) P hP.1 _ η
  intro n S hS
  exact exact_hom_of_finiteFree_retract (X.sheaf.over U) (P.X n) (hP.2 n) S hS

-- Transport a comparison square without unfolding the concrete derived-category objects.
private theorem exists_comparisons_of_isos {C : Type*} [Category C]
    {A B T T' H H' : C} (g : A ⟶ B) (f : T ⟶ H) (f' : T' ⟶ H') (h : H ⟶ H')
    [IsIso f] [IsIso f'] [IsIso h]
    (hab : ∃ a : A ≅ T', ∃ b : B ≅ H', g ≫ b.hom = a.hom ≫ f') :
    ∃ a : A ≅ T, ∃ b : B ≅ H, g ≫ b.hom = a.hom ≫ f := by
  obtain ⟨a, b, hab⟩ := hab
  refine ⟨a ≪≫ asIso f' ≪≫ (asIso h).symm ≪≫ (asIso f).symm,
    b ≪≫ (asIso h).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [← Category.assoc, hab]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The resolution comparisons use several equivalent carrier presentations.
/-- Given representatives and an ordinary evaluation chain map, there are compatible
source and target comparison isomorphisms. The comparisons are existentially
quantified; the square is not asserted for arbitrary isomorphisms.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of
lemma-dual-perfect-complex; Tag 08DM, lemma-Rhom-strictly-perfect;
Tag 08DL, lemma-restriction-RHom-to-U.
(blueprint: lem-pc-strictly-perfect-evaluation-comparisons).

Proof:
1. A finite-projective term is a retract of a finite free sheaf. Internal Hom
   makes its short-complex sequence a retract of the finite-free sequence.
   Monomorphisms and epimorphisms are stable under retracts; the retraction on
   homology makes its homology zero. Thus termwise internal Hom is exact.
2. Apply bounded exact-term Hom to the functorial K-injective resolution
   eta:F to I. Consequently Q Hom(P,eta) is invertible.
3. Construct the ordinary evaluation map for I using the specified degree maps
   and their differential equation. Apply the K-injective comparison theorem
   with eN followed by Q eta to obtain aI and bI and the resolved square.
4. Both ordinary evaluation maps are invertible by the strictly-perfect
   degreewise theorem. Set b=bI followed by the inverse of Q Hom(P,eta).
   Set a=aI followed by Q fI, the inverse of Q Hom(P,eta), and the inverse of Q f.
   Associativity and cancellation give R(g);b=a;Q(f).
   The source comparison is existentially chosen, so it need not be the map
   induced by tensoring eta. No separate evaluation-naturality lemma is needed.
   Zero complexes and empty opens use the same retractions and inverses.
-/
theorem exists_strictlyPerfect_evaluation_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  let A := localEvaluationModules X U
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj F
  let η : F ⟶ I := (CochainComplex.toKInjectiveResolution.{u} A).app F
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A F).2
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A F
  let fI : localEvaluationTensor X U P I ⟶ homComplex (R := X.sheaf.over U) P I :=
    { f := localEvaluationDegreeMap X U P I
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P I n m h }
  have hfI : IsLocalOrdinaryEvaluation X U P I fI := by
    intro p q n r h
    exact localEvaluationDegreeMap_formula X U P I p q n r h
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have : ∀ n : ℤ, IsIso (fI.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P I hstrict fI hfI n
  have : IsIso fI := HomologicalComplex.Hom.isIso_of_components fI
  let h := ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map η
  have : QuasiIso h := strictlyPerfect_hom_quasiIso X U P hstrict η
  have : IsIso (Q.map h) := inferInstance
  let eI := _eN ≪≫ asIso (Q.map η)
  exact exists_comparisons_of_isos _ (Q.map f) (Q.map fI) (Q.map h)
    (exists_strictlyPerfect_kInjective_evaluation_comparisons
      X K N U P I hstrict eK eI fI hfI)

end AlgebraicGeometry
