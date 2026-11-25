/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.OpenCover
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Finite affine factorizations and gluing of intervals
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

private theorem exists_affine_factorization {U V : Scheme.{u}}
    [IsAffine U] [IsAffine V] (g : U ⟶ V) [LocallyOfFiniteType g] :
    ∃ (m : ℕ) (c : U ⟶ AffineSpace (ULift.{u} (Fin m)) V),
      IsClosedImmersion c ∧ c ≫ (AffineSpace (ULift.{u} (Fin m)) V ↘ V) = g := by
  classical
  let R := Γ(V, ⊤)
  let B := Γ(U, ⊤)
  let : Algebra R B := g.appTop.hom.toAlgebra
  have hft : Algebra.FiniteType R B :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
      (inferInstance : LocallyOfFiniteType g)
  obtain ⟨m, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let q' : MvPolynomial (ULift.{u} (Fin m)) R →ₐ[R] B :=
    q.comp (MvPolynomial.renameEquiv R Equiv.ulift).toAlgHom
  have hq' : Function.Surjective q' := hq.comp
    (MvPolynomial.renameEquiv R Equiv.ulift).surjective
  let c := U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom q'.toRingHom) ≫
    (AffineSpace.isoOfIsAffine (ULift.{u} (Fin m)) V).inv
  refine ⟨m, c, ?_, ?_⟩
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom q'.toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ hq'
    change IsClosedImmersion (U.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom q'.toRingHom) ≫ _)
    exact IsClosedImmersion.comp _ _
  · dsimp [c]
    rw [Category.assoc, Category.assoc, AffineSpace.isoOfIsAffine_inv_over,
      ← Category.assoc (Spec.map _), ← Spec.map_comp]
    have heq : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom q'.toRingHom =
        g.appTop := by
      ext x
      exact q'.commutes x
    change U.isoSpec.hom ≫ Spec.map
      (CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom q'.toRingHom) ≫
      V.isoSpec.inv = g
    rw [heq]
    simp only [Scheme.isoSpec, asIso_hom, asIso_inv]
    rw [← Scheme.toSpecΓ_naturality_assoc]
    simp

private theorem finite_affine_cover (X : Scheme.{u}) (W : X.Opens)
    (hW : IsCompact (W : Set X)) :
    ∃ (n : ℕ) (U : Fin n → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, U i ≤ W) ∧
      ∀ x : X, x ∈ W → ∃ i, x ∈ U i := by
  classical
  obtain ⟨s, hs, heq⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  let : Fintype s := hs.fintype
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i ↦ (e.symm i).val.val, ?_, ?_, ?_⟩
  · intro i
    exact (e.symm i).val.property
  · intro i
    rw [heq]
    exact le_iSup_of_le (e.symm i).val
      (le_iSup_of_le (e.symm i).property le_rfl)
  · intro x hx
    rw [heq] at hx
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hUs, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp hU
    exact ⟨e ⟨U, hUs⟩, by simpa [e] using hxU⟩

private theorem sf_geometry
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (V : Fin n → Y.Opens) (N : Fin n → ℕ)
      (U : (i : Fin n) → Fin (N i) → X.Opens)
      (hUV : ∀ (i : Fin n) (j : Fin (N i)), U i j ≤ f ⁻¹ᵁ V i)
      (m : (i : Fin n) → Fin (N i) → ℕ)
      (c : (i : Fin n) → (j : Fin (N i)) →
        (U i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme),
      (∀ i : Fin n, IsAffineOpen (V i)) ∧
      (∀ y : Y, ∃ i : Fin n, y ∈ V i) ∧
      (∀ (i : Fin n) (j : Fin (N i)), IsAffineOpen (U i j)) ∧
      (∀ (i : Fin n) (x : X), x ∈ f ⁻¹ᵁ V i → ∃ j : Fin (N i), x ∈ U i j) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsClosedImmersion (c i j) ∧
        c i j ≫ (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) = f.resLE (V i) (U i j) (hUV i j) ∧
        SmoothOfRelativeDimension (m i j)
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme) ∧
        IsSeparated
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme)) ∧
      (∀ i : Fin n,
        IsSeparated ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((V i).ι ≫ (Y ↘ Spec (.of k)))) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsSeparated ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        QuasiCompact ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        IsSeparated ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k)))) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  obtain ⟨n, V, hV, -, hcovV⟩ := finite_affine_cover Y ⊤ isCompact_univ
  have hc (i : Fin n) : IsCompact (f ⁻¹ᵁ V i : Set X) :=
    f.isCompact_preimage (hV i).isCompact
  choose N U hU hUV hcovU using fun i ↦ finite_affine_cover X (f ⁻¹ᵁ V i) (hc i)
  have hf (i : Fin n) (j : Fin (N i)) := by
    let : IsAffine (V i).toScheme := hV i
    let : IsAffine (U i j).toScheme := hU i j
    exact exists_affine_factorization (f.resLE (V i) (U i j) (hUV i j))
  choose m c hclosed hcomp using hf
  refine ⟨n, V, N, U, hUV, m, c, hV, fun y ↦ hcovV y trivial, hU, hcovU, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨hclosed i j, hcomp i j, ?_, inferInstance⟩
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin (m i j)))
      (V i).toScheme
  · intro i
    let : IsAffine (V i).toScheme := hV i
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro i j
    let : IsAffine (V i).toScheme := hV i
    let : IsAffine (U i j).toScheme := hU i j
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩

private theorem homology_zero_of_open_cover
    (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}} {ι : Type}
    (W : ι → X.Opens) (hW : ∀ x : X, ∃ i, x ∈ W i)
    (K : Etale.DerivedCategoryModule A X) (q : ℤ)
    (h : ∀ i, IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
  let F := (_root_.DerivedCategory.homologyFunctor _ q).obj K
  have hz (i : ι) : IsZero ((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).obj F) :=
    (h i).of_iso (let P := Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι;
      (P.mapDerivedCategoryHomologyFunctorIso q).app K)
  have hi := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective
    (ModuleCat.{u + 1} A) (fun i : ULift.{u} ι ↦ (W i.down).ι)
    (fun x ↦ by obtain ⟨i, hi⟩ := hW x; exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩)
    (0 : F ⟶ 0) (fun i ↦ isIso_of_source_target_iso_zero _ (hz i.down).isoZero
      ((Etale.upperStar (ModuleCat.{u + 1} A) (W i.down).ι).map_isZero (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private theorem constructible_homology_of_open_cover
    (A : Type (u + 1)) [CommRing A] [Finite A] {X : Scheme.{u}} [IsNoetherian X]
    {ι : Type} (W : ι → X.Opens) (hW : ∀ x : X, ∃ i, x ∈ W i)
    (K : Etale.DerivedCategoryModule A X) (q : ℤ)
    (h : ∀ i, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K))) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  apply Scheme.IsConstructibleSheaf.of_iSup_eq_top
    (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
    (CA := fun M : ModuleCat.{u + 1} A ↦ M) W
    (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hW x))
  intro i
  let P := Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι
  let e := (P.mapDerivedCategoryHomologyFunctorIso q).app K
  have ht : Scheme.IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
      (CA := fun M : ModuleCat.{u + 1} A ↦ M)
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (h i)
  exact @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _ e.symm ht

private noncomputable def pullback_tensor_single_iso
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}} (g : Z ⟶ X)
    (K : Etale.DerivedCategoryModule A X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory).obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≅
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj
      (((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory).obj K)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) g).obj F)) :=
  ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).app _).symm ≪≫
    Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g K _ ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).app K)).app _ ≪≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj _).mapIso
      ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) g).app F)

private theorem tor_amplitude_of_open_cover
    (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}} {ι : Type}
    (W : ι → X.Opens) (hW : ∀ x : X, ∃ i, x ∈ W i)
    (K : Etale.DerivedCategoryModule A X) (a b : ι → ℤ) (amin bmax : ℤ)
    (ha : ∀ i, amin ≤ a i) (hb : ∀ i, b i ≤ bmax)
    (h : ∀ i, Etale.DerivedCategory.hasTorAmplitudeIn A (W i).toScheme (a i) (b i)
      (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K)) :
    Etale.DerivedCategory.hasTorAmplitudeIn A X amin bmax K := by
  intro F q hq
  apply homology_zero_of_open_cover A W hW
  intro i
  have hqi : q < a i ∨ b i < q := hq.imp
    (fun hq ↦ lt_of_lt_of_le hq (ha i)) (fun hq ↦ lt_of_le_of_lt (hb i) hq)
  exact (h i ((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).obj F) q hqi).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (pullback_tensor_single_iso A (W i).ι K F))

private theorem finite_endpoints {ι : Type} [Finite ι] [Nonempty ι]
    (r s a b : ι → ℤ) :
    ∃ rmin smax amin bmax : ℤ,
      IsLeast (Set.range r) rmin ∧ IsGreatest (Set.range s) smax ∧
      IsLeast (Set.range a) amin ∧ IsGreatest (Set.range b) bmax := by
  obtain ⟨ir, -, hr⟩ := Set.exists_min_image Set.univ r (Set.toFinite _) Set.univ_nonempty
  obtain ⟨is, -, hs⟩ := Set.exists_max_image Set.univ s (Set.toFinite _) Set.univ_nonempty
  obtain ⟨ia, -, ha⟩ := Set.exists_min_image Set.univ a (Set.toFinite _) Set.univ_nonempty
  obtain ⟨ib, -, hb⟩ := Set.exists_max_image Set.univ b (Set.toFinite _) Set.univ_nonempty
  exact ⟨r ir, s is, a ia, b ib,
    ⟨⟨ir, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hr i trivial⟩,
    ⟨⟨is, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hs i trivial⟩,
    ⟨⟨ia, rfl⟩, by rintro _ ⟨i, rfl⟩; exact ha i trivial⟩,
    ⟨⟨ib, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hb i trivial⟩⟩

private theorem glue_finite_intervals
    (A : Type (u + 1)) [CommRing A] [Finite A] {X : Scheme.{u}} [IsNoetherian X]
    {ι : Type} [Finite ι] (W : ι → X.Opens) (hW : ∀ x : X, ∃ i, x ∈ W i)
    (K : Etale.DerivedCategoryModule A X) (r s a b : ι → ℤ)
    (h : ∀ i,
      (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K))) ∧
      (∀ q : ℤ, q < r i ∨ s i < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K))) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A (W i).toScheme (a i) (b i)
        (((Etale.upperStar (ModuleCat.{u + 1} A) (W i).ι).mapDerivedCategory).obj K)) :
    Etale.DerivedCategory.isBoundedConstructible A X K ∧
    (Nonempty X → ∃ rmin smax amin bmax : ℤ,
      IsLeast (Set.range r) rmin ∧ IsGreatest (Set.range s) smax ∧
      IsLeast (Set.range a) amin ∧ IsGreatest (Set.range b) bmax ∧
      (∀ q : ℤ, q < rmin ∨ smax < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A X amin bmax K) ∧
    (IsEmpty X → IsZero K ∧ ∀ r₀ s₀ a₀ b₀ : ℤ,
      (∀ q : ℤ, q < r₀ ∨ s₀ < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A X a₀ b₀ K) := by
  classical
  have hc (q : ℤ) := constructible_homology_of_open_cover A W hW K q (fun i ↦ (h i).1 q)
  have he : IsEmpty X → IsZero K ∧ ∀ r₀ s₀ a₀ b₀ : ℤ,
      (∀ q : ℤ, q < r₀ ∨ s₀ < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A X a₀ b₀ K := by
    intro hX
    let := hX
    have hz (M : Etale.DerivedCategoryModule A X) : IsZero M :=
      _root_.DerivedCategory.isZero_of_forall_isZero_homology M
        (fun _ ↦ Scheme.Etale.isZero_sheaf_of_isEmpty _)
    exact ⟨hz K, fun _ _ _ _ ↦ ⟨fun _ _ ↦ Scheme.Etale.isZero_sheaf_of_isEmpty _,
      fun _ _ _ ↦ Scheme.Etale.isZero_sheaf_of_isEmpty _⟩⟩
  have hn : Nonempty X → ∃ rmin smax amin bmax : ℤ,
      IsLeast (Set.range r) rmin ∧ IsGreatest (Set.range s) smax ∧
      IsLeast (Set.range a) amin ∧ IsGreatest (Set.range b) bmax ∧
      (∀ q : ℤ, q < rmin ∨ smax < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A X amin bmax K := by
    intro hX
    obtain ⟨x⟩ := hX
    obtain ⟨i, -⟩ := hW x
    have : Nonempty ι := ⟨i⟩
    obtain ⟨rmin, smax, amin, bmax, hr, hs, ha, hb⟩ := finite_endpoints r s a b
    refine ⟨rmin, smax, amin, bmax, hr, hs, ha, hb, ?_, ?_⟩
    · intro q hq
      apply homology_zero_of_open_cover A W hW K q
      intro i
      exact (h i).2.1 q (hq.imp
        (fun hq ↦ lt_of_lt_of_le hq (hr.2 ⟨i, rfl⟩))
        (fun hq ↦ lt_of_le_of_lt (hs.2 ⟨i, rfl⟩) hq))
    · exact tor_amplitude_of_open_cover A W hW K a b amin bmax
        (fun i ↦ ha.2 ⟨i, rfl⟩) (fun i ↦ hb.2 ⟨i, rfl⟩) (fun i ↦ (h i).2.2)
  refine ⟨⟨hc, ?_⟩, hn, he⟩
  by_cases hX : Nonempty X
  · obtain ⟨rmin, smax, _, _, _, _, _, _, hv, -⟩ := hn hX
    refine ⟨min rmin smax, max rmin smax, min_le_max, fun q hq ↦ hv q ?_⟩
    exact hq.imp (fun hq ↦ lt_of_lt_of_le hq (min_le_left _ _))
      (fun hq ↦ lt_of_le_of_lt (le_max_right _ _) hq)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨0, 0, le_rfl, (he inferInstance).2 0 0 0 0 |>.1⟩

/-- Finite affine charts factor through affine space, and local constructibility and
cohomological and Tor bounds glue with the minimum lower and maximum upper endpoints.
`IsLeast` and `IsGreatest` specify precisely these extrema of the finite endpoint ranges.
Restriction is the functor on derived categories induced by exact etale inverse image. -/
theorem exists_sf_affine_chart_factorization_gluing
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (V : Fin n → Y.Opens) (N : Fin n → ℕ)
      (U : (i : Fin n) → Fin (N i) → X.Opens)
      (hUV : ∀ (i : Fin n) (j : Fin (N i)), U i j ≤ f ⁻¹ᵁ V i)
      (m : (i : Fin n) → Fin (N i) → ℕ)
      (c : (i : Fin n) → (j : Fin (N i)) →
        (U i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme),
      (∀ i : Fin n, IsAffineOpen (V i)) ∧
      (∀ y : Y, ∃ i : Fin n, y ∈ V i) ∧
      (∀ (i : Fin n) (j : Fin (N i)), IsAffineOpen (U i j)) ∧
      (∀ (i : Fin n) (x : X), x ∈ f ⁻¹ᵁ V i → ∃ j : Fin (N i), x ∈ U i j) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsClosedImmersion (c i j) ∧
        c i j ≫ (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) = f.resLE (V i) (U i j) (hUV i j) ∧
        SmoothOfRelativeDimension (m i j)
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme) ∧
        IsSeparated
          (AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘ (V i).toScheme)) ∧
      (∀ i : Fin n,
        IsSeparated ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((V i).ι ≫ (Y ↘ Spec (.of k)))) ∧
      (∀ (i : Fin n) (j : Fin (N i)),
        IsSeparated ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        QuasiCompact ((U i j).ι ≫ (X ↘ Spec (.of k))) ∧
        IsSeparated ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((AffineSpace (ULift.{u} (Fin (m i j))) (V i).toScheme ↘
          (V i).toScheme) ≫ (V i).ι ≫ (Y ↘ Spec (.of k)))) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
        (K : Etale.DerivedCategoryModule A X)
        (r s a b : (Σ i : Fin n, Fin (N i)) → ℤ),
        (∀ (i : Fin n) (j : Fin (N i)),
          (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
            ((_root_.DerivedCategory.homologyFunctor _ q).obj
              (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K))) ∧
          (∀ q : ℤ, q < r ⟨i, j⟩ ∨ s ⟨i, j⟩ < q →
            IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
              (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K))) ∧
          Etale.DerivedCategory.hasTorAmplitudeIn A (U i j).toScheme (a ⟨i, j⟩) (b ⟨i, j⟩)
            (((Etale.upperStar (ModuleCat.{u + 1} A) (U i j).ι).mapDerivedCategory).obj K)) →
        Etale.DerivedCategory.isBoundedConstructible A X K ∧
        (Nonempty X → ∃ rmin smax amin bmax : ℤ,
          IsLeast (Set.range r) rmin ∧ IsGreatest (Set.range s) smax ∧
          IsLeast (Set.range a) amin ∧ IsGreatest (Set.range b) bmax ∧
          (∀ q : ℤ, q < rmin ∨ smax < q →
            IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
          Etale.DerivedCategory.hasTorAmplitudeIn A X amin bmax K) ∧
        (IsEmpty X → IsZero K ∧
          ∀ r₀ s₀ a₀ b₀ : ℤ,
            (∀ q : ℤ, q < r₀ ∨ s₀ < q →
              IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
            Etale.DerivedCategory.hasTorAmplitudeIn A X a₀ b₀ K)) := by
  classical
  obtain ⟨n, V, N, U, hUV, m, c, hV, hcovV, hU, hcovU, hfactor, hVk, hUk⟩ :=
    sf_geometry k X Y f
  refine ⟨n, V, N, U, hUV, m, c, hV, hcovV, hU, hcovU, hfactor, hVk, hUk, ?_⟩
  intro A _ _ K r s a b h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let W : (Σ i : Fin n, Fin (N i)) → X.Opens := fun ij ↦ U ij.1 ij.2
  have hW (x : X) : ∃ ij, x ∈ W ij := by
    obtain ⟨i, hi⟩ := hcovV (f x)
    obtain ⟨j, hj⟩ := hcovU i x hi
    exact ⟨⟨i, j⟩, hj⟩
  exact glue_finite_intervals (X := X) (ι := Σ i : Fin n, Fin (N i))
    A W hW K r s a b (fun (ij : Σ i : Fin n, Fin (N i)) ↦ h ij.1 ij.2)

end AlgebraicGeometry
