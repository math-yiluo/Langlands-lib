/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.NoetherianApproximation
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteStrata
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.AlgebraicGeometry.Closed.ClosedSectionAffinePartition
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.DescendQuasiFiniteAffine
import WeilConjectures.AlgebraicGeometry.Finite.FiniteAffineSectionCover
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Finite etale thickenings after surjective affine base change

## References

* Stacks Project, Etale Cohomology, Tag 095K, part (1)
* Stacks Project, Tag 095K (1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem thickening_baseChange
    {V U U₀ V₀ T E : Scheme.{u}} [IsAffine U] [IsAffine U₀] [IsAffine T]
    (h : V ⟶ U) (h₀ : V₀ ⟶ U₀) (b : U ⟶ U₀) (v : V ⟶ V₀)
    (sq : IsPullback v h h₀ b) (a : T ⟶ U₀) [Surjective a]
    (i : E ⟶ pullback h₀ a) (hi : IsThickening i)
    [IsFinite (i ≫ pullback.snd h₀ a)] [Etale (i ≫ pullback.snd h₀ a)] :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (a' : U' ⟶ U),
      Surjective a' ∧ ∃ (Z : Scheme.{u}) (i' : Z ⟶ pullback h a'),
        IsThickening i' ∧ IsFinite (i' ≫ pullback.snd h a') ∧
          Etale (i' ≫ pullback.snd h a') := by
  let U' := pullback b a
  let a' : U' ⟶ U := pullback.fst b a
  let t : U' ⟶ T := pullback.snd b a
  let P := pullback h a'
  let q : P ⟶ pullback h₀ a :=
    pullback.lift (pullback.fst h a' ≫ v) (pullback.snd h a' ≫ t) (by
      rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition,
        Category.assoc, pullback.condition]
      rfl)
  have hs : IsPullback q (pullback.snd h a') (pullback.snd h₀ a) t := by
    have big := (IsPullback.of_hasPullback h a').paste_horiz sq
    have hab : a' ≫ b = t ≫ a := pullback.condition
    rw [hab] at big
    have hq : q ≫ pullback.fst h₀ a = pullback.fst h a' ≫ v := by simp [q]
    rw [← hq] at big
    exact big.of_right (by simp [q]) (IsPullback.of_hasPullback h₀ a)
  let Z := pullback i q
  let i' : Z ⟶ P := pullback.snd i q
  have : IsClosedImmersion i := hi.1
  have : Surjective i := hi.2
  have hf : IsFinite (i' ≫ pullback.snd h a') := by
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback i q).paste_vert hs) inferInstance
  have he : Etale (i' ≫ pullback.snd h a') := by
    exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback i q).paste_vert hs) inferInstance
  exact ⟨U', inferInstance, a', inferInstance, Z, i',
    ⟨inferInstance, inferInstance⟩, hf, he⟩

private theorem locallyQuasiFinite_of_isQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : f.IsQuasiFinite) : LocallyQuasiFinite f := by
  let : LocallyOfFiniteType f := hf.1
  apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
  intro x
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_iff_isOpen_singleton.mpr
  rintro ⟨y, hy⟩
  change f y = x at hy
  subst x
  have hopen := hf.2.2 y
  rw [← (f.fiberHomeo (f y)).isOpen_image] at hopen
  simpa only [Set.image_singleton, Scheme.Hom.asFiber,
    Homeomorph.apply_symm_apply] using hopen

private theorem isQuasiFinite_of_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [QuasiCompact f] : f.IsQuasiFinite :=
  ⟨inferInstance, inferInstance, fun x ↦
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (f.quasiFiniteAt x)⟩

private theorem exists_noetherian_affine_model
    {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (h : V ⟶ U)
    (hqf : h.IsQuasiFinite) [LocallyOfFinitePresentation h] :
    ∃ (U₀ V₀ : Scheme.{u}) (_ : IsAffine U₀) (_ : IsAffine V₀)
      (_ : IsNoetherian U₀) (h₀ : V₀ ⟶ U₀) (b : U ⟶ U₀) (v : V ⟶ V₀),
      h₀.IsQuasiFinite ∧ IsPullback v h h₀ b := by
  let A := Γ(U, ⊤)
  let D := finsetSubringDiagram A
  let c := finsetSubringCocone A
  obtain ⟨i₀, B₀, b₀, hfp, k, hpush⟩ :=
    CommRingCat.exists_isPushout_of_finitePresentation D c
      (isColimitFinsetSubringCocone A) h.appTop h.finitePresentation_appTop
  let : LocallyQuasiFinite h := locallyQuasiFinite_of_isQuasiFinite h hqf
  have hspec : LocallyQuasiFinite (Spec.map h.appTop) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyQuasiFinite V.isoSpec.hom,
      Scheme.isoSpec_hom_naturality]
    infer_instance
  let := hspec
  have hs := (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip
  have hp : LocallyQuasiFinite (Spec.map (pushout.inl (c.ι.app i₀) b₀)) := by
    have he : LocallyQuasiFinite (pullback.snd (Spec.map b₀) (Spec.map (c.ι.app i₀))) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyQuasiFinite hs.isoPullback.hom,
        hs.isoPullback_hom_snd]
      infer_instance
    have can := (isPullback_SpecMap_pushout (c.ι.app i₀) b₀).flip
    rw [← can.isoPullback_hom_snd]
    let := he
    infer_instance
  have hpfp : LocallyOfFinitePresentation (Spec.map (pushout.inl (c.ι.app i₀) b₀)) := by
    have : LocallyOfFinitePresentation (Spec.map b₀) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hfp
    exact MorphismProperty.of_isPullback
      (isPullback_SpecMap_pushout (c.ι.app i₀) b₀).flip inferInstance
  let := hp
  let := hpfp
  obtain ⟨i, hi, hqi⟩ := descend_isQuasiFinite_affine D c
    (isColimitFinsetSubringCocone A) i₀ B₀ b₀ hfp
      (isQuasiFinite_of_locallyQuasiFinite _)
  let g := D.map (homOfLE hi)
  let Bi := pushout g b₀
  let bi : D.obj i ⟶ Bi := pushout.inl g b₀
  let ki : Bi ⟶ Γ(V, ⊤) := pushout.desc (c.ι.app i ≫ h.appTop) k (by
    rw [← Category.assoc, c.w (homOfLE hi)]
    exact hpush.w)
  have hpi : IsPushout (c.ι.app i) bi h.appTop ki := by
    have hc : g ≫ c.ι.app i = c.ι.app i₀ := c.w (homOfLE hi)
    have hk : pushout.inr g b₀ ≫ ki = k := by simp [ki]
    rw [← hc, ← hk] at hpush
    exact hpush.of_left (by simp [bi, ki]) (IsPushout.of_hasPushout g b₀)
  have sq₀ := (isPullback_SpecMap_of_isPushout _ _ _ _ hpi).flip
  have sq₁ : IsPullback V.isoSpec.hom h (Spec.map h.appTop) U.isoSpec.hom :=
    IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality h⟩
  exact ⟨Spec (D.obj i), Spec Bi, inferInstance, inferInstance, inferInstance,
    Spec.map bi, U.isoSpec.hom ≫ Spec.map (c.ι.app i),
    V.isoSpec.hom ≫ Spec.map ki, hqi, sq₁.paste_horiz sq₀⟩

private theorem exists_surjective_affine_finite_baseChange
    {V U : Scheme.{u}} [IsAffine V] [IsAffine U] [IsNoetherian U]
    (h : V ⟶ U) (hqf : h.IsQuasiFinite) :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (_ : IsNoetherian T) (a : T ⟶ U),
      Surjective a ∧ IsFinite (pullback.snd h a) := by
  classical
  let : LocallyOfFiniteType h := hqf.1
  let : QuasiCompact h := hqf.2.1
  let : LocallyQuasiFinite h := locallyQuasiFinite_of_isQuasiFinite h hqf
  obtain ⟨S, hS⟩ := h.exists_stratification_isFinite
  have hn (i : Fin S.n) : IsNoetherian (S.domain i) := by
    have : TopologicalSpace.NoetherianSpace (S.domain i) :=
      (S.immersion i).isEmbedding.isInducing.noetherianSpace
    exact isNoetherian_of_locallyOfFiniteType (S.immersion i)
  have hc (i : Fin S.n) : CompactSpace (S.domain i) := by
    let := hn i
    infer_instance
  let := hc
  choose n T j hj hcover using fun i : Fin S.n ↦
    (S.domain i).exists_partition_isImmersion_isAffine_isReduced
  let I := Σ i : Fin S.n, Fin (n i)
  let B : I → Scheme.{u} := fun i ↦ T i.1 i.2
  let b : ∀ i : I, B i ⟶ U := fun i ↦ j i.1 i.2 ≫ S.immersion i.1
  have hB (i : I) : IsAffine (B i) := (hj i.1 i.2).2.1
  let := hB
  let a : (∐ B) ⟶ U := Sigma.desc b
  have ha : Surjective a := ⟨by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    obtain ⟨y, hy⟩ : x ∈ Set.range (S.immersion i) := by
      simpa only [S.range_immersion] using hi
    obtain ⟨k, ⟨z, hz⟩, _⟩ := hcover i y
    refine ⟨Sigma.ι B ⟨i, k⟩ z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    change S.immersion i (j i k z) = x
    rw [hz, hy]⟩
  have hft (i : I) : LocallyOfFiniteType (b i) := by
    have : IsImmersion (j i.1 i.2) := (hj i.1 i.2).1
    dsimp [b]
    infer_instance
  have : LocallyOfFiniteType a := IsZariskiLocalAtSource.sigmaDesc hft
  have hfin (i : I) : IsFinite (pullback.snd h (b i)) := by
    have := hS i.1
    have he := pullbackLeftPullbackSndIso_inv_snd_snd h (S.immersion i.1) (j i.1 i.2)
    change IsFinite (pullback.snd h (j i.1 i.2 ≫ S.immersion i.1))
    rw [← he]
    infer_instance
  have htotal : IsFinite (pullback.snd h a) := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (sigmaOpenCover B)
    intro i
    change I at i
    change IsFinite (pullback.snd (pullback.snd h a) (Sigma.ι B i))
    have hp := (IsPullback.of_hasPullback (pullback.snd h a) (Sigma.ι B i)).paste_horiz
      (IsPullback.of_hasPullback h a)
    have hi : Sigma.ι B i ≫ a = b i := Sigma.ι_comp_desc b i
    rw [hi] at hp
    have := hfin i
    rw [← hp.isoPullback_hom_snd]
    infer_instance
  exact ⟨∐ B, inferInstance, isNoetherian_of_locallyOfFiniteType a, a, ha, htotal⟩

private theorem closedImmersion_sigmaDesc
    {I : Type*} [Small.{u} I] [Finite I] {X : I → Scheme.{u}} {Y : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (f i)]
    (hd : Pairwise (fun i j ↦ Disjoint (Set.range (f i)) (Set.range (f j)))) :
    IsClosedImmersion (Sigma.desc f) := by
  have : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  refine ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (Sigma.desc f).continuous ?_ ?_⟩
  · intro x y hxy
    obtain ⟨i, x, rfl⟩ := (sigmaOpenCover X).exists_eq x
    obtain ⟨j, y, rfl⟩ := (sigmaOpenCover X).exists_eq y
    change (Sigma.desc f) (Sigma.ι X i x) = (Sigma.desc f) (Sigma.ι X j y) at hxy
    change Sigma.ι X i x = Sigma.ι X j y
    have hf : f i x = f j y := by
      simpa only [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using hxy
    by_cases hij : i = j
    · subst j
      exact congrArg (Sigma.ι X i) ((f i).isClosedEmbedding.injective hf)
    · exact False.elim (Set.disjoint_left.mp (hd hij) ⟨x, rfl⟩ ⟨y, hf.symm⟩)
  · intro A hA
    have heq : (Sigma.desc f) '' A =
        ⋃ i, f i '' ((Sigma.ι X i) ⁻¹' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, z, rfl⟩ := (sigmaOpenCover X).exists_eq x
        refine Set.mem_iUnion.mpr ⟨i, z, hx, ?_⟩
        change f i z = (Sigma.desc f) (Sigma.ι X i z)
        simp only [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      · rintro hy
        obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
        refine ⟨Sigma.ι X i z, hz, ?_⟩
        simp only [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    rw [heq]
    exact isClosed_iUnion_of_finite fun i ↦ (f i).isClosedEmbedding.isClosedMap _
      (hA.preimage (Sigma.ι X i).continuous)

private theorem closedImmersion_sigmaι
    {I : Type*} [Small.{u} I] (X : I → Scheme.{u}) (i : I) : IsClosedImmersion (Sigma.ι X i) := by
  apply IsClosedImmersion.of_isPreimmersion
  classical
  have heq : (Set.range (Sigma.ι X i))ᶜ =
      ⋃ j : {j : I // j ≠ i}, Set.range (Sigma.ι X j.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, z, rfl⟩ := (sigmaOpenCover X).exists_eq x
      have hji : j ≠ i := by
        rintro rfl
        exact hx ⟨z, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, z, rfl⟩
    · intro hx hi
      obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hx
      obtain ⟨w, hw⟩ := hi
      exact j.2 (congrArg Sigma.fst ((sigmaι_eq_iff X _ _ _ _).mp (hz.trans hw.symm)))
  rw [← isOpen_compl_iff, heq]
  exact isOpen_iUnion fun j ↦ (Sigma.ι X j.1).isOpenEmbedding.isOpen_range

private theorem assemble_section_partition
    {Y X : Scheme.{u}} (h : Y ⟶ X) [IsFinite h]
    (m : ℕ) (R : Fin m → Scheme.{u}) (r : ∀ a, R a ⟶ X)
    (hR : ∀ a, IsAffine (R a))
    (hcover : ∀ x : X, ∃ (a : Fin m) (z : R a), r a z = x)
    (hsections : ∀ a : Fin m, ∃ (q : ℕ) (t : Fin q → (R a ⟶ pullback h (r a))),
      (∀ k, IsClosedImmersion (t k) ∧ IsIso (t k ≫ pullback.snd h (r a))) ∧
      Pairwise (fun k l ↦ Disjoint (Set.range (t k)) (Set.range (t l))) ∧
      ∀ y : ↥(pullback h (r a)), ∃ (k : Fin q) (z : R a), t k z = y) :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (a : T ⟶ X),
      Surjective a ∧ ∃ (E : Scheme.{u}) (i : E ⟶ pullback h a),
        IsThickening i ∧ IsFinite (i ≫ pullback.snd h a) ∧
          Etale (i ≫ pullback.snd h a) := by
  classical
  let := hR
  let a : (∐ R) ⟶ X := Sigma.desc r
  have ha : Surjective a := ⟨by
    intro x
    obtain ⟨k, z, hz⟩ := hcover x
    exact ⟨Sigma.ι R k z, by simpa only [← Scheme.Hom.comp_apply, a, Sigma.ι_comp_desc] using hz⟩⟩
  choose q t ht hd hc using hsections
  let P := pullback h a
  let v (k : Fin m) : pullback h (r k) ⟶ P :=
    pullback.lift (pullback.fst h (r k))
      (pullback.snd h (r k) ≫ Sigma.ι R k) (by simp [a, pullback.condition])
  have hv (k : Fin m) : IsPullback (v k) (pullback.snd h (r k))
      (pullback.snd h a) (Sigma.ι R k) := by
    apply IsPullback.of_right _ (by simp [v]) (IsPullback.of_hasPullback h a)
    simpa only [v, pullback.lift_fst, a, Sigma.ι_comp_desc] using
      (IsPullback.of_hasPullback h (r k))
  have hvclosed (k : Fin m) : IsClosedImmersion (v k) := by
    have := closedImmersion_sigmaι R k
    exact MorphismProperty.of_isPullback (hv k).flip inferInstance
  let I := Σ k : Fin m, Fin (q k)
  let E : I → Scheme.{u} := fun x ↦ R x.1
  let f : ∀ x : I, E x ⟶ P := fun x ↦ t x.1 x.2 ≫ v x.1
  have hfc (x : I) : IsClosedImmersion (f x) := by
    have := (ht x.1 x.2).1
    have := hvclosed x.1
    dsimp [f]
    infer_instance
  let := hfc
  have hfd : Pairwise (fun x y ↦ Disjoint (Set.range (f x)) (Set.range (f y))) := by
    intro x y hxy
    apply Set.disjoint_left.mpr
    rintro z ⟨u, rfl⟩ ⟨w, hw⟩
    by_cases hij : x.1 = y.1
    · rcases x with ⟨x, k⟩
      rcases y with ⟨y, l⟩
      dsimp at hij
      subst y
      have hkl : k ≠ l := fun e ↦ hxy (by cases e; rfl)
      have heq : t x l w = t x k u := (v x).isClosedEmbedding.injective hw
      exact Set.disjoint_left.mp (hd x hkl) ⟨u, rfl⟩ ⟨w, heq⟩
    · have heq := congrArg (fun z : P ↦ pullback.snd h a z) hw
      have hh : Sigma.ι R y.1 ((t y.1 y.2 ≫ pullback.snd h (r y.1)) w) =
          Sigma.ι R x.1 ((t x.1 x.2 ≫ pullback.snd h (r x.1)) u) := by
        change ((t y.1 y.2 ≫ v y.1) ≫ pullback.snd h a) w =
          ((t x.1 x.2 ≫ v x.1) ≫ pullback.snd h a) u at heq
        simpa only [Category.assoc, (hv y.1).w, (hv x.1).w,
          Scheme.Hom.comp_apply] using heq
      exact hij (congrArg Sigma.fst ((sigmaι_eq_iff R _ _ _ _).mp hh)).symm
  let i : (∐ E) ⟶ P := Sigma.desc f
  have hic : IsClosedImmersion i := by
    exact closedImmersion_sigmaDesc f hfd
  have his : Surjective i := ⟨by
    intro z
    obtain ⟨k, x, hx⟩ := (sigmaOpenCover R).exists_eq (pullback.snd h a z)
    obtain ⟨y, hy, hyx⟩ := Scheme.exists_preimage_of_isPullback (hv k)
      z x hx.symm
    obtain ⟨l, w, hw⟩ := hc k y
    refine ⟨Sigma.ι E ⟨k, l⟩ w, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    change v k (t k l w) = z
    rw [hw, hy]⟩
  have het : Etale (i ≫ pullback.snd h a) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (sigmaOpenCover E)
    intro x
    change Etale (Sigma.ι E x ≫ i ≫ pullback.snd h a)
    rw [← Category.assoc, show Sigma.ι E x ≫ i = f x from Sigma.ι_comp_desc f x]
    have : IsIso (t x.1 x.2 ≫ pullback.snd h (r x.1)) := (ht x.1 x.2).2
    change Etale ((t x.1 x.2 ≫ v x.1) ≫ pullback.snd h a)
    rw [Category.assoc, (hv x.1).w, ← Category.assoc]
    infer_instance
  let := hic
  exact ⟨∐ R, inferInstance, a, ha, ∐ E, i, ⟨hic, his⟩, inferInstance, het⟩

private theorem compose_thickening_cover
    {Y X T S E : Scheme.{u}} (h : Y ⟶ X) (b : T ⟶ X) (c : S ⟶ T)
    (i : E ⟶ pullback (pullback.snd h b) c) (hi : IsThickening i)
    (hf : IsFinite (i ≫ pullback.snd (pullback.snd h b) c))
    (he : Etale (i ≫ pullback.snd (pullback.snd h b) c)) :
    ∃ j : E ⟶ pullback h (c ≫ b), IsThickening j ∧
      IsFinite (j ≫ pullback.snd h (c ≫ b)) ∧ Etale (j ≫ pullback.snd h (c ≫ b)) := by
  let e := pullbackLeftPullbackSndIso h b c
  have : IsClosedImmersion i := hi.1
  have : Surjective i := hi.2
  refine ⟨i ≫ e.hom, ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · simpa only [Category.assoc, e, pullbackLeftPullbackSndIso_hom_snd] using hf
  · simpa only [Category.assoc, e, pullbackLeftPullbackSndIso_hom_snd] using he

private theorem finite_affine_thickening
    {Y X : Scheme.{u}} [IsAffine X] [IsNoetherian X] (h : Y ⟶ X) [IsFinite h] :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (a : T ⟶ X),
      Surjective a ∧ ∃ (E : Scheme.{u}) (i : E ⟶ pullback h a),
        IsThickening i ∧ IsFinite (i ≫ pullback.snd h a) ∧
          Etale (i ≫ pullback.snd h a) := by
  obtain ⟨X', b, hbaff, hbsurj, hbfree, W, p, j, hW, hp, hj, hjp,
    ⟨n, Z, s, hs, hcover⟩, _, _⟩ := exists_finite_affine_section_cover h
  let := hbaff
  let := hbfree
  let := hW
  let := hp
  let := hj
  have : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType b
  obtain ⟨m, R, r, hR, hc, ht⟩ :=
    exists_closed_section_affine_partition (pullback.snd h b) p j hjp n Z s hs hcover
  obtain ⟨T, hT, c, hcsurj, E, i, hi, hfin, het⟩ :=
    assemble_section_partition (pullback.snd h b) m R r (fun k ↦ (hR k).1) hc ht
  obtain ⟨j', hj', hf', he'⟩ := compose_thickening_cover h b c i hi hfin het
  let := hbsurj
  let := hcsurj
  exact ⟨T, hT, c ≫ b, inferInstance, E, j', hj', hf', he'⟩

/-- A quasi-finite finitely presented morphism of affine schemes admits a surjective affine
base change on which the source has a finite etale closed subscheme with the same points.
-/
theorem exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite
    {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (h : V ⟶ U)
    (hqf : Scheme.Hom.IsQuasiFinite h)
    (hfp : LocallyOfFinitePresentation h ∧ QuasiCompact h ∧ QuasiSeparated h) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (a : U' ⟶ U),
      Surjective a ∧ ∃ (Z : Scheme.{u}) (i : Z ⟶ pullback h a),
        IsThickening i ∧ IsFinite (i ≫ pullback.snd h a) ∧
          Etale (i ≫ pullback.snd h a) := by
  let : LocallyOfFinitePresentation h := hfp.1
  obtain ⟨U₀, V₀, hU₀, hV₀, hn₀, h₀, b, v, hq₀, sq⟩ :=
    exists_noetherian_affine_model h hqf
  let := hU₀
  let := hV₀
  let := hn₀
  obtain ⟨T, hT, hnT, c, hcs, hcf⟩ := exists_surjective_affine_finite_baseChange h₀ hq₀
  let := hT
  let := hnT
  let := hcf
  obtain ⟨S, hS, d, hds, E, i, hi, hf, he⟩ := finite_affine_thickening (pullback.snd h₀ c)
  obtain ⟨j, hj, hjf, hje⟩ := compose_thickening_cover h₀ c d i hi hf he
  let := hS
  let := hcs
  let := hds
  let := hjf
  let := hje
  exact thickening_baseChange h h₀ b v sq (d ≫ c) j hj

end AlgebraicGeometry
