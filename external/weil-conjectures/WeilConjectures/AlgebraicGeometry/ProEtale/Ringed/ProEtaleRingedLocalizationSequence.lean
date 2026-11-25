/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Homology.ExactSequence

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.RingTheory.ProperBaseChange.BoundedWContractibleExtension
import WeilConjectures.RingTheory.ProperBaseChange.WContractibleClosedLocalization
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleShriekSpecializationZero
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Triple
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleSpecializationUnit

/-! Ringed pro-etale localization: a geometric step of the open-closed argument.

## References

* Stacks Project, Tag 09AH, 098H, 09AC and 09AG
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem module_epi_of_local_surjective {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    {F G : SheafOfModules.{u + 1} R} (a : F ⟶ G)
    (h : ∀ T : X.ProEt, ∃ (I : Type (u + 1)) (V : I → X.ProEt)
      (f : ∀ j, V j ⟶ T), Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
        ∀ j, Function.Surjective (a.val.app (op (V j)))) : Epi a := by
  let E := SheafOfModules.toSheaf R
  have hl : Sheaf.IsLocallySurjective (E.map a) := by
    constructor
    intro T s
    obtain ⟨I, V, f, hf, hs⟩ := h T
    apply (ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hf)
    rw [Sieve.generate_le_iff]
    rintro W g ⟨j⟩
    exact hs j (G.val.map (f j).op s)
  have : Epi (E.map a) := Sheaf.epi_of_isLocallySurjective (E.map a)
  constructor
  intro P s t hst
  apply E.map_injective
  apply (cancel_epi (E.map a)).mp
  simpa only [← E.map_comp] using congrArg E.map hst

private theorem module_shortExact_of_local_sections {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    {F G H : SheafOfModules.{u + 1} R} (a : F ⟶ G) (b : G ⟶ H)
    (h : ∀ T : X.ProEt, ∃ (I : Type (u + 1)) (V : I → X.ProEt)
      (f : ∀ j, V j ⟶ T), Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
        ∀ j, Function.Injective (a.val.app (op (V j))) ∧
          Function.Surjective (b.val.app (op (V j))) ∧
          Function.Exact (a.val.app (op (V j))) (b.val.app (op (V j)))) :
    Mono a ∧ Epi b ∧ (ComposableArrows.mk₂ a b).Exact := by
  have hinj (T : X.ProEt) : Function.Injective (a.val.app (op T)) := by
    intro s t hst
    obtain ⟨I, V, f, hf, hj⟩ := h T
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp F.isSheaf)
    apply (hsh _ (Precoverage.generate_mem_toGrothendieck hf)).isSeparatedFor.ext
    rintro W g ⟨W', p, q, ⟨j⟩, rfl⟩
    change F.val.map (p ≫ f j).op s = F.val.map (p ≫ f j).op t
    rw [op_comp]
    simp only [PresheafOfModules.map_comp_apply]
    congr 1
    apply (hj j).1
    have hn (x : F.val.obj (op T)) :
        a.val.app (op (V j)) (F.val.map (f j).op x) =
          G.val.map (f j).op (a.val.app (op T) x) :=
      PresheafOfModules.naturality_apply a.val (f j).op x
    rw [hn, hn, hst]
  have ha : Mono a := by
    constructor
    intro P s t hst
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply hinj T.unop
    exact congrArg (fun k : P ⟶ G ↦ k.val.app T x) hst
  have hb : Epi b := module_epi_of_local_surjective R b (by
    intro T
    obtain ⟨I, V, f, hf, hj⟩ := h T
    exact ⟨I, V, f, hf, fun j ↦ (hj j).2.1⟩)
  have hz : a ≫ b = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨I, V, f, hf, hj⟩ := h T.unop
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp H.isSheaf)
    apply (hsh _ (Precoverage.generate_mem_toGrothendieck hf)).isSeparatedFor.ext
    rintro W g ⟨W', p, q, ⟨j⟩, rfl⟩
    have hzj := ((hj j).2.2 (a.val.app (op (V j))
      (F.val.map (f j).op x))).mpr ⟨_, rfl⟩
    change H.val.map (p ≫ f j).op
      (b.val.app T (a.val.app T x)) = H.val.map (p ≫ f j).op 0
    rw [op_comp]
    simp only [PresheafOfModules.map_comp_apply]
    have hn : H.val.map (f j).op (b.val.app T (a.val.app T x)) = 0 := by
      rw [← PresheafOfModules.naturality_apply b.val (f j).op,
        ← PresheafOfModules.naturality_apply a.val (f j).op]
      exact hzj
    rw [hn]
    simp only [map_zero]
  let S := ShortComplex.mk a b hz
  have he : S.Exact := by
    apply S.exact_iff_epi_kernel_lift.mpr
    apply module_epi_of_local_surjective R (kernel.lift b a hz)
    intro T
    obtain ⟨I, V, f, hf, hj⟩ := h T
    refine ⟨I, V, f, hf, ?_⟩
    intro j s
    let E := SheafOfModules.evaluation R (op (V j))
    have hinj : Function.Injective (E.map (kernel.ι b)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hs : b.val.app _ ((kernel.ι b).val.app _ s) = 0 := by
      exact congrArg (fun k : kernel b ⟶ H ↦ k.val.app _ s) (kernel.condition b)
    obtain ⟨t, ht⟩ := ((hj j).2.2 _).mp hs
    refine ⟨t, hinj ?_⟩
    exact (congrArg (fun k : F ⟶ G ↦ k.val.app _ t) (kernel.lift_ι b a hz)).trans ht
  exact ⟨ha, hb, S.exact_iff_exact_toComposableArrows.mp he⟩
end AlgebraicGeometry.Scheme

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ring_localization_cover {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Type u) [CommRing R] (g : Spec (CommRingCat.of R) ⟶ X) [WeaklyEtale g]
    (hR : ∀ (D : Type u) [CommRing D] (φ : R →+* D),
      φ.FaithfullyFlat → φ.WeaklyEtale → ∃ r : D →+* R, r.comp φ = RingHom.id R) :
    ∃ (n : ℕ) (V : Option (Fin n) → X.ProEt) (f : ∀ j, V j ⟶ ProEt.mk g),
      Presieve.ofArrows V f ∈ ProEt.precoverage X (ProEt.mk g) ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (e : P ⟶ Q),
            Epi e → Function.Surjective (e.hom.app (op (V j)))) ∧
          (∀ v : (V j).left, ∃ z : ↥(pullback (V j).hom i),
            Specializes v ((pullback.fst (V j).hom i) z))) := by
  classical
  let C : Set (PrimeSpectrum R) := g ⁻¹' Set.range i
  have hC : IsClosed C := i.isClosedEmbedding.isClosed_range.preimage g.continuous
  have hcompact : IsCompact Cᶜ := by
    have : CompactSpace ↥(pullback g U.hom) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst g U.hom)
    have hr : Cᶜ = Set.range (pullback.fst g U.hom) := by
      rw [Scheme.Pullback.range_fst]
      exact (congrArg (Set.preimage g) hU).symm
    rw [hr]
    exact isCompact_range (pullback.fst g U.hom).continuous
  obtain ⟨s, hs⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hcompact, hC.isOpen_compl⟩
  let J : Ideal R := Ideal.span (s : Set R)
  have hJ : PrimeSpectrum.zeroLocus (J : Set R) = C := by
    simpa only [J, PrimeSpectrum.zeroLocus_span, compl_compl] using
      congrArg (fun t : Set (PrimeSpectrum R) ↦ tᶜ) hs
  let e : Fin s.card ≃ s := s.equivFin.symm
  let a : Fin s.card → R := fun k ↦ (e k).val
  have ha : ∀ k, a k ∈ J := fun k ↦ Ideal.subset_span (e k).property
  have har : Set.range a = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).property
    · intro hx
      obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hV : PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (Set.range a) := by
    rw [har, PrimeSpectrum.zeroLocus_span]
  let S : Submonoid R := (IsUnit.submonoid (R ⧸ J)).comap (Ideal.Quotient.mk J)
  let B := Localization S
  obtain ⟨_, _, _, hcover, hsplit⟩ :=
    IsLocalization.wcontractible_closed_localization.{u, 0} R B J s.card a ha hV
  let E := IsLocalization.closedLocalizationFamily R B a
  have hw (j : Option (Fin s.card)) : WeaklyEtale (E.f j) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hcover ⟨j⟩
  let V (j : Option (Fin s.card)) : X.ProEt :=
    have := hw j
    ProEt.mk (E.f j ≫ g)
  let f (j : Option (Fin s.card)) : V j ⟶ ProEt.mk g :=
    MorphismProperty.Over.homMk (E.f j)
  refine ⟨s.card, V, f, ?_, ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hcover
  · intro j
    cases j with
    | some k =>
      left
      have hsub : Set.range (V (some k)).hom ⊆ Set.range U.hom := by
        rintro _ ⟨x, rfl⟩
        rw [hU]
        intro hx
        have hm : PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x ∈ C := hx
        rw [← hJ] at hm
        have hak : a k ∈
            (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x).asIdeal :=
          hm (ha k)
        have hn : a k ∉
            (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x).asIdeal := by
          have hh : PrimeSpectrum.comap (algebraMap R (Localization.Away (a k))) x ∈
              Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (a k)))) :=
            Set.mem_range_self x
          rw [PrimeSpectrum.localization_away_comap_range _ (a k)] at hh
          exact hh
        exact hn hak
      exact ⟨MorphismProperty.Over.homMk
        (IsOpenImmersion.lift U.hom (V (some k)).hom hsub)
        (IsOpenImmersion.lift_fac _ _ _)⟩
    | none =>
      right
      refine ⟨inferInstanceAs (IsAffine (Spec (.of B))), ?_, ?_⟩
      · intro P Q e he
        have := hw none
        exact ProEt.surjective_app_of_affine_ring_retractions.{u, 0} X B (E.f none ≫ g)
          (hsplit hR) P Q e
      · intro v
        obtain ⟨_, _, _, _, hspec⟩ := affineClosedSpecializationLocalization R J S
          (fun _ ↦ Iff.rfl)
        obtain ⟨w, hvw, hwJ⟩ := hspec v
        have hwC : g (E.f none w) ∈ Set.range i := by
          change PrimeSpectrum.comap (algebraMap R B) w ∈ C
          rw [← hJ]
          exact hwJ
        obtain ⟨z, hz⟩ := hwC
        obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := (V none).hom) (g := i) w z hz.symm
        exact ⟨q, hq.symm ▸ hvw⟩

private theorem exists_split_affine_extension (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (φ : A →+* D),
      Presieve.singleton (Spec.map (CommRingCat.ofHom φ)) ∈
        proetalePrecoverage (Spec (CommRingCat.of A)) ∧
      (∀ (B : Type u) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) := by
  obtain ⟨D, hD, φ, _, _, _, hsplit, hcover⟩ :=
    RingHom.exists_bounded_wContractible_extension.{u, 0} A
      (max Cardinal.aleph0 (Cardinal.mk A)) (le_max_left _ _) (le_max_right _ _)
  exact ⟨D, hD, φ, hcover, hsplit⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localization_cover {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (T : X.ProEt) :
    ∃ (I : Type (u + 1)) (V : I → X.ProEt) (f : ∀ j, V j ⟶ T),
      Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (e : P ⟶ Q),
            Epi e → Function.Surjective (e.hom.app (op (V j)))) ∧
          (∀ v : (V j).left, ∃ z : ↥(pullback (V j).hom i),
            Specializes v ((pullback.fst (V j).hom i) z))) := by
  classical
  let A := T.left.affineOpenCover
  choose D hD φ hcover hsplit using fun j : A.I₀ ↦ exists_split_affine_extension (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let p (j : A.I₀) := Spec.map (CommRingCat.ofHom (φ j))
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (p j) (hcover j)
  let B := (C.bind E).reindex (Equiv.ulift : ULift.{u + 1} _ ≃ _)
  have hB (j : B.I₀) : WeaklyEtale (B.f j) :=
    Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) j
  let W (j : B.I₀) : X.ProEt := ProEt.mk (B.f j ≫ T.hom)
  let b (j : B.I₀) : W j ⟶ T := MorphismProperty.Over.homMk (B.f j)
  have hb : Presieve.ofArrows W b ∈ ProEt.precoverage X T := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact B.mem₀
  have hlocal (j : B.I₀) :=
    ring_localization_cover i U hU (D j.down.1) (B.f j ≫ T.hom) (hsplit j.down.1)
  choose n V f hf hV using hlocal
  refine ⟨Σ j, Option (Fin (n j)), fun j ↦ V j.1 j.2,
    fun j ↦ f j.1 j.2 ≫ b j.1, ?_, fun j ↦ hV j.1 j.2⟩
  have : (ProEt.precoverage X).IsStableUnderComposition := by
    dsimp [ProEt.precoverage]
    infer_instance
  exact Precoverage.comp_mem_coverings b hb f hf

end AlgebraicGeometry.Scheme

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem module_empty_sections {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (F : SheafOfModules.{u + 1} R) (V : X.ProEt) [IsEmpty V.left] :
    Subsingleton (F.val.obj (op V)) := by
  let G := (SheafOfModules.toSheaf R).obj F
  let T := (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  let : Unique (T.obj.obj (op V)) := Types.isTerminalEquivUnique _
    (T.isTerminalOfBotCover V (ProEt.bot_mem_topology V))
  change Subsingleton (T.obj.obj (op V))
  infer_instance

private theorem module_shriek_sections_subsingleton
    {X Z : Scheme.{u}} (U : X.ProEt) (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty ↥(pullback U.hom i))
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (G : SheafOfModules.{u + 1} (R.over U)) (V : X.ProEt) [IsAffine V.left]
    (hspec : ∀ v : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes v ((pullback.fst V.hom i) z)) :
    Subsingleton (((SheafOfModules.extensionByZeroPresheaf R U ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).obj G).val.obj (op V)) := by
  let P := ((SheafOfModules.extensionByZeroPresheaf R U).obj G).presheaf
  let F := sheafify (ProEt.topology X) P
  let η := toSheafify (ProEt.topology X) P
  have hF : Presieve.IsSheaf (ProEt.topology X)
      (F ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp
        ((presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj P).property)
  have hzero : ∀ s : F.obj (op V), s = 0 := by
    intro s
    obtain ⟨n, W, f, hcover, hW⟩ := ProEt.exists_specialization_cover_refinement i V
      hspec (Presheaf.imageSieve η s) (Presheaf.imageSieve_mem (ProEt.topology X) η s)
    apply (hF.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
    rintro T f' ⟨j⟩
    obtain ⟨p, hp⟩ := (hW j).1
    have hzP : Subsingleton (P.obj (op (W j))) := by
      have hzG (φ : W j ⟶ U) : Subsingleton (G.val.obj (op (Over.mk φ))) := by
        have hempty := ProEt.empty_of_lift_of_specializes_closed U i hdisjoint
          (W j) (hW j).2 φ.left (MorphismProperty.Over.w φ)
        let H := (SheafOfModules.toSheaf (R.over U)).obj G
        let K := (sheafCompose ((ProEt.topology X).over U)
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj H
        have hbot : (⊥ : Sieve (Over.mk φ)) ∈ (ProEt.topology X).over U (Over.mk φ) := by
          rw [GrothendieckTopology.mem_over_iff, map_bot]
          exact ProEt.bot_mem_topology (W j)
        let : Unique (K.obj.obj (op (Over.mk φ))) := Types.isTerminalEquivUnique _
          (K.isTerminalOfBotCover (Over.mk φ) hbot)
        change Subsingleton (K.obj.obj (op (Over.mk φ)))
        infer_instance
      let (φ : W j ⟶ U) : Subsingleton (G.val.obj (op (Over.mk φ))) := hzG φ
      change Subsingleton (DirectSum (W j ⟶ U)
        (fun φ ↦ G.val.obj (op (Over.mk φ))))
      infer_instance
    change F.map (f j).op s = F.map (f j).op 0
    rw [← hp, Subsingleton.elim p 0]
    simp
  refine ⟨fun s t ↦ ?_⟩
  exact (hzero s).trans (hzero t).symm

end AlgebraicGeometry.Scheme

open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

set_option linter.style.haveILetI false in
private theorem counit_bijective_on_open {X : AlgebraicGeometry.Scheme.{u}}
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{u + 1})
    (U : X.ProEt) [AlgebraicGeometry.IsOpenImmersion U.hom]
    (aj : (extensionByZeroPresheaf.{u + 1} R U ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)) ⊣ overFunctor.{u + 1} R U)
    (M : SheafOfModules.{u + 1} R) (V : X.ProEt) (φ : V ⟶ U) :
    Function.Bijective ((aj.counit.app M).val.app (op V)) := by
  let b := SheafOfModules.overPushforwardOverAdj (R := R) U
  have hsub : ∀ W : X.ProEt, Subsingleton (W ⟶ U) := by
    intro W
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact f.w.trans g.w.symm
  have hfull : (Over.forget U).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (@Subsingleton.elim _ (hsub V.left) _ _), rfl⟩
  letI : (Over.forget U).Full := hfull
  haveI : IsIso (Over.forgetAdjStar U).unit := inferInstance
  haveI : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
    infer_instance
  let t : Adjunction.Triple _ _ _ := ⟨aj, b⟩
  haveI : IsIso aj.unit := t.isIso_unit_iff_isIso_counit.mpr inferInstance
  haveI : IsIso ((overFunctor R U).map (aj.counit.app M)) := by
    have htri := aj.right_triangle_components M
    have hcomp : IsIso (aj.unit.app ((overFunctor R U).obj M) ≫
        (overFunctor R U).map (aj.counit.app M)) := htri ▸ inferInstance
    exact IsIso.of_isIso_comp_left (aj.unit.app ((overFunctor R U).obj M)) _
  let E := evaluation (R.over U) (op (Over.mk φ))
  haveI : IsIso (E.map ((overFunctor R U).map (aj.counit.app M))) := inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (E.map ((overFunctor R U).map (aj.counit.app M)))

end SheafOfModules

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual counit and unit form the open-closed short exact sequence with
arbitrary module coefficients. This is the local geometric step, without the
formal exactness consequences or the filtered-colimit assertion. -/
theorem proEtale_ringed_localization_sequence {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))
    (aj : (SheafOfModules.extensionByZeroPresheaf.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U ⋙
      PresheafOfModules.sheafification (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)) ⊣
      SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) :
    ∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
      (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact := by
  intro M
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  have hd : IsEmpty ↥(pullback U.hom i) := by
    apply Scheme.isEmpty_pullback
    rw [hU]
    exact disjoint_compl_left
  apply module_shortExact_of_local_sections R (aj.counit.app M) (ai.unit.app M)
  intro T
  obtain ⟨I, V, f, hf, hV⟩ := localization_cover i U hU T
  refine ⟨I, V, f, hf, ?_⟩
  intro j
  rcases hV j with hopen | ⟨hA, hw, hs⟩
  · obtain ⟨φ⟩ := hopen
    have hc := SheafOfModules.counit_bijective_on_open R U aj M (V j) φ
    have hempty : IsEmpty ↥(pullback (V j).hom i) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro x ⟨v, rfl⟩ hx
      have hm : (V j).hom v ∈ Set.range U.hom := by
        refine ⟨φ.left v, ?_⟩
        exact congrArg (fun g : (V j).left ⟶ X ↦ g v)
          (MorphismProperty.Over.w φ)
      rw [hU] at hm
      exact hm hx
    have : IsEmpty ((proEtaleBaseChange i).obj (V j)).left := by
      change IsEmpty ↥(pullback (V j).hom i)
      exact hempty
    have hz := module_empty_sections _ ((proEtaleModuleInverseImage i A).obj M)
      ((proEtaleBaseChange i).obj (V j))
    have hz' : Subsingleton (((proEtaleModuleInverseImage i A ⋙
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
          (J := ProEt.topology X) (K := ProEt.topology Z) (S := R)
          (R := (sheafCompose (ProEt.topology Z)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))
          ⟨Functor.whiskerRight
            ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj M).val.obj (op (V j))) := by
      change Subsingleton (((proEtaleModuleInverseImage i A).obj M).val.obj
        (op ((proEtaleBaseChange i).obj (V j))))
      exact hz
    refine ⟨hc.1, ?_, ?_⟩
    · intro y
      exact ⟨0, @Subsingleton.elim _ hz' _ _⟩
    · intro y
      exact ⟨fun _ ↦ hc.2 y, fun _ ↦ @Subsingleton.elim _ hz' _ _⟩
  · have := hA
    have hz := module_shriek_sections_subsingleton U i hd R
      ((SheafOfModules.overFunctor R U).obj M) (V j) hs
    have hb := proEtale_module_unit_bijective_of_specialization i (V j) hw hs A ai M
    refine ⟨fun _ _ _ ↦ @Subsingleton.elim _ hz _ _, hb.2, ?_⟩
    intro y
    constructor
    · intro hy
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact hb.1 ((map_zero _).trans hy.symm)
    · rintro ⟨x, rfl⟩
      have hx : x = 0 := @Subsingleton.elim _ hz _ _
      rw [hx, map_zero, map_zero]

end AlgebraicGeometry.Scheme
