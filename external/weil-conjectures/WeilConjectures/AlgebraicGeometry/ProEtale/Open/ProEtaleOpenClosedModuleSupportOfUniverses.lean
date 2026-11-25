/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
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
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianSpecializationOfUniverses
import WeilConjectures.RingTheory.ProperBaseChange.BoundedWContractibleExtension
import WeilConjectures.RingTheory.ProperBaseChange.WContractibleClosedLocalization
import WeilConjectures.AlgebraicGeometry.Affine.AffineClosedSpecializationLocalization
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Open and closed support for modules in independent universes

## References

* Stacks Project, Tags 09AG, 09AH and 09BM
* Stacks Project, with arbitrary ring sheaves
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_over_proEtTopology
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- The direct-sum/sheafification Hom argument works for any disjoint morphism.
private theorem pullback_extension_isZero
    {X Z : Scheme.{t}} (i : Z ⟶ X) (U : X.ProEt)
    (hd : Disjoint (Set.range U.hom) (Set.range i))
    (R : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    (M : SheafOfModules.{max u (t + 1)}
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R).over U)) :
    IsZero ((Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange i)
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)).obj
        ((SheafOfModules.toSheaf _).obj
          ((SheafOfModules.localizedSystemExtension.{t + 1, t, u} R U).obj M))) := by
  classical
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  let P := ((SheafOfModules.extensionByZeroPresheaf.{max u (t + 1)} A U).obj M).presheaf
  let B := Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  let D := (proEtaleBaseChange i).sheafPushforwardContinuous
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  have hz (H : Sheaf (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)}) :
      Subsingleton (P ⟶ ((sheafToPresheaf _ _).obj (D.obj H))) := by
    refine ⟨fun f g ↦ ?_⟩
    ext V x
    change (f.app V) x = (g.app V) x
    change DirectSum (V.unop ⟶ U) (fun φ ↦ M.val.obj (op (Over.mk φ))) at x
    induction x using DirectSum.induction_on with
    | zero =>
      exact (map_zero (f.app V).hom).trans (map_zero (g.app V).hom).symm
    | of φ x =>
      have hempty : IsEmpty ((proEtaleBaseChange i).obj V.unop).left := by
        apply Scheme.isEmpty_pullback
        apply Set.disjoint_left.mpr
        rintro y ⟨v, rfl⟩ hy
        have hv : V.unop.hom v ∈ Set.range U.hom := by
          refine ⟨φ.left v, ?_⟩
          exact congrArg (fun k : V.unop.left ⟶ X ↦ k v) φ.w
        exact Set.disjoint_left.mp hd hv hy
      have hterminal := ProEt.isTerminalSectionsOfIsEmpty H
        ((proEtaleBaseChange i).obj V.unop)
      have : Subsingleton (H.obj.obj (op ((proEtaleBaseChange i).obj V.unop))) :=
        AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero _).of_iso (hterminal.uniqueUpToIso HasZeroObject.zeroIsTerminal))
      exact @Subsingleton.elim (H.obj.obj (op ((proEtaleBaseChange i).obj V.unop)))
        this _ _
    | add x y hx hy =>
      change (f.app V).hom (x + y) = (g.app V).hom (x + y)
      simp only [map_add, hx, hy]
  have hinit : IsInitial (B.obj ((presheafToSheaf
      (ProEt.topology X) AddCommGrpCat.{max u (t + 1)}).obj P)) := by
    refine IsInitial.ofUnique (h := fun H ↦ ?_)
    let e := (a.homEquiv _ H).trans
      ((sheafificationAdjunction (ProEt.topology X)
        AddCommGrpCat.{max u (t + 1)}).homEquiv P (D.obj H))
    let : Subsingleton (P ⟶ (sheafToPresheaf _ _).obj (D.obj H)) := hz H
    let : Unique (P ⟶ (sheafToPresheaf _ _).obj (D.obj H)) :=
      ⟨⟨0⟩, fun _ ↦ Subsingleton.elim _ _⟩
    exact Equiv.unique e
  exact hinit.isZero

private theorem ring_localization_cover {X Z : Scheme.{t}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Type t) [CommRing R] (g : Spec (CommRingCat.of R) ⟶ X) [WeaklyEtale g]
    (hR : ∀ (D : Type t) [CommRing D] (φ : R →+* D),
      φ.FaithfullyFlat → φ.WeaklyEtale → ∃ r : D →+* R, r.comp φ = RingHom.id R) :
    ∃ (n : ℕ) (V : Option (Fin n) → X.ProEt) (f : ∀ j, V j ⟶ ProEt.mk g),
      Presieve.ofArrows V f ∈ ProEt.precoverage X (ProEt.mk g) ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (e : P ⟶ Q),
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
    IsLocalization.wcontractible_closed_localization.{t, 0} R B J s.card a ha hV
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
        exact ProEt.surjective_app_of_affine_ring_retractions.{t, u} X B (E.f none ≫ g)
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

private theorem exists_split_affine_extension (A : Type t) [CommRing A] :
    ∃ (D : Type t) (_ : CommRing D) (φ : A →+* D),
      Presieve.singleton (Spec.map (CommRingCat.ofHom φ)) ∈
        proetalePrecoverage (Spec (CommRingCat.of A)) ∧
      (∀ (B : Type t) [CommRing B] (g : D →+* B),
        g.FaithfullyFlat → g.WeaklyEtale →
          ∃ r : B →+* D, r.comp g = RingHom.id D) := by
  obtain ⟨D, hD, φ, _, _, _, hsplit, hcover⟩ :=
    RingHom.exists_bounded_wContractible_extension.{t, 0} A
      (max Cardinal.aleph0 (Cardinal.mk A)) (le_max_left _ _) (le_max_right _ _)
  exact ⟨D, hD, φ, hcover, hsplit⟩

private theorem localization_cover {X Z : Scheme.{t}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (T : X.ProEt) :
    ∃ (I : Type (t + 1)) (V : I → X.ProEt) (f : ∀ j, V j ⟶ T),
      Presieve.ofArrows V f ∈ ProEt.precoverage X T ∧
      ∀ j, (Nonempty (V j ⟶ U)) ∨
        (IsAffine (V j).left ∧
          (∀ (P Q : Sheaf (ProEt.topology X) (Type (max u (t + 1)))) (e : P ⟶ Q),
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
  let B := (C.bind E).reindex (Equiv.ulift : ULift.{t + 1} _ ≃ _)
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

private theorem support_detect_isIso
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})
    {M N : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)}
    (f : M ⟶ N)
    [IsIso ((SheafOfModules.localizedSystemRestriction.{t + 1, t, u} R U).map f)]
    [IsIso ((Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange i)
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)).map
        ((SheafOfModules.toSheaf _).map f))] : IsIso f := by
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  let E := SheafOfModules.toSheaf.{max u (t + 1)} A
  let B := Functor.sheafPullbackConstruction.sheafPullback
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  let D := (proEtaleBaseChange i).sheafPushforwardContinuous
    AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleBaseChange i) AddCommGrpCat.{max u (t + 1)}
      (ProEt.topology X) (ProEt.topology Z)
  have hlocal (T : X.ProEt) :
      ∃ (I : Type (t + 1)) (V : I → X.ProEt) (g : ∀ j, V j ⟶ T),
        Presieve.ofArrows V g ∈ ProEt.precoverage X T ∧
          ∀ j, Function.Bijective (f.val.app (op (V j))) := by
    obtain ⟨I, V, g, hg, hV⟩ := localization_cover i U hU T
    refine ⟨I, V, g, hg, fun j ↦ ?_⟩
    rcases hV j with hopen | ⟨hA, hw, hs⟩
    · obtain ⟨φ⟩ := hopen
      exact ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.evaluation (A.over U) (op (Over.mk φ))).map
          ((SheafOfModules.localizedSystemRestriction.{t + 1, t, u} R U).map f))
    · have := hA
      let ev := sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⋙
        (CategoryTheory.evaluation _ _).obj (op (V j))
      have hM := proEtale_abelian_unit_bijective_of_specialization
        i (V j) hw hs B a (E.obj M)
      have hN := proEtale_abelian_unit_bijective_of_specialization
        i (V j) hw hs B a (E.obj N)
      have : IsIso (ev.map (a.unit.app (E.obj M))) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hM
      have : IsIso (ev.map (a.unit.app (E.obj N))) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hN
      have he := congrArg ev.map (a.unit.naturality (E.map f))
      simp only [Functor.id_map, Functor.comp_map, Functor.map_comp] at he
      have : IsIso (ev.map (E.map f) ≫ ev.map (a.unit.app (E.obj N))) := by
        rw [he]
        infer_instance
      have : IsIso (ev.map (E.map f)) :=
        IsIso.of_isIso_comp_right _ (ev.map (a.unit.app (E.obj N)))
      exact ConcreteCategory.bijective_of_isIso (ev.map (E.map f))
  have hi : Presheaf.IsLocallyInjective (ProEt.topology X) (E.map f).hom := by
    constructor
    intro T x y hxy
    change f.val.app T x = f.val.app T y at hxy
    obtain ⟨I, V, g, hg, hb⟩ := hlocal T.unop
    apply (ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hg)
    rw [Sieve.generate_le_iff]
    rintro W q ⟨j⟩
    change M.val.map (g j).op x = M.val.map (g j).op y
    apply (hb j).injective
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hxy]
  have hs : Presheaf.IsLocallySurjective (ProEt.topology X) (E.map f).hom := by
    constructor
    intro T y
    obtain ⟨I, V, g, hg, hb⟩ := hlocal T
    apply (ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hg)
    rw [Sieve.generate_le_iff]
    rintro W q ⟨j⟩
    exact (hb j).surjective (N.val.map (g j).op y)
  have : IsIso (E.map f) := (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso f E

/-- Complementary restrictions detect module isomorphisms, and closed restriction
annihilates open extension. Neither assertion concerns preservation of products. -/
theorem proEtaleOpenClosedModuleSupportOfUniverses
    {X Z : Scheme.{t}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}) :
    let A := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
    let I := SheafOfModules.toSheaf.{max u (t + 1)} A ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange i)
        AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)
    (∀ M, IsZero (I.obj ((SheafOfModules.localizedSystemExtension.{t + 1, t, u}
      R U).obj M))) ∧
    (∀ {M N : SheafOfModules.{max u (t + 1)} A} (f : M ⟶ N),
      IsIso ((SheafOfModules.localizedSystemRestriction.{t + 1, t, u} R U).map f) →
      IsIso (I.map f) → IsIso f) := by
  refine ⟨?_, ?_⟩
  · intro M
    exact pullback_extension_isZero i U (by rw [hU]; exact disjoint_compl_left) R M
  · intro M N f hj hi
    exact @support_detect_isIso _ _ i _ U _ _ hU R M N f hj hi

end AlgebraicGeometry.Scheme
