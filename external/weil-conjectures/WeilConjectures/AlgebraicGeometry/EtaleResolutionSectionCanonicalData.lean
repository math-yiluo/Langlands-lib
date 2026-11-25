/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMapBijective
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison

/-!
# Existence of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private lemma extMk_zero_injective {C : Type*} [Category C] [Abelian C]
    [HasExt C] {A G : C} (I : InjectiveResolution G)
    (f : A ⟶ I.cocomplex.X 0) (hf : f ≫ I.cocomplex.d 0 1 = 0)
    (h : I.extMk f 1 rfl hf = 0) : f = 0 := by
  have h := congrArg I.extEquivCohomologyClass h
  simp only [InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff
    _ _ _ _ _ (-1) (by omega)] at h
  obtain ⟨g, hg⟩ := h
  have hz : g = 0 := by
    apply IsZero.eq_of_tgt
    exact I.cochainComplex.isZero_of_isStrictlyGE 0 (-1) (by omega)
  apply (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp
  simpa [hz] using hg.symm

set_option backward.isDefEq.respectTransparency false in
private lemma represented_resolution {C : Type*} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (E : C ⥤ AddCommGrpCat.{w}) [E.Additive] (A : C)
    (e : ∀ F : C, (A ⟶ F) ≃+ E.obj F)
    (he : ∀ {F G : C} (f : F ⟶ G) (a : A ⟶ F),
      e G (a ≫ f) = E.map f (e F a))
    {G : C} (I : InjectiveResolution G) (q : ℕ) :
    ∃ t : ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology q ≃+
      Abelian.Ext A G q,
      ∀ (f : A ⟶ I.cocomplex.X q) (hf : f ≫ I.cocomplex.d q (q + 1) = 0)
        (z : ((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).cycles q),
        (((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles q) z =
          e (I.cocomplex.X q) f →
        t ((((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ q) z) =
          I.extMk f (q + 1) rfl hf := by
  classical
  have hn (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
    ComplexShape.next_eq' _ rfl
  have hp (n : ℕ) : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' _ rfl
  have hp0 : (ComplexShape.up ℕ).prev 0 = 0 :=
    ComplexShape.prev_eq_self' _ _ (by intro n; simp)
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let S := K.sc' (q - 1) q (q + 1)
  have cycle (z : S.cycles) :
      (e (I.cocomplex.X q)).symm (S.iCycles z) ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (e (I.cocomplex.X (q + 1))).injective
    rw [he, AddEquiv.apply_symm_apply, map_zero]
    change S.g (S.iCycles z) = 0
    rw [← ConcreteCategory.comp_apply, S.iCycles_g]
    rfl
  let k : S.cycles →+ Abelian.Ext A G q :=
    { toFun := fun z ↦ I.extMk ((e _).symm (S.iCycles z)) (q + 1) rfl (cycle z)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [map_add]
        exact (I.add_extMk _ _ _ rfl (cycle x) (cycle y)).symm }
  have val (z : S.cycles) (f : A ⟶ I.cocomplex.X q)
      (hf : f ≫ I.cocomplex.d q (q + 1) = 0) (hz : S.iCycles z = e _ f) :
      k z = I.extMk f (q + 1) rfl hf := by
    dsimp only [k, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    simp only [hz, AddEquiv.symm_apply_apply]
  have kernel (z : S.cycles) : k z = 0 ↔ ∃ x : S.X₁, S.toCycles x = z := by
    cases q with
    | zero =>
      have hS : S.f = 0 := by
        change E.map (I.cocomplex.d 0 0) = 0
        simp
      constructor
      · intro hz
        have hf := extMk_zero_injective I _ (cycle z) hz
        have hz' : z = 0 := by
          apply (AddCommGrpCat.mono_iff_injective (S.iCycles)).mp inferInstance
          have := congrArg (e (I.cocomplex.X 0)) hf
          simpa using this
        exact ⟨0, by simpa using hz'.symm⟩
      · rintro ⟨x, rfl⟩
        have ht : S.toCycles = 0 := by
          rw [← cancel_mono S.iCycles, S.toCycles_i, zero_comp, hS]
        simp [ht]
    | succ n =>
      constructor
      · intro hz
        obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff _ _ rfl (cycle z) n rfl).mp hz
        refine ⟨e (I.cocomplex.X n) g, ?_⟩
        apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
        rw [← ConcreteCategory.comp_apply, S.toCycles_i]
        change E.map (I.cocomplex.d n (n + 1)) (e _ g) = S.iCycles z
        rw [← he, hg, AddEquiv.apply_symm_apply]
      · rintro ⟨x, rfl⟩
        apply (I.extMk_eq_zero_iff _ _ rfl (cycle _) n rfl).mpr
        refine ⟨(e (I.cocomplex.X n)).symm x, ?_⟩
        apply (e (I.cocomplex.X (n + 1))).injective
        rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        rw [← ConcreteCategory.comp_apply, S.toCycles_i]
        rfl
  have hk : S.toCycles ≫ AddCommGrpCat.ofHom k = 0 := by
    ext x
    exact (kernel (S.toCycles x)).mpr ⟨x, rfl⟩
  let t : S.homology ⟶ AddCommGrpCat.of (Abelian.Ext A G q) :=
    S.descHomology (AddCommGrpCat.ofHom k) hk
  have ht (z : S.cycles) : t (S.homologyπ z) = k z := by
    change (S.homologyπ ≫ t) z = k z
    rw [S.π_descHomology]
    rfl
  have hs : Function.Surjective t := by
    intro a
    obtain ⟨f, hf, rfl⟩ := I.extMk_surjective a (q + 1) rfl
    have hcycle : S.g (e _ f) = 0 := by
      change E.map (I.cocomplex.d q (q + 1)) (e _ f) = 0
      rw [← he, hf, map_zero]
    let z : S.cycles := S.abCyclesIso.inv ⟨e _ f, hcycle⟩
    refine ⟨S.homologyπ z, (ht z).trans (val z f hf ?_)⟩
    exact S.abCyclesIso_inv_apply_iCycles _
  have hi : Function.Injective t := by
    apply (AddMonoidHom.ker_eq_bot_iff t.hom).mp
    rw [eq_bot_iff]
    intro a ha
    change a = 0
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance a
    obtain ⟨x, rfl⟩ := (kernel z).mp ((ht z).symm.trans ha)
    rw [← ConcreteCategory.comp_apply, S.toCycles_comp_homologyπ]
    rfl
  have hprev : (ComplexShape.up ℕ).prev q = q - 1 := by
    cases q with
    | zero => exact hp0
    | succ n => simp [hp]
  let c := K.cyclesIsoSc' (q - 1) q (q + 1) hprev (hn q)
  let d := K.homologyIsoSc' (q - 1) q (q + 1) hprev (hn q)
  refine ⟨d.addCommGroupIsoToAddEquiv.trans (AddEquiv.ofBijective t.hom ⟨hi, hs⟩), ?_⟩
  intro f hf z hz
  change t (d.hom (K.homologyπ q z)) = _
  have hd : d.hom (K.homologyπ q z) = S.homologyπ (c.hom z) := by
    change (K.homologyπ q ≫ d.hom) z = (c.hom ≫ S.homologyπ) z
    rw [K.π_homologyIsoSc'_hom]
  rw [hd, ht]
  apply val (c.hom z) f hf
  change (c.hom ≫ S.iCycles) z = e _ f
  rw [K.cyclesIsoSc'_hom_iCycles]
  exact hz

/-- Existence of comparisons normalized by the Hom-to-sections adjunction.
Source: Stacks Project, Tag 0A50 (sections of resolutions), Tag 03F3 (localization).
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-data)

Proof: For the constant integer sheaf on X, the constant-sheaf adjunction and
 evaluation at 1 identify Hom into each term of I with global sections. These
 additive equivalences commute with differentials. Thus the Hom-complex computation
 of Ext identifies its cocycle classes with homology of the global section complex.
 Map cycles by `I.extMk`; its kernel is the boundaries and it is surjective,
 so descent through the homology cokernel gives the global additive equivalence
 with the prescribed cocycle value. For every open W, replace
 the constant sheaf by the free abelian sheaf on the representable W. The
 sheafification/free/Yoneda adjunction gives `sectionsEquiv` in each degree,
 naturally in the resolution term, and hence again an equivalence of cocycle
 classes. Compose the resulting homology-to-Ext equivalence with the independently
 constructed `etaleOpenObjectCohomologyMap`, which is bijective by localization:
 inverse image along W preserves injectives, since exact extension by zero is
 its left adjoint. The composite has the stated open cocycle value. This
 constructs all opens from the same adjunction, with no compatibility claimed
 here. In degree zero use the kernel of the first differential; in positive
 degrees quotient cycles by boundaries. Empty opens and zero sheaves give zero
 groups and the same construction. -/
theorem exists_resolutionSection_canonical_comparison {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G) :
    Nonempty (ResolutionSectionCanonicalComparison G I) := by
  classical
  let e (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ F).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have he {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (f : F ⟶ F') (a : EtaleOpenComparison.integerSheaf X ⟶ F) :
      e F' (a ≫ f) = (etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).map f (e F a) := by
    dsimp only [e, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  have hg (q : ℕ) := represented_resolution
    (etaleSectionFunctor (Scheme.Etale.mk (𝟙 X)))
    (EtaleOpenComparison.integerSheaf X) e (fun f a ↦ he f a) I q
  have ho (W : X.Opens) (q : ℕ) := represented_resolution
    (etaleSectionFunctor (Scheme.Etale.mk W.ι)) ((etaleOpenFreeSheaf X).obj
      (Scheme.Etale.mk W.ι))
    (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk W.ι))
    (fun f a ↦ EtaleOpenComparison.sectionsEquiv_naturality _ _ f a) I q
  let og (W : X.Opens) (q : ℕ) := AddEquiv.ofBijective
    (etaleOpenObjectCohomologyMap G q W).hom
      (etaleOpenObjectCohomologyMap_bijective G q W)
  refine ⟨{ globalEquiv := fun q ↦ (hg q).choose
            openEquiv := fun W q ↦ (ho W q).choose.trans (og W q)
            global_cocycle := ?_
            open_cocycle := ?_ }⟩
  · intro q f hf z hz
    exact (hg q).choose_spec f hf z hz
  · intro W q f hf z hz
    change og W q ((ho W q).choose _) = _
    rw [(ho W q).choose_spec f hf z hz]
    rfl

end AlgebraicGeometry.Etale
