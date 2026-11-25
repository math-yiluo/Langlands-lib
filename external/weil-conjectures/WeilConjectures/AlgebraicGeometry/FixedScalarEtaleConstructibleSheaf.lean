/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.FixedScalarEtaleModel
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentation
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-! # Constructibility under the etale scalar presentation

Source: Stacks Tags 03CY, 03RW and 095E (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem moduleLocalFiniteDatum
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    localFinite X.smallEtaleTopology A F ↔
      ∃ d : LocallyConstantDatum F, ∀ i : d.cover.I₀,
        ∃ M : ModuleCat.{u + 1} A, Module.Finite A M ∧
          Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} A)).obj M) := by
  classical
  rw [localFinite_iff_sieve X.smallEtaleTopology A F]
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let S := finiteModelSieve X.smallEtaleTopology A F T
  have hmem : finiteModelSieve X.smallEtaleTopology A F (⊤_ X.Etale) ∈
      X.smallEtaleTopology (⊤_ X.Etale) ↔ S ∈ X.smallEtaleTopology T := by
    let e := (Scheme.Etale.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
    change _ ↔ (finiteModelSieve X.smallEtaleTopology A F (⊤_ X.Etale)).pullback
      e.hom ∈ X.smallEtaleTopology T
    exact GrothendieckTopology.pullback_mem_iff_of_isIso.symm
  rw [hmem]
  constructor
  · intro hS
    have hx := (Scheme.mem_smallEtaleTopology_iff S).mp hS
    choose V g hg hx using hx
    have hc : ∀ x : X, ∃ i y, (V i).hom y = x := by
      intro x
      obtain ⟨y, hy⟩ := hx x
      refine ⟨x, y, ?_⟩
      have hw : (g x).left = (V x).hom :=
        (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g x))
      change (g x).left y = x at hy
      exact (congrArg (fun f : (V x).left ⟶ X ↦ f y) hw.symm).trans hy
    let C : Scheme.Cover.{u} Scheme.etalePrecoverage X :=
      Scheme.Cover.mkOfCovers X (fun x ↦ (V x).left) (fun x ↦ (V x).hom) hc
    have hm (i : C.I₀) : ∃ M : ModuleCat.{u + 1} A, Module.Finite A M ∧
        Nonempty (F.over (C.etalePrecoverageToEtale i) ≅
          (constantSheaf (X.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj M) := by
      obtain ⟨M, hM, ⟨e⟩⟩ := hg i
      have he := e ≪≫ (X.smallEtaleTopology.overPullbackConstantSheafIso
        (ModuleCat.{u + 1} A) (V i)).app M
      exact ⟨M, hM, ⟨he⟩⟩
    refine ⟨⟨C, fun i ↦ ?_⟩, hm⟩
    obtain ⟨M, _, ⟨e⟩⟩ := hm i
    exact Sheaf.isConstant_of_iso _ e
  · rintro ⟨d, hd⟩
    let V := d.cover.etalePrecoverageToEtale
    let t (i : d.cover.I₀) : V i ⟶ T := MorphismProperty.Over.homMk (d.cover.f i)
    have hcover : Sieve.ofArrows V t ∈ X.smallEtaleTopology T := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff t).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, y, hy⟩ := d.cover.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, hy⟩⟩
    apply X.smallEtaleTopology.superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro U f ⟨i⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i
    let := hM
    exact ⟨M, hM, ⟨e ≪≫
      ((X.smallEtaleTopology.overPullbackConstantSheafIso (ModuleCat.{u + 1} A) (V i)).app M).symm⟩⟩

private theorem localFinite_iff_finiteLocallyConstant (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    localFinite Y.smallEtaleTopology A F ↔ IsFiniteLocallyConstantSheaf F := by
  classical
  rw [moduleLocalFiniteDatum]
  constructor
  · rintro ⟨d, hd⟩
    refine { toIsLocallyConstantSheaf := ⟨⟨d⟩⟩, toIsFiniteSheaf := ?_ }
    constructor
    intro Ω _ _ s
    have : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @Etale))
    obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
    have : Etale (d.cover.f i) := d.cover.map_prop i
    obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (d.cover.f i) s x hx
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i
    have hgen := ((ModuleCat.isFinitelyGenerated_iff M).mpr hM).of_iso
      (constantValueStalkIso F (d.cover.etalePrecoverageToEtale i) M e t).symm
    change ConcreteCategory.IsFinitelyGenerated
      (((pointSmallEtale (t ≫ d.cover.f i)).sheafFiber).obj F) at hgen
    simpa only [ht] using hgen
  · intro hF
    let := hF
    obtain ⟨d₀⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    let 𝒰 : Cover.{u} etalePrecoverage Y :=
      { I₀ := { i : d₀.cover.I₀ // Nonempty (d₀.cover.X i) }
        X i := d₀.cover.X i.1
        f i := d₀.cover.f i.1
        mem₀ := by
          refine (presieve₀_mem_precoverage_iff _).mpr
            ⟨fun y ↦ ?_, fun i ↦ d₀.cover.map_prop i.1⟩
          obtain ⟨i, x, hx⟩ := d₀.cover.exists_eq y
          exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
    let d : LocallyConstantDatum F := ⟨𝒰, fun i ↦ d₀.isConstant i.1⟩
    refine ⟨d, fun i ↦ ?_⟩
    have := d.isConstant i
    obtain ⟨M, ⟨e⟩⟩ := (F.over (d.cover.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
    let U := d.cover.etalePrecoverageToEtale i
    have : Nonempty U.left := i.2
    let x : U.left := Classical.arbitrary _
    let Ω := SeparableClosure (U.left.residueField x)
    let s : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
      ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
    have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (F := F) Ω (s ≫ U.hom)).of_iso (constantValueStalkIso F U M e.symm s)
    exact ⟨M, (ModuleCat.isFinitelyGenerated_iff M).mp hgen, ⟨e.symm⟩⟩

private theorem coefficientConstructible_realization (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (smallModelComparisonEtaleTopology.{u, u} X) A)) :
    IsCoefficientConstructibleEtaleModule.{u, u} X A F ↔
      IsConstructibleSheaf ((ProEtale.finiteComparisonEtaleModelRealization X A).obj F) := by
  have hglobal := ProEtale.coefficient_etale_global X A F
  change IsCoefficientConstructibleEtaleModule.{u, u} X A F ↔ _ at hglobal
  rw [hglobal]
  change (∃ S : Stratification X, _) ↔ IsConstructibleSheaf _
  rw [show IsConstructibleSheaf
      ((ProEtale.finiteComparisonEtaleModelRealization X A).obj F) ↔
      ∃ S : Stratification X, ∀ i, IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
          ((ProEtale.finiteComparisonEtaleModelRealization X A).obj F)) from
      ⟨fun h ↦ h.exists_stratification, fun h ↦ ⟨h⟩⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro i
  rw [ProEtale.etaleSites_localFinite]
  let e := (ProEtale.etaleSitePullbackSquare (S.immersion i) A).app
    ((coefficientModelFixedScalars _ A).obj F)
  exact (show localFinite _ A _ ↔ localFinite _ A _ from
    ⟨localFinite_iso _ A e, localFinite_iso _ A e.symm⟩).trans
      (localFinite_iff_finiteLocallyConstant _ A _)

/-- The explicit scalar and small-site equivalence preserves and reflects the module
constructibility condition. No finiteness of the underlying coefficient set is required.
Source: Stacks Modules on Sites Tag 03CY; Etale Cohomology Tags 03RW and 095E
(auxiliary; not a blueprint node).

Proof: apply etale_noetherian_global_constructibility to the coefficient module. The
resulting finite stratification is a stratification on the original scheme with exactly
the same immersed domains. Restriction to each stratum commutes with the site equivalence:
the corresponding direct images are precomposition along the same base change, and taking
adjoint mates gives the inverse-image comparison. The scalar restriction identifies the
underlying module-valued sheaves and their constant module models. Precomposition by the
site equivalence sends and reflects covering sieves; the induced equivalences of slice
sites identify the restrictions and the sheafified constant module objects. Thus the local
finite-module condition is unchanged. On the original etale site, locally constant sheaves
with finitely generated stalks admit local constant models with finitely generated values:
start with a constant trivialization, use a geometric point in each nonempty member to
identify its value with a stalk, and refine by these members. Empty members can be removed;
on the empty scheme the empty cover suffices. Conversely a finite constant module has
finitely generated stalks and the property is local. These two operations identify precisely
IsConstructibleSheaf on the same stratification. The ring is Noetherian, so finite generation
and finite presentation agree; neither argument asks that the ring be finite as a set. -/
theorem fixedScalarEtale_constructible_sheaf (X : Scheme.{u}) [IsNoetherian X]
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    IsCoefficientConstructibleEtaleModule.{u, u} X k
      ((fixedScalarEtaleSheafEquivalence X k).functor.obj F) ↔ IsConstructibleSheaf F := by
  let E := fixedScalarEtaleSheafEquivalence X k
  let r : E.inverse ≅ ProEtale.finiteComparisonEtaleModelRealization X k := by
    unfold E fixedScalarEtaleSheafEquivalence ProEtale.finiteComparisonEtaleModelRealization
    exact Functor.isoWhiskerRight (CategoryTheory.restrictionIso _ k) _
  let e : (ProEtale.finiteComparisonEtaleModelRealization X k).obj
      (E.functor.obj F) ≅ F :=
    (r.app (E.functor.obj F)).symm ≪≫ E.unitIso.symm.app F
  exact (coefficientConstructible_realization X k _).trans
    ⟨fun h ↦ let := h; IsConstructibleSheaf.of_iso e,
      fun h ↦ by
        have : IsConstructibleSheaf F := h
        exact IsConstructibleSheaf.of_iso e.symm⟩

end AlgebraicGeometry.Scheme
