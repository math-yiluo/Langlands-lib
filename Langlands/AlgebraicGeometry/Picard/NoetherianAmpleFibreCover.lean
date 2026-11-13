import Langlands.AlgebraicGeometry.Picard.AmpleFibreCover

/-! # Ample-fibre covers of abelian schemes over noetherian affine bases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Over a noetherian affine base, every point lies in a constructible set which is the
image of the fibre-ample locus of a line bundle on a base change of the abelian scheme
to an affine scheme of finite type. -/
theorem exists_ampleFibre_piece {R₀ : CommRingCat.{u}} [IsNoetherianRing R₀]
    (A₀ : AbelianScheme (Spec R₀)) (x : Spec R₀) :
    ∃ (T W : Scheme.{u}) (g : T ⟶ Spec R₀) (a : W ⟶ A₀.X.left) (q : W ⟶ T)
      (L : LineBundle W), IsPullback a q A₀.X.hom g ∧ IsAffine T ∧
      IsConstructible (g '' ampleFibreLocus q L) ∧ x ∈ g '' ampleFibreLocus q L := by
  let K := x.asIdeal.ResidueField
  let φK : Spec (CommRingCat.of K) ⟶ Spec R₀ := Spec.map (CommRingCat.ofHom (algebraMap R₀ K))
  let AK := (AbelianScheme.baseChange φK).obj A₀
  obtain ⟨LK, hLK⟩ := GroupScheme.fieldAmpleExistence K AK.toGrp
    inferInstance inferInstance inferInstance
  obtain ⟨B, hBfg, -, M₀, hM₀, hc⟩ := lineBundleSubalgebraDescent (A₀ := R₀) (A := K)
    A₀.X.hom (pullback.fst A₀.X.hom φK) (pullback.snd A₀.X.hom φK)
    (IsPullback.of_hasPullback _ _) LK.obj LK.property ∅
  let g : Spec (CommRingCat.of B) ⟶ Spec R₀ := Spec.map (CommRingCat.ofHom (algebraMap R₀ B))
  let κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B K))
  have hκ : κ ≫ g = φK := by
    dsimp only [κ, g, φK]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let W := pullback A₀.X.hom g
  let L : LineBundle W := ⟨M₀, hM₀⟩
  have hw : pullback.fst A₀.X.hom φK ≫ A₀.X.hom = (pullback.snd A₀.X.hom φK ≫ κ) ≫ g := by
    rw [Category.assoc, hκ, pullback.condition]
  let c : AK.X.left ⟶ W := pullback.lift _ _ hw
  have hc₁ : c ≫ pullback.fst A₀.X.hom g = pullback.fst A₀.X.hom φK := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd A₀.X.hom g = pullback.snd A₀.X.hom φK ≫ κ :=
    pullback.lift_snd _ _ _
  obtain ⟨e⟩ := hc c hc₁ hc₂
  have hsq : IsPullback c (pullback.snd A₀.X.hom φK) (pullback.snd A₀.X.hom g) κ := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback A₀.X.hom g)
    rw [hc₁, hκ]
    exact IsPullback.of_hasPullback _ _
  have hBfin : Algebra.FiniteType R₀ B := (Subalgebra.fg_iff_finiteType B).mp hBfg
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ B
  let t : Spec (CommRingCat.of B) := κ (IsLocalRing.closedPoint K)
  have ht : t ∈ ampleFibreLocus (pullback.snd A₀.X.hom g) L := by
    rw [← mem_ampleFibreLocus_iff_of_isPullback hsq]
    have hL' : ((LineBundle.pullback c).obj L).IsAmple := hLK.of_iso e.symm
    have : IsAffineHom ((pullback.snd A₀.X.hom φK).fiberι (IsLocalRing.closedPoint K)) := by
      change IsAffineHom (pullback.fst (pullback.snd A₀.X.hom φK)
        ((Spec (CommRingCat.of K)).fromSpecResidueField (IsLocalRing.closedPoint K)))
      exact MorphismProperty.pullback_fst _ _ inferInstance
    exact hL'.pullback_of_isAffineHom _
  have hgt : g t = x := by
    change PrimeSpectrum.comap (algebraMap R₀ B)
      (PrimeSpectrum.comap (algebraMap B K) (IsLocalRing.closedPoint K)) = x
    ext1
    change Ideal.comap (algebraMap R₀ B) (Ideal.comap (algebraMap B K)
      (IsLocalRing.maximalIdeal K)) = x.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsLocalRing.maximalIdeal_eq_bot,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  refine ⟨Spec (CommRingCat.of B), W, g, pullback.fst _ _, pullback.snd _ _, L,
    IsPullback.of_hasPullback _ _, inferInstance, ?_, ⟨t, ht, hgt⟩⟩
  have hopen : IsOpen (ampleFibreLocus (pullback.snd A₀.X.hom g) L) :=
    isOpen_ampleFibreLocus _ L
  have hcons : IsConstructible (ampleFibreLocus (pullback.snd A₀.X.hom g) L) :=
    (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hopen
  have hfp : (algebraMap R₀ B).FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr hBfin)
  exact PrimeSpectrum.isConstructible_comap_image hfp hcons

/-- In a spectral space, a cover by constructible sets has a finite subcover: constructible
sets are open in the constructible topology, which is compact. -/
theorem exists_finset_cover_of_isConstructible {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [QuasiSober X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    {ι : Type*} (C : ι → Set X) (hC : ∀ i, IsConstructible (C i))
    (hcov : ∀ x, ∃ i, x ∈ C i) : ∃ s : Finset ι, ∀ x, ∃ i ∈ s, x ∈ C i := by
  let D : ι → Set (WithConstructibleTopology X) := fun i ↦ WithTopology.ofTopology ⁻¹' C i
  have hD : ∀ i, IsOpen (D i) := by
    intro i
    rw [WithConstructibleTopology.isOpen_iff]
    change IsOpen[constructibleTopology X] (C i)
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem (hC i)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover D hD (by
    intro y _
    obtain ⟨i, hi⟩ := hcov (WithTopology.ofTopology y)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨s, fun x ↦ ?_⟩
  have hx := hs (Set.mem_univ (WithTopology.toTopology (constructibleTopology X) x))
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, hx⟩

/-- An abelian scheme over a noetherian affine base has an ample-fibre cover of the whole
base. -/
theorem noetherian_hasAmpleFibreCover {R₀ : CommRingCat.{u}} [IsNoetherianRing R₀]
    (A₀ : AbelianScheme (Spec R₀)) : HasAmpleFibreCover A₀.X.hom Set.univ := by
  choose T W g a q L hpb haff hcons hmem using exists_ampleFibre_piece A₀
  obtain ⟨s, hs⟩ := exists_finset_cover_of_isConstructible
    (fun x ↦ g x '' ampleFibreLocus (q x) (L x)) hcons (fun x ↦ ⟨x, hmem x⟩)
  refine ⟨s, inferInstance, fun i ↦ T i, fun i ↦ W i, fun i ↦ g i, fun i ↦ a i,
    fun i ↦ q i, fun i ↦ L i, fun i ↦ hpb i, fun i ↦ haff i, fun _ ↦ Set.subset_univ _, ?_⟩
  intro y _
  obtain ⟨i, hi, t, ht, rfl⟩ := hs y
  exact ⟨⟨i, hi⟩, t, rfl, ht⟩

end Langlands.AlgebraicGeometry.Picard
