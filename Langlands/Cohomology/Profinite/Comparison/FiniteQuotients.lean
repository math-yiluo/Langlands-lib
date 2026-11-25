import Langlands.Cohomology.Profinite.Comparison.Discrete
import Langlands.Cohomology.Profinite.Comparison.FilteredHomology
import Langlands.Cohomology.Profinite.OpenNormal
import Langlands.Cohomology.Tate.PGroupTateVanishingProof
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Comparison with the colimit over finite quotients

For an open normal subgroup `U` of `G`, a cochain of `G/U` with values in `A^U` gives, by
composing with the projection `Gⁿ → (G/U)ⁿ`, a locally constant cochain of `G` with values in `A`.
These inflation maps form a cocone on the Library's diagram
`Langlands.Continuous.finiteQuotientCochainDiagram A` of finite-quotient cochain complexes. For a
profinite group it is a colimit cocone in every degree: every locally constant cochain factors
through some finite quotient and takes values in some `A^U`, and the maps from each stage are
injective. Hence `isoFiniteQuotientCohomology A n : cohomology A n ≅ finiteQuotientCohomology A n`,
the Library's colimit of the cohomology of the finite quotients (Serre's definition of the
cohomology of a profinite group).

Consequences: every class is inflated from a finite quotient (`exists_inflation_eq`), and in
positive degree it is killed by the order of that quotient (`exists_card_smul_eq_zero`), so
`Hⁿ(G, A)` is torsion for `n ≥ 1` (`isTorsion_cohomology`).
-/

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits groupCohomology Langlands.Continuous

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

theorem isLocallyConstant_comp_quotient_mk [IsTopologicalGroup G] (U : OpenNormalSubgroup G)
    {n : ℕ} {X : Type*} (y : (Fin n → G ⧸ U.toSubgroup) → X) :
    IsLocallyConstant fun g : Fin n → G => y fun i => (g i : G ⧸ U.toSubgroup) :=
  (IsLocallyConstant.of_discrete y).comp_continuous
    (continuous_pi fun i => continuous_quot_mk.comp (continuous_apply i))

namespace OpenNormalSubgroup

theorem exists_le_of_finite {ι : Type*} [Finite ι] (V : ι → OpenNormalSubgroup G) :
    ∃ W : OpenNormalSubgroup G, ∀ i, W ≤ V i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨W, hW⟩ := Finset.exists_le (α := (OpenNormalSubgroup G)ᵒᵈ)
    (Finset.univ.image fun i => OrderDual.toDual (V i))
  exact ⟨OrderDual.ofDual W, fun i => hW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

end OpenNormalSubgroup

/-- The order of a finite group kills its cohomology in positive degree (from the Library's
`Langlands.Tate.PGroupVanishing.card_smul_eq_zero` for Tate cohomology). -/
theorem card_smul_groupCohomology {Q : Type u} [Group Q] [Fintype Q] (M : Rep.{u} k Q) {n : ℕ}
    (hn : n ≠ 0) (x : groupCohomology M n) : Fintype.card Q • x = 0 := by
  have : NeZero n := ⟨hn⟩
  let e := (TateCohomology.isoGroupCohomology (R := k) (G := Q) n).app M
  obtain ⟨t, rfl⟩ : ∃ t, e.hom.hom t = x := ⟨e.inv.hom x, Iso.inv_hom_id_apply e x⟩
  have h := congrArg e.hom.hom (Langlands.Tate.PGroupVanishing.card_smul_eq_zero M n t)
  rw [map_nsmul, map_zero] at h
  exact h

section Level

variable (A : Rep.{u} k G)

/-- The transition map `Hⁿ(G/U, A^U) ⟶ Hⁿ(G/V, A^V)` for `V ≤ U`: the Library's inflation
`Langlands.Continuous.finiteInflation`. -/
noncomputable abbrev transition {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    groupCohomology (A.quotientToInvariants U.toSubgroup) n ⟶
      groupCohomology (A.quotientToInvariants V.toSubgroup) n :=
  finiteInflation A n h

variable [IsTopologicalGroup G] [IsSmoothRep A]

/-- Inflation of cochains from the finite quotient `G/U` (cochains of `G/U` with values in
`A^U`) to Mathlib's inhomogeneous cochains of `G`. -/
noncomputable abbrev infCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants U.toSubgroup) ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (QuotientGroup.mk' U.toSubgroup)
    (Rep.ofHom (A.ρ.quotientToInvariants_lift U.toSubgroup))

noncomputable def inflationCochainsX (U : OpenNormalSubgroup G) (n : ℕ) :
    (inhomogeneousCochains (A.quotientToInvariants U.toSubgroup)).X n ⟶
      (cochains A).X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict (locallyConstantCochains A n)
    ((infCochains A U).f n).hom
    fun x => isLocallyConstant_comp_quotient_mk U fun q => (x q : A)

theorem inflationCochainsX_comp_ι (U : OpenNormalSubgroup G) (n : ℕ) :
    inflationCochainsX A U n ≫ (cochainsι A).f n = (infCochains A U).f n :=
  rfl

/-- Inflation of cochains from the finite quotient `G/U` into the locally constant cochains. -/
noncomputable def inflationCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants U.toSubgroup) ⟶ cochains A where
  f n := inflationCochainsX A U n
  comm' i j _ := by
    rw [← cancel_mono ((cochainsι A).f j), Category.assoc, Category.assoc,
      ← (cochainsι A).comm i j, ← Category.assoc, inflationCochainsX_comp_ι,
      inflationCochainsX_comp_ι, HomologicalComplex.Hom.comm]

@[simp]
theorem inflationCochains_f_hom_apply (U : OpenNormalSubgroup G) (n : ℕ)
    (x : (Fin n → G ⧸ U.toSubgroup) →
      Representation.invariants (A.ρ.comp U.toSubgroup.subtype)) (g : Fin n → G) :
    ((cochainsι A).f n).hom (((inflationCochains A U).f n).hom x) g =
      (x fun i => (g i : G ⧸ U.toSubgroup) : A) :=
  rfl

theorem inflationCochains_comp_cochainsι (U : OpenNormalSubgroup G) :
    inflationCochains A U ≫ cochainsι A = infCochains A U := by
  ext n : 1
  exact inflationCochainsX_comp_ι A U n

/-- Inflation `Hⁿ(G/U, A^U) ⟶ Hⁿ(G, A)` from a finite quotient. -/
noncomputable def inflation (U : OpenNormalSubgroup G) (n : ℕ) :
    groupCohomology (A.quotientToInvariants U.toSubgroup) n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (inflationCochains A U) n

theorem inflation_comp_toGroupCohomology (U : OpenNormalSubgroup G) (n : ℕ) :
    inflation A U n ≫ toGroupCohomology A n =
      (groupCohomology.infNatTrans k U.toSubgroup n).app A := by
  unfold inflation toGroupCohomology
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [inflationCochains_comp_cochainsι]
  rfl

theorem finiteQuotientCochainDiagram_map_comp_inflationCochains
    {U V : FiniteQuotientIndex (G := G)} (f : U ⟶ V) :
    (finiteQuotientCochainDiagram A).map f ≫ inflationCochains A (OrderDual.ofDual V) =
      inflationCochains A (OrderDual.ofDual U) := by
  ext n x : 3
  apply Subtype.ext
  rfl

theorem transition_comp_inflation {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    transition A h n ≫ inflation A V n = inflation A U n := by
  unfold transition finiteInflation inflation
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  congr 1

/-- The inflation maps, as a cocone on the Library's diagram of finite-quotient cochains. -/
@[simps]
noncomputable def inflationCochainsCocone : Cocone (finiteQuotientCochainDiagram A) where
  pt := cochains A
  ι :=
    { app U := inflationCochains A (OrderDual.ofDual U)
      naturality _ _ f :=
        (finiteQuotientCochainDiagram_map_comp_inflationCochains A f).trans
          (Category.comp_id _).symm }

/-- The inflation maps in degree `n`, as a cocone on `finiteQuotientDiagram A n`. -/
noncomputable abbrev inflationCocone (n : ℕ) : Cocone (finiteQuotientDiagram A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone
    (inflationCochainsCocone A)

theorem inflationCocone_ι_app (n : ℕ) (U : FiniteQuotientIndex (G := G)) :
    (inflationCocone A n).ι.app U = inflation A (OrderDual.ofDual U) n :=
  rfl

theorem inflationCochains_f_injective (U : OpenNormalSubgroup G) (n : ℕ) :
    Function.Injective ((inflationCochains A U).f n).hom := by
  intro x y hxy
  apply inhomogeneousCochains.ext
  intro q
  have h : ((x fun i => (((q i).out : G) : G ⧸ U.toSubgroup)) : A) =
      ((y fun i => (((q i).out : G) : G ⧸ U.toSubgroup)) : A) :=
    congrArg (fun c => ((cochainsι A).f n).hom c fun i => (q i).out) hxy
  simp only [QuotientGroup.out_eq'] at h
  exact Subtype.ext h

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_inflationCochains_f_eq (n : ℕ) (x : (cochains A).X n) :
    ∃ (U : OpenNormalSubgroup G)
      (y : (inhomogeneousCochains (A.quotientToInvariants U.toSubgroup)).X n),
      ((inflationCochains A U).f n).hom y = x := by
  have hx : IsLocallyConstant (((cochainsι A).f n).hom x : (Fin n → G) → A) :=
    (show locallyConstantCochains A n from x).2
  obtain ⟨U₁, g, hg⟩ := exists_openNormalSubgroup_factor_fin_of_isLocallyConstant hx
  have hV : ∀ p, ∃ V : OpenNormalSubgroup G,
      g p ∈ Representation.invariants (A.ρ.comp V.toSubgroup.subtype) := fun p =>
    (isSmoothRep_iff_forall_exists_openNormalSubgroup A).1 ‹_› (g p)
  choose V hV using hV
  obtain ⟨W, hW⟩ := OpenNormalSubgroup.exists_le_of_finite V
  have hU₁ : W ⊓ U₁ ≤ U₁ := inf_le_right
  refine ⟨W ⊓ U₁, fun q => ⟨g fun i => quotientTransition hU₁ (q i),
    invariants_comp_subtype_antitone A.ρ (fun _ hz => (inf_le_left.trans (hW _)) hz) (hV _)⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsι A).f n)).1 inferInstance
  funext h
  rw [inflationCochains_f_hom_apply]
  exact (congrFun hg h).symm

theorem inflationCochainsCocone_surj (n : ℕ) (x : (inflationCochainsCocone A).pt.X n) :
    ∃ (U : FiniteQuotientIndex (G := G)) (y : ((finiteQuotientCochainDiagram A).obj U).X n),
      (((inflationCochainsCocone A).ι.app U).f n).hom y = x := by
  obtain ⟨U, y, hy⟩ := exists_inflationCochains_f_eq A n x
  exact ⟨OrderDual.toDual U, y, hy⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inflationCochainsCocone_inj (n : ℕ) (U : FiniteQuotientIndex (G := G))
    (y : ((finiteQuotientCochainDiagram A).obj U).X n)
    (hy : (((inflationCochainsCocone A).ι.app U).f n).hom y = 0) :
    ∃ (V : FiniteQuotientIndex (G := G)) (f : U ⟶ V),
      (((finiteQuotientCochainDiagram A).map f).f n).hom y = 0 := by
  refine ⟨U, 𝟙 U, ?_⟩
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact inflationCochains_f_injective A (OrderDual.ofDual U) n (hy.trans (map_zero _).symm)

/-- Every class is inflated from a finite quotient. -/
theorem exists_inflation_eq (n : ℕ) (x : cohomology A n) :
    ∃ (U : OpenNormalSubgroup G)
      (y : groupCohomology (A.quotientToInvariants U.toSubgroup) n),
      (inflation A U n).hom y = x := by
  obtain ⟨U, y, hy⟩ := exists_homologyMap_eq_of_cocone (inflationCochainsCocone A) n
    (inflationCochainsCocone_surj A n) (inflationCochainsCocone_inj A _) x
  exact ⟨OrderDual.ofDual U, y, hy⟩

/-- A class of a finite quotient that inflates to zero already vanishes on a smaller quotient. -/
theorem exists_transition_eq_zero (n : ℕ) (U : OpenNormalSubgroup G)
    (y : groupCohomology (A.quotientToInvariants U.toSubgroup) n)
    (hy : (inflation A U n).hom y = 0) :
    ∃ (V : OpenNormalSubgroup G) (h : V ≤ U), (transition A h n).hom y = 0 := by
  obtain ⟨V, f, hf⟩ := exists_homologyMap_map_eq_zero_of_cocone (inflationCochainsCocone A) n
    (inflationCochainsCocone_surj A _) (inflationCochainsCocone_inj A n)
    (OrderDual.toDual U) y hy
  exact ⟨OrderDual.ofDual V, leOfHom f, hf⟩

/-- The inflation maps make `Hⁿ(G, A)` the colimit of the cohomology of the finite quotients. -/
noncomputable def isColimitInflationCocone (n : ℕ) : IsColimit (inflationCocone A n) :=
  isColimitHomologyMapCocone (inflationCochainsCocone A) n (inflationCochainsCocone_surj A)
    (inflationCochainsCocone_inj A)

/-- The comparison with the Library's `Langlands.Continuous.finiteQuotientCohomology`: the
cohomology of a profinite group with coefficients in a smooth module is the colimit of the
cohomology of its finite quotients. -/
noncomputable def isoFiniteQuotientCohomology (n : ℕ) :
    cohomology A n ≅ finiteQuotientCohomology A n :=
  (isColimitInflationCocone A n).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
theorem inflation_comp_isoFiniteQuotientCohomology_hom (U : OpenNormalSubgroup G) (n : ℕ) :
    inflation A U n ≫ (isoFiniteQuotientCohomology A n).hom = finiteStageToColimit A U n :=
  (isColimitInflationCocone A n).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (OrderDual.toDual U)

/-- In positive degree every class is killed by the order of a finite quotient. -/
theorem exists_card_smul_eq_zero {n : ℕ} (hn : n ≠ 0) (x : cohomology A n) :
    ∃ U : OpenNormalSubgroup G, Nat.card (G ⧸ U.toSubgroup) • x = 0 := by
  obtain ⟨U, y, rfl⟩ := exists_inflation_eq A n x
  have := Fintype.ofFinite (G ⧸ U.toSubgroup)
  refine ⟨U, ?_⟩
  rw [Nat.card_eq_fintype_card, ← map_nsmul, card_smul_groupCohomology _ hn y, map_zero]

/-- The cohomology of a profinite group is torsion in positive degree. -/
theorem isTorsion_cohomology {n : ℕ} (hn : 1 ≤ n) : IsAddTorsion (cohomology A n) :=
  fun x => by
    obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A (Nat.one_le_iff_ne_zero.1 hn) x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨_, Nat.card_pos, hU⟩

end Level

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

universe u

section TrivialGroup

/-- The positive-degree cohomology of a trivial group vanishes. -/
theorem subsingleton_cohomology_of_subsingleton_group {k H : Type u} [CommRing k] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [Subsingleton H] (A : Rep.{u} k H) [IsSmoothRep A]
    {n : ℕ} (hn : n ≠ 0) : Subsingleton (cohomology A n) := by
  suffices h : ∀ x : cohomology A n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A hn x
  have : Nat.card (H ⧸ U.toSubgroup) = 1 := Nat.card_unique
  rwa [this, one_smul] at hU

end TrivialGroup

end Langlands.ProfiniteCohomology
