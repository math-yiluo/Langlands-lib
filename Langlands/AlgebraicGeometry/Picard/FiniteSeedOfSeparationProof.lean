import Langlands.AlgebraicGeometry.Picard.FiniteSeedOfSeparationStatement
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.LinearSystem.DualNumberPoints
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

/-! # Finite section seeds from pointwise separation on a Noetherian scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.AlgebraicGeometry.LinearSystem

/-- A global section of a line bundle has a local equation near every point: on a
trivializing open `U ∋ x` there is a function `a` such that the section vanishes along a
morphism landing in `U` exactly when `a` pulls back to zero. -/
lemma exists_localEquation {X : Scheme.{u}} (L : LineBundle X) (s : GlobalSections L.obj)
    (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (a : Γ(X, U)),
      ∀ (T : Scheme.{u}) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U),
        VanishesAlong L g s ↔ g.appLE U ⊤ hg a = 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.property x
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (sectionHom L.obj s) ≫ e.hom
  have htop : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have h1 : U.ι.appLE U ⊤ U.ι_preimage_self.ge (U.topIso.hom (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤)))) =
      ψ.app ⊤ (1 : Γ(U.toScheme, ⊤)) := by
    rw [htop]
    exact Iso.hom_inv_id_apply _ _
  refine ⟨U, hxU, U.topIso.hom (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))), fun T g hg ↦ ?_⟩
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg (Set.mem_univ t)
  let g' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  have hgg : g' ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hval : ∀ (h : T ⟶ X) (hh : g' ≫ U.ι = h) (e' : ⊤ ≤ h ⁻¹ᵁ U),
      h.appLE U ⊤ e' (U.topIso.hom (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤)))) =
        g'.appTop (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) := by
    intro h hh e'
    subst hh
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    conv_rhs => rw [← h1]
    change _ = (U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ g'.appLE ⊤ (g' ⁻¹ᵁ ⊤) le_rfl) _
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [VanishesAlong, pullbackSection_eq_zero_iff, hval g hgg hg]
  calc (Scheme.Modules.pullback g).map (sectionHom L.obj s) = 0
      ↔ (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullback U.ι).map (sectionHom L.obj s)) = 0 := by
        rw [pullback_map_comp_eq_zero_iff, hgg]
    _ ↔ (Scheme.Modules.pullback g').map
          ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom L.obj s)) = 0 :=
        (map_eq_zero_iff_of_natIso (Functor.isoWhiskerRight
          (Scheme.Modules.restrictFunctorIsoPullback U.ι) (Scheme.Modules.pullback g')) _).symm
    _ ↔ (Scheme.Modules.pullback g').map ψ = 0 := by
        simp only [ψ, Functor.map_comp]
        rw [comp_eq_zero_iff_of_epi, comp_eq_zero_iff_of_mono]
    _ ↔ g'.appTop (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) = 0 :=
        pullback_scalar_eq_zero_iff g' ψ

/-- For a morphism `f` from the spectrum of a local ring whose closed point specializes to
`x`, the germ at `x` of a function `a` on `U ∋ x`, sent to `R` through the stalk at the
closed point, is the global function `f.appLE U ⊤ hg a` read in `R`. -/
lemma germ_stalkSpecializes_stalkClosedPointTo {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (f : Spec R ⟶ X) {x : X} (h : f (IsLocalRing.closedPoint R) ⤳ x)
    (U : X.Opens) (hxU : x ∈ U) (hg : ⊤ ≤ f ⁻¹ᵁ U) :
    X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ hg ≫ (Scheme.ΓSpecIso R).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo,
    Iso.trans_hom, Scheme.Hom.appLE, Category.assoc]
  rfl

/-- In a complete lattice without infinite strictly ascending chains, every family is
bounded by the supremum of a finite subfamily. -/
private lemma exists_finset_forall_le_biSup {α ι : Type*} [CompleteLattice α] [WellFoundedGT α]
    (f : ι → α) : ∃ F : Finset ι, ∀ i, f i ≤ ⨆ j ∈ F, f j := by
  classical
  obtain ⟨_, ⟨F, rfl⟩, hF⟩ :=
    (wellFounded_gt (α := α)).has_min (Set.range fun F : Finset ι ↦ ⨆ j ∈ F, f j) ⟨_, ∅, rfl⟩
  refine ⟨F, fun i ↦ ?_⟩
  have hle : (⨆ j ∈ F, f j) ≤ ⨆ j ∈ insert i F, f j :=
    biSup_mono fun j hj ↦ Finset.mem_insert_of_mem hj
  have heq : (⨆ j ∈ insert i F, f j) = ⨆ j ∈ F, f j := by
    by_contra hne
    exact hF _ ⟨_, rfl⟩ (lt_of_le_of_ne hle (Ne.symm hne))
  rw [← heq]
  exact le_biSup f (Finset.mem_insert_self i F)

/-- Pointwise separation by good sections gives a finite section seed on a Noetherian
scheme. -/
theorem finiteSeedOfSeparation : FiniteSeedOfSeparationStatement.{u} := by
  intro K _ X _ p z hpt htan
  classical
  let ι := {i : Σ L : LineBundle X, GlobalSections L.obj //
    VanishesAlong i.1 z i.2 ∧
      ∃ y : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p y ∧ ¬ VanishesAlong i.1 y i.2}
  let z₀ : X := z (IsLocalRing.closedPoint K)
  have hloc : ∀ i : ι, ∃ (U : X.Opens) (_ : z₀ ∈ U) (a : Γ(X, U)),
      ∀ (T : Scheme.{u}) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U),
        VanishesAlong i.1.1 g i.1.2 ↔ g.appLE U ⊤ hg a = 0 :=
    fun i ↦ exists_localEquation i.1.1 i.1.2 z₀
  choose U hU a ha using hloc
  let c : ι → X.presheaf.stalk z₀ := fun i ↦ X.presheaf.germ (U i) z₀ (hU i) (a i)
  obtain ⟨F₁, hF₁⟩ :=
    exists_finset_forall_le_biSup (fun i : ι ↦ trivializationOpen i.1.1.obj i.1.2)
  obtain ⟨F₂, hF₂⟩ := exists_finset_forall_le_biSup (fun i : ι ↦ Ideal.span {c i})
  let F := F₁ ∪ F₂
  let e := F.equivFin.symm
  refine ⟨F.card, fun k ↦ (e k).1.1.1, fun k ↦ (e k).1.1.2, fun k ↦ (e k).1.2.1,
    fun k ↦ (e k).1.2.2, ?_, ?_⟩
  · intro x hx hxz
    obtain ⟨L, s, hzs, hy, hxs⟩ := hpt x hx hxz
    rw [vanishesAlong_iff_not_mem, not_not] at hxs
    have hmem := hF₁ ⟨⟨L, s⟩, hzs, hy⟩ hxs
    simp only [Opens.mem_iSup] at hmem
    obtain ⟨j, hj, hxj⟩ := hmem
    obtain ⟨k, rfl⟩ : ∃ k, ((e k) : ι) = j :=
      ⟨e.symm ⟨j, Finset.mem_union_left _ hj⟩, by simp⟩
    refine ⟨k, ?_⟩
    rw [vanishesAlong_iff_not_mem, not_not]
    exact hxj
  · intro t ht
    obtain ⟨L, s, hzs, hy, hts⟩ := htan t ht
    by_contra hall
    push Not at hall
    apply hts
    have hmemU : ∀ {V : X.Opens}, z₀ ∈ V → ∀ τ, t τ ∈ V :=
      fun hV ↦ forall_mem_of_augmentation_comp ht.1.2 hV
    have hsp : t (IsLocalRing.closedPoint (DualNumber K)) ⤳ z₀ :=
      specializes_iff_forall_open.2 fun S hS hz ↦ hmemU (V := ⟨S, hS⟩) hz _
    let φ := X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo t
    have hkey : ∀ j : ι, VanishesAlong j.1.1 t j.1.2 ↔ φ (c j) = 0 := by
      intro j
      have hg : ⊤ ≤ t ⁻¹ᵁ U j := fun τ _ ↦ hmemU (hU j) τ
      rw [ha j _ t hg]
      have h2 := ConcreteCategory.congr_hom
        (germ_stalkSpecializes_stalkClosedPointTo t hsp (U j) (hU j) hg) (a j)
      have h3 : φ (c j) = (Scheme.ΓSpecIso _).hom (t.appLE (U j) ⊤ hg (a j)) := h2
      rw [h3]
      exact ((ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).hom).1.eq_iff' (map_zero _)).symm
    have hker : (⨆ j ∈ F₂, Ideal.span {c j}) ≤ RingHom.ker φ.hom := by
      refine iSup₂_le fun j hj ↦ (Ideal.span_singleton_le_iff_mem _).2 ?_
      obtain ⟨k, rfl⟩ : ∃ k, ((e k) : ι) = j :=
        ⟨e.symm ⟨j, Finset.mem_union_right _ hj⟩, by simp⟩
      have := hall k
      exact RingHom.mem_ker.2 ((hkey _).1 this)
    exact (hkey ⟨⟨L, s⟩, hzs, hy⟩).2
      (RingHom.mem_ker.1 (hker (hF₂ _ (Ideal.mem_span_singleton_self _))))

end Langlands.AlgebraicGeometry.Picard
