import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore
import Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStages

/-! # Proof of descent of finitely presented modules to finitely generated subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

namespace ModuleDescentProof

open ModuleDescentCore ModuleDescentStages Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.AffineVanishing

/-- A quasi-compact scheme is covered by finitely many affine opens. -/
lemma exists_finset_affineOpens_cover (Z : Scheme.{u}) [CompactSpace Z] :
    ∃ t : Finset Z.affineOpens, ∀ z : Z, ∃ i ∈ t, z ∈ (i : Z.Opens) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : Z.affineOpens => ((i : Z.Opens) : Set Z)) (fun i => (i : Z.Opens).2) (by
      intro z _
      obtain ⟨V, hV, hzV, -⟩ :=
        (Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens) (show z ∈ (⊤ : Z.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hzV⟩)
  refine ⟨t, fun z => ?_⟩
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  exact ⟨i, hi, hzi⟩

/-- A quasi-compact open inside an affine open is covered by finitely many basic opens
contained in it. -/
lemma exists_finset_basicOpen_cover {Z : Scheme.{u}} {W O : Z.Opens} (hW : IsAffineOpen W)
    (hO : IsCompact (O : Set Z)) (hOW : O ≤ W) :
    ∃ t : Finset Γ(Z, W), (∀ h ∈ t, Z.basicOpen h ≤ O) ∧
      ∀ z ∈ O, ∃ h ∈ t, z ∈ Z.basicOpen h := by
  classical
  let κ := {h : Γ(Z, W) // Z.basicOpen h ≤ O}
  obtain ⟨t, ht⟩ := hO.elim_finite_subcover (fun h : κ => (Z.basicOpen h.1 : Set Z))
    (fun h => (Z.basicOpen h.1).2) (by
      intro z hz
      obtain ⟨h, hhO, hzh⟩ := hW.exists_basicOpen_le ⟨z, hz⟩ (hOW hz)
      exact Set.mem_iUnion.2 ⟨⟨h, hhO⟩, hzh⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro h hh
    obtain ⟨h', _, rfl⟩ := Finset.mem_image.1 hh
    exact h'.2
  · intro z hz
    obtain ⟨h, hh, hzh⟩ := Set.mem_iUnion₂.1 (ht hz)
    exact ⟨h.1, Finset.mem_image_of_mem _ hh, hzh⟩

/-- On a basic open of an affine open, the restrictions of generators of the sections over the
affine open generate the sections. -/
lemma mem_span_restrict_basicOpen {Z : Scheme.{u}} (M : Z.Modules) [M.IsQuasicoherent]
    {U : Z.Opens} (hU : IsAffineOpen U) {n : ℕ} (γ : Fin n → Γ(M, U))
    (hγ : Submodule.span Γ(Z, U) (Set.range γ) = ⊤) (h : Γ(Z, U)) {O : Z.Opens}
    (hO : O = Z.basicOpen h) (hOU : O ≤ U) (s : Γ(M, O)) :
    s ∈ Submodule.span Γ(Z, O) (Set.range fun m => M.presheaf.map (homOfLE hOU).op (γ m)) := by
  subst hO
  have hloc := QuasicoherentLocal.isLocalizingAt_of_isQuasicoherent hU M
  obtain ⟨k, t, ht⟩ := hloc.exists_res_eq h s
  have hres : ∀ x ∈ Submodule.span Γ(Z, U) (Set.range γ),
      M.presheaf.map (homOfLE hOU).op x ∈
        Submodule.span Γ(Z, Z.basicOpen h)
          (Set.range fun m => M.presheaf.map (homOfLE hOU).op (γ m)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact Submodule.subset_span ⟨m, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hx
  have ht' : rres (Z.basicOpen_le h) h ^ k • s ∈
      Submodule.span Γ(Z, Z.basicOpen h)
        (Set.range fun m => M.presheaf.map (homOfLE hOU).op (γ m)) := by
    rw [← ht]
    exact hres t (hγ ▸ Submodule.mem_top)
  have hu : IsUnit (rres (Z.basicOpen_le h) h ^ k) :=
    (Z.toRingedSpace.isUnit_res_basicOpen h).pow k
  obtain ⟨u, hu⟩ := hu
  have : s = (↑u⁻¹ : Γ(Z, Z.basicOpen h)) • (rres (Z.basicOpen_le h) h ^ k • s) := by
    rw [← hu, smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ ht'

section Stage

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {X₀ X : Scheme.{u}} {f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)} {a : X ⟶ X₀}
  {f : X ⟶ Spec (CommRingCat.of A)}

lemma spec_map_comp (T : Subalgebra A₀ A) :
    Spec.map (CommRingCat.ofHom (algebraMap T A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A₀ T)) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

lemma exists_isLift (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (T : Subalgebra A₀ A) : ∃ c, IsLift f₀ a f T c :=
  ⟨pullback.lift a (f ≫ Spec.map (CommRingCat.ofHom (algebraMap T A)))
    (by rw [Category.assoc, spec_map_comp, hpb.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _⟩

lemma IsLift.eq {T : Subalgebra A₀ A} {c c' : X ⟶ stage f₀ T} (hc : IsLift f₀ a f T c)
    (hc' : IsLift f₀ a f T c') : c = c' :=
  pullback.hom_ext (hc.1.trans hc'.1.symm) (hc.2.trans hc'.2.symm)

lemma IsLift.isPullback (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    {T : Subalgebra A₀ A} {c : X ⟶ stage f₀ T} (hc : IsLift f₀ a f T c) :
    IsPullback c f (stageSnd f₀ T) (Spec.map (CommRingCat.ofHom (algebraMap T A))) := by
  refine IsPullback.of_right ?_ hc.2 (IsPullback.of_hasPullback _ _)
  rw [hc.1, spec_map_comp]
  exact hpb

lemma IsLift.isAffineHom
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    {T : Subalgebra A₀ A} {c : X ⟶ stage f₀ T} (hc : IsLift f₀ a f T c) : IsAffineHom c :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (IsLift.isPullback hpb hc).flip inferInstance

lemma isNoetherianRing_stage [IsNoetherianRing A₀] [LocallyOfFiniteType f₀]
    {T : Subalgebra A₀ A} (hT : T.FG) {V : (stage f₀ T).Opens} (hV : IsAffineOpen V) :
    IsNoetherianRing Γ(stage f₀ T, V) := by
  have : IsNoetherianRing T := by
    have := (Subalgebra.fg_iff_finiteType T).mp hT
    exact Algebra.FiniteType.isNoetherianRing A₀ T
  have : IsNoetherianRing Γ(Spec (CommRingCat.of T), ⊤) :=
    isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of T)).symm.commRingCatIsoToRingEquiv
  have hft := (stageSnd f₀ T).finiteType_appLE (isAffineOpen_top _) hV le_top
  let := ((stageSnd f₀ T).appLE ⊤ V le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (CommRingCat.of T), ⊤) Γ(stage f₀ T, V) := hft
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of T), ⊤) Γ(stage f₀ T, V)

lemma isAffineHom_fromSpec_stage [IsSeparated f₀] {T : Subalgebra A₀ A}
    {V : (stage f₀ T).Opens} (hV : IsAffineOpen V) : IsAffineHom hV.fromSpec := by
  have : IsSeparated (stageSnd f₀ T) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback _ _)
      inferInstance
  exact IsAffineHom.of_comp hV.fromSpec (stageSnd f₀ T)

/-- A finite free presentation of the sections over each member of a finite affine cover. -/
lemma exists_relations {R P : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] :
    ∃ (n : ℕ) (γ : Fin n → P) (m : ℕ) (ρ : Fin m → Fin n → R),
      Submodule.span R (Set.range γ) = ⊤ ∧ (∀ a, ∑ l, ρ a l • γ l = 0) ∧
      ∀ c : Fin n → R, ∑ l, c l • γ l = 0 → c ∈ Submodule.span R (Set.range ρ) := by
  obtain ⟨n, γ, hγ⟩ := Module.Finite.exists_fin (R := R) (M := P)
  have hsurj : Function.Surjective (Fintype.linearCombination R γ) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R γ).1 hγ
  obtain ⟨m, ρ, hρ⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Module.FinitePresentation.fg_ker _ hsurj)
  refine ⟨n, γ, m, ρ, hγ, fun a => ?_, fun c hc => ?_⟩
  · have : ρ a ∈ LinearMap.ker (Fintype.linearCombination R γ) :=
      hρ ▸ Submodule.subset_span ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at this
    exact this
  · rw [hρ, LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact hc

end Stage

end ModuleDescentProof

open ModuleDescentProof ModuleDescentCore ModuleDescentStages in
/-- Proof of `FinitePresentationModuleSubalgebraDescentStatement`. -/
theorem finitePresentationModuleSubalgebraDescent :
    FinitePresentationModuleSubalgebraDescentStatement.{u} := by
  intro A₀ _ _ A _ _ X₀ f₀ _ _ _ X a f hpb M hM s
  classical
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  have : IsAffineHom a :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  -- A finite affine open cover of `X₀`.
  obtain ⟨t, ht⟩ := exists_finset_affineOpens_cover X₀
  let W : t → X₀.Opens := fun i => (i.1 : X₀.Opens)
  have hW : ∀ i, IsAffineOpen (W i) := fun i => i.1.2
  -- Presentations of the sections over the preimages.
  have hfp : ∀ i, Module.FinitePresentation Γ(X, a ⁻¹ᵁ W i) Γ(M, a ⁻¹ᵁ W i) := fun i =>
    finitePresentation_sections_of_isAffineOpen M ((hW i).preimage a)
  choose n γ m ρ hγ hρ hrel using fun i => @exists_relations _ _ _ _ _ (hfp i)
  -- Finite covers of the overlaps by basic opens.
  have hcpt : ∀ ik : t × t, IsCompact ((W ik.1 ⊓ W ik.2 : X₀.Opens) : Set X₀) := fun ik =>
    QuasiSeparatedSpace.inter_isCompact _ _ (W ik.1).2 (hW ik.1).isCompact (W ik.2).2
      (hW ik.2).isCompact
  choose tt htt₁ htt₂ using fun ik : t × t =>
    exists_finset_basicOpen_cover (hW ik.1) (hcpt ik) inf_le_left
  -- Cross coefficients.
  let J := Σ ik : t × t, Σ _ : tt ik, Fin (n ik.2)
  have hDle : ∀ j : J, a ⁻¹ᵁ X₀.basicOpen (j.2.1 : Γ(X₀, W j.1.1)) ≤ a ⁻¹ᵁ W j.1.1 :=
    fun j => a.preimage_mono (X₀.basicOpen_le _)
  have hDle' : ∀ j : J, a ⁻¹ᵁ X₀.basicOpen (j.2.1 : Γ(X₀, W j.1.1)) ≤ a ⁻¹ᵁ W j.1.2 :=
    fun j => a.preimage_mono ((htt₁ j.1 j.2.1.1 j.2.1.2).trans inf_le_right)
  have hcross0 : ∀ j : J, M.presheaf.map (homOfLE (hDle' j)).op (γ j.1.2 j.2.2) ∈
      Submodule.span Γ(X, a ⁻¹ᵁ X₀.basicOpen (j.2.1 : Γ(X₀, W j.1.1)))
        (Set.range fun l => M.presheaf.map (homOfLE (hDle j)).op (γ j.1.1 l)) := fun j =>
    mem_span_restrict_basicOpen M ((hW j.1.1).preimage a) (γ j.1.1) (hγ j.1.1)
      (a.app _ (j.2.1 : Γ(X₀, W j.1.1))) (Scheme.preimage_basicOpen a _) (hDle j) _
  choose cc hcc using fun j : J => (Submodule.mem_span_range_iff_exists_fun _).1 (hcross0 j)
  -- Descend the relation entries and the cross coefficients.
  obtain ⟨C₁, hC₁⟩ := exists_finset_forall_descends f₀ a f hpb
    (fun j : Σ i : t, Fin (m i) × Fin (n i) => W j.1) (fun j => hW j.1)
    (fun j => ρ j.1 j.2.1 j.2.2)
  obtain ⟨C₂, hC₂⟩ := exists_finset_forall_descends f₀ a f hpb
    (fun q : Σ j : J, Fin (n j.1.1) => X₀.basicOpen (q.1.2.1 : Γ(X₀, W q.1.1.1)))
    (fun q => (hW q.1.1.1).basicOpen _) (fun q => cc q.1 q.2)
  let T : Subalgebra A₀ A := Algebra.adjoin A₀ (↑(C₁ ∪ C₂ ∪ s) : Set A)
  have hT : T.FG := Subalgebra.fg_adjoin_finset _
  have hCT : (↑(C₁ ∪ C₂ ∪ s) : Set A) ⊆ T := Algebra.subset_adjoin
  have hC₁T : (↑C₁ : Set A) ⊆ T := fun x hx => hCT (by simp [hx])
  have hC₂T : (↑C₂ : Set A) ⊆ T := fun x hx => hCT (by simp [hx])
  refine ⟨T, hT, fun x hx => hCT (by simp [hx]), ?_⟩
  have key : ∀ c, IsLift f₀ a f T c → ∃ G : (stage f₀ T).Modules, G.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pullback c).obj G ≅ M) := by
    intro c hc
    have : IsAffineHom c := IsLift.isAffineHom hpb hc
    choose y₁ hy₁ using hC₁ T hC₁T c hc
    choose y₂ hy₂ using hC₂ T hC₂T c hc
    obtain ⟨hc₁, -⟩ := hc
    subst hc₁
    have hy₁' : ∀ j, c.app _ (y₁ j) = ρ j.1 j.2.1 j.2.2 := fun j => by
      simpa using hy₁ j rfl
    have hy₂' : ∀ q, c.app _ (y₂ q) = cc q.1 q.2 := fun q => by
      simpa using hy₂ q rfl
    have : IsAffineHom (stageFst f₀ T) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip
        inferInstance
    let V : t → (stage f₀ T).Opens := fun i => stageFst f₀ T ⁻¹ᵁ W i
    have hV : ∀ i, IsAffineOpen (V i) := fun i => (hW i).preimage _
    have : ∀ i, IsNoetherianRing Γ(stage f₀ T, V i) := fun i => isNoetherianRing_stage hT (hV i)
    have hcov : ∀ y, ∃ i, y ∈ V i := fun y => by
      obtain ⟨i, hi, hyi⟩ := ht (stageFst f₀ T y)
      exact ⟨⟨i, hi⟩, hyi⟩
    refine exists_isFinitePresentation_pullback_iso c M V hV (g := fun i l => γ i l)
      (fun i => isAffineHom_fromSpec_stage (hV i)) hcov ?_ ?_
    · intro i k y hy
      obtain ⟨h, hh, hyh⟩ := htt₂ (i, k) (stageFst f₀ T y) hy
      refine ⟨stageFst f₀ T ⁻¹ᵁ X₀.basicOpen h,
        (stageFst f₀ T).preimage_mono (htt₁ (i, k) h hh), hyh, fun l => ?_⟩
      let j : J := ⟨(i, k), ⟨h, hh⟩, l⟩
      have hsm : ∀ r, (y₂ ⟨j, r⟩ • (directImage c M).presheaf.map
          (homOfLE ((stageFst f₀ T).preimage_mono
            ((htt₁ (i, k) h hh).trans inf_le_left))).op (γ i r) :
            Γ(directImage c M, stageFst f₀ T ⁻¹ᵁ X₀.basicOpen h)) =
          (cc j r • M.presheaf.map (homOfLE (hDle j)).op (γ i r) :
            Γ(M, (c ≫ stageFst f₀ T) ⁻¹ᵁ X₀.basicOpen (j.2.1 : Γ(X₀, W j.1.1)))) := by
        intro r
        rw [← hy₂' ⟨j, r⟩]
        rfl
      have e' : (directImage c M).presheaf.map (homOfLE ((stageFst f₀ T).preimage_mono
          ((htt₁ (i, k) h hh).trans inf_le_right))).op (γ k l) =
          ∑ r, (y₂ ⟨j, r⟩ • (directImage c M).presheaf.map
            (homOfLE ((stageFst f₀ T).preimage_mono
              ((htt₁ (i, k) h hh).trans inf_le_left))).op (γ i r) :
              Γ(directImage c M, stageFst f₀ T ⁻¹ᵁ X₀.basicOpen h)) := by
        rw [Finset.sum_congr rfl fun r _ => hsm r]
        exact (hcc j).symm
      rw [e']
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
    · intro k
      refine ⟨m k, fun r l => y₁ ⟨k, r, l⟩, fun r => ?_, hγ k, fun c' hc' => ?_⟩
      · change ∑ l, (c.app (V k) (y₁ ⟨k, r, l⟩) • (show Γ(M, c ⁻¹ᵁ V k) from γ k l)) = 0
        have hfun2 : ∀ l, c.app (V k) (y₁ ⟨k, r, l⟩) = ρ k r l := fun l => hy₁' ⟨k, r, l⟩
        simp only [hfun2]
        exact hρ k r
      · have hfun : (fun r l => c.app (V k) (y₁ ⟨k, r, l⟩)) = ρ k := by
          funext r l
          exact hy₁' ⟨k, r, l⟩
        rw [hfun]
        exact hrel k c' hc'
  obtain ⟨q₀, hq₀⟩ := exists_isLift hpb T
  obtain ⟨G, hG, hiso⟩ := key q₀ hq₀
  refine ⟨G, hG, fun c hc₁ hc₂ => ?_⟩
  have : c = q₀ := IsLift.eq ⟨hc₁, hc₂⟩ hq₀
  subst this
  exact hiso

end Langlands.AlgebraicGeometry.NoetherianApproximation
