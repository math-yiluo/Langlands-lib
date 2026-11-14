import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistUniformVanishing
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top

/-! # Nonzero sections of large twists on nonempty fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Modules.FibreTwist

/-- An invertible module has nonzero sections over every nonempty open. -/
lemma nontrivial_sections_of_isInvertible {X : Scheme.{u}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (W : X.affineOpens) [Nonempty W.1] :
    Nontrivial Γ(M, W.1) := by
  obtain ⟨hD, ⟨e⟩⟩ := hM.dual_monoidalV2
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hbij := hM.bijective_lift_tensorSectionsBilin_monoidalV2 hD W
  have h0 := (Equiv.ofBijective _ hbij).symm.subsingleton
  have h1 : Subsingleton Γ(𝟙_ X.Modules, W.1) :=
    @Equiv.subsingleton _ _ (asIso (e.hom.app W.1)).addCommGroupIsoToAddEquiv.toEquiv.symm h0
  have h2 : Subsingleton Γ(X, W.1) := h1
  exact not_subsingleton Γ(X, W.1) h2

section CechZero

open CechBridge

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {π : X ⟶ Spec R}

/-- A nonzero Čech `0`-cocycle gives nonzero Čech homology in degree `0`. -/
lemma not_isZero_homology_zero (F : OModulePresheaf π) (K : X.OrderedAffineCover)
    (σ : F.cochain K 0) (hσ : F.d K 0 σ = 0) (hne : σ ≠ 0) :
    ¬ IsZero ((cechComplex F K).homology 0) := by
  intro hz
  have hex : (cechComplex F K).ExactAt 0 := ((cechComplex F K).exactAt_iff_isZero_homology 0).2 hz
  rw [HomologicalComplex.exactAt_iff' (cechComplex F K) 0 0 1 (by simp) (by simp)] at hex
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 hex
  have h00 : (cechComplex F K).d 0 0 = 0 := (cechComplex F K).shape 0 0 (by simp)
  have hmem : σ ∈ LinearMap.ker ((cechComplex F K).d 0 1).hom := by
    rw [cechComplex_d F K 0]
    exact hσ
  change σ ∈ LinearMap.ker ((cechComplex F K).sc' 0 0 1).g.hom at hmem
  rw [← h] at hmem
  obtain ⟨y, hy⟩ := hmem
  apply hne
  rw [← hy]
  change ((cechComplex F K).d 0 0).hom y = 0
  rw [h00]
  rfl

lemma not_isZero_homology_zero_of_iso {C D : CochainComplex (ModuleCat.{u} R) ℕ} (e : C ≅ D)
    (h : ¬ IsZero (C.homology 0)) : ¬ IsZero (D.homology 0) :=
  fun hD => h (IsZero.of_iso hD (HomologicalComplex.homologyMapIso e 0))

end CechZero

section GlobalGeneration

open CechBridge

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
  {L : P.Modules} {N : ℕ} (𝔓 : L.ProjPresentation q N)

/-- The degree-zero Čech homology of `F ⊗ O(d)` is nonzero once a global generation datum exists
on a nonempty scheme. -/
lemma not_isZero_cech_twist [IsSeparated q] [IsClosedImmersion 𝔓.toProj]
    (hL : Scheme.Modules.IsInvertible L) (F : P.Modules) (hF : Scheme.Modules.IsInvertible F)
    [Nonempty P] (d : ℕ) {m : ℕ}
    (σ : Fin m → ((OModulePresheaf.ofModules q F).tensor (ProjSpace.twist q 𝔓.toProj d)).H0
      (ProjSpace.stdCoverPullback 𝔓.toProj))
    (hσ : ∀ s : (ProjSpace.stdCoverPullback 𝔓.toProj).Idx 0,
      Submodule.span Γ(P, (ProjSpace.stdCoverPullback 𝔓.toProj).inter s)
        (Set.range fun l : Fin m =>
          (σ l : ((OModulePresheaf.ofModules q F).tensor (ProjSpace.twist q 𝔓.toProj d)).cochain
            (ProjSpace.stdCoverPullback 𝔓.toProj) 0) s) = ⊤) :
    ¬ IsZero ((cechComplex ((OModulePresheaf.ofModules q F).tensor
      (ProjSpace.twist q 𝔓.toProj d)) (ProjSpace.stdCoverPullback 𝔓.toProj)).homology 0) := by
  let K := ProjSpace.stdCoverPullback 𝔓.toProj
  obtain ⟨e, -, he, hbij⟩ := 𝔓.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 d
  obtain ⟨y⟩ := ‹Nonempty P›
  have hy : y ∈ ⨆ i, K.U i := by
    rw [K.iSup_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  let s₀ : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by
    have : a = b := Fin.ext (by have := a.2; have := b.2; omega)
    rw [this]
    exact lt_irrefl b)⟩
  have hys : y ∈ K.inter s₀ := by
    change y ∈ ⨅ j : Fin 1, K.U i
    rw [iInf_const]
    exact hyi
  let W := K.affineInter q s₀
  have : Nonempty W.1 := ⟨⟨y, hys⟩⟩
  have hLd : Scheme.Modules.IsInvertible (L.tensorPow d) := hL.tensorPow_monoidalV2 d
  have hFLd : Scheme.Modules.IsInvertible (F ⊗ L.tensorPow d) := hF.tensor_monoidalV2 hLd
  have h1 : Nontrivial Γ(F ⊗ L.tensorPow d, W.1) := nontrivial_sections_of_isInvertible hFLd W
  have h2 : Nontrivial (((OModulePresheaf.ofModules q F).tensor
      (OModulePresheaf.ofModules q (L.tensorPow d))).obj W.1) :=
    @Equiv.nontrivial _ _ (Equiv.ofBijective _ (tensorSectionsAffHom_bijective (q := q) hF hLd W)) h1
  have h3 : Nontrivial (((OModulePresheaf.ofModules q F).tensor
      (ProjSpace.twist q 𝔓.toProj d)).obj W.1) :=
    (Equiv.ofBijective _ (tensorRightAffHom_bijective (OModulePresheaf.ofModules q F)
      (OModulePresheaf.ofModules q (L.tensorPow d)) (ProjSpace.twist q 𝔓.toProj d) e
      (fun h x => he _ _ h x) W (hbij _ i.down (K.inter_le s₀ 0)))).symm.nontrivial
  have hex : ∃ l, (σ l : ((OModulePresheaf.ofModules q F).tensor
      (ProjSpace.twist q 𝔓.toProj d)).cochain K 0) ≠ 0 := by
    by_contra hall
    push Not at hall
    have htop := hσ s₀
    have hbot : Submodule.span Γ(P, K.inter s₀) (Set.range fun l : Fin m =>
        (σ l : ((OModulePresheaf.ofModules q F).tensor
          (ProjSpace.twist q 𝔓.toProj d)).cochain K 0) s₀) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact congrFun (hall l) s₀
    rw [hbot] at htop
    obtain ⟨a, b, hab⟩ := h3
    exact hab ((Submodule.eq_bot_iff _).1 htop.symm a trivial ▸
      ((Submodule.eq_bot_iff _).1 htop.symm b trivial).symm)
  obtain ⟨l, hl⟩ := hex
  exact not_isZero_homology_zero _ K _ (σ l).2 hl

/-- Transfer of nonvanishing in degree `0` from the twisted presheaf to the presheaf tensor with
sections of `L^{⊗ d}`. -/
lemma not_isZero_cech_tensor_of_twist [IsSeparated q] [IsAffineHom 𝔓.toProj] (F : P.Modules)
    (d : ℕ) (e : ∀ U : P.Opens, Γ(L.tensorPow d, U) →ₗ[Γ(P, U)] ProjSpace.twistObj q 𝔓.toProj d U)
    (he : ∀ (U U' : P.Opens) (h : U ≤ U') (x : Γ(L.tensorPow d, U')),
      e U ((L.tensorPow d).presheaf.map (homOfLE h).op x) = ProjSpace.twistRes q 𝔓.toProj d h (e U' x))
    (hbij : ∀ (U : P.Opens) (i : Fin (N + 1)), U ≤ ProjSpace.pullbackChart 𝔓.toProj i →
      Function.Bijective (e U))
    (h : ¬ IsZero ((cechComplex ((OModulePresheaf.ofModules q F).tensor
      (ProjSpace.twist q 𝔓.toProj d)) (ProjSpace.stdCoverPullback 𝔓.toProj)).homology 0)) :
    ¬ IsZero ((cechComplex ((OModulePresheaf.ofModules q F).tensor
      (OModulePresheaf.ofModules q (L.tensorPow d))) (ProjSpace.stdCoverPullback 𝔓.toProj)).homology 0) :=
  not_isZero_homology_zero_of_iso (cechComplexIsoOfBijective (ProjSpace.stdCoverPullback 𝔓.toProj)
    (tensorRightAffHom (OModulePresheaf.ofModules q F)
      (OModulePresheaf.ofModules q (L.tensorPow d)) (ProjSpace.twist q 𝔓.toProj d) e
      (fun h x => he _ _ h x))
    (fun _ s => tensorRightAffHom_bijective (OModulePresheaf.ofModules q F)
      (OModulePresheaf.ofModules q (L.tensorPow d)) (ProjSpace.twist q 𝔓.toProj d) e
      (fun h x => he _ _ h x) _
      (hbij _ (s.1 0).down (CechBridge.inter_le_pullbackChart 𝔓 s)))).symm h

/-- Transfer of nonvanishing in degree `0` to the actual sections of `F ⊗ M`. -/
lemma not_isZero_relativeCohomology_zero_of_cech [IsSeparated q] (K : P.OrderedAffineCover)
    (F M : P.Modules) (hF : Scheme.Modules.IsInvertible F) (hM : Scheme.Modules.IsInvertible M)
    (h : ¬ IsZero ((cechComplex ((OModulePresheaf.ofModules q F).tensor
      (OModulePresheaf.ofModules q M)) K).homology 0)) :
    ¬ IsZero ((DerivedSections.relativeCohomology q 0).obj (F ⊗ M)) := by
  have h' := not_isZero_homology_zero_of_iso (cechComplexIsoOfBijective K
    (tensorSectionsAffHom (q := q) F M) (fun _ _ => tensorSectionsAffHom_bijective hF hM _)) h
  have hFM : Scheme.Modules.IsInvertible (F ⊗ M) := hF.tensor_monoidalV2 hM
  have : (F ⊗ M).IsQuasicoherent :=
    Picard.IsLocallyFreeRankOne.isQuasicoherent (fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hFM.exists_trivialization x
      exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫ e⟩⟩)
  exact fun hz => h' (IsZero.of_iso hz
    (CechResolution.cechCohomologyIso (R := CommRingCat.of A) q K (F ⊗ M) 0))

/-- **Nonzero sections of large twists.** On a nonempty scheme with a presentation whose morphism
to projective space is a closed immersion, `H⁰(F ⊗ L^{⊗ d}) ≠ 0` for all large `d`. -/
theorem exists_not_isZero_relativeCohomology_zero [IsSeparated q] [IsClosedImmersion 𝔓.toProj]
    (hL : Scheme.Modules.IsInvertible L) (F : P.Modules) (hF : Scheme.Modules.IsInvertible F)
    [Nonempty P] :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      ¬ IsZero ((DerivedSections.relativeCohomology q 0).obj (F ⊗ L.tensorPow d)) := by
  obtain ⟨d₁, hd₁⟩ := OModulePresheaf.exists_forall_exists_H0_tensor_twist_span_eq_top 𝔓.toProj
    𝔓.toProj_π (OModulePresheaf.ofModules q F)
    (OModulePresheaf.isCoherent_ofModules_of_locallyTrivial q F hF.exists_trivialization)
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial q F hF.exists_trivialization)
  refine ⟨d₁, fun d hd => ?_⟩
  obtain ⟨m, σ, hσ⟩ := hd₁ d hd
  obtain ⟨e, -, he, hbij⟩ := 𝔓.exists_linearMap_sections_tensorPow_twistObj_monoidalV2 d
  exact not_isZero_relativeCohomology_zero_of_cech (ProjSpace.stdCoverPullback 𝔓.toProj) F
    (L.tensorPow d) hF (hL.tensorPow_monoidalV2 d)
    (not_isZero_cech_tensor_of_twist 𝔓 F d e he hbij (not_isZero_cech_twist 𝔓 hL F hF d σ hσ))

end GlobalGeneration

section Fibre

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero sections of large twists on a nonempty base change along `Spec B ⟶ T`. -/
theorem nonzeroSections_of_point (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ) (𝔓 : 𝓛X.ProjPresentation f N)
    [IsProper f] (h𝓛 : Scheme.Modules.IsInvertible 𝓛X) [IsClosedImmersion 𝔓.toProj]
    (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (F : (pullback f s).Modules) (hF : Scheme.Modules.IsInvertible F) (B : CommRingCat.{u})
    (b : Spec B ⟶ T) (hne : Nonempty (pullback (C := Scheme.{u}) (pullback.snd f s) b)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ¬ IsZero ((DerivedSections.relativeCohomology (pullback.snd (pullback.snd f s) b) 0).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd f s) b)).obj
          (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n))) := by
  let gT := pullback.snd f s
  let a := pullback.fst gT b
  let q := pullback.snd gT b
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (b ≫ s)
  let : Algebra A B := φ.hom.toAlgebra
  have sq : IsPullback (a ≫ pullback.fst f s) q f
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    have h := (IsPullback.of_hasPullback gT b).paste_horiz (IsPullback.of_hasPullback f s)
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap A B)) = b ≫ s := Spec.map_preimage (b ≫ s)
    rw [hφ]
    exact h
  obtain ⟨𝔓', -, -, hpb⟩ := 𝔓.exists_baseChange_of_isPullback sq
  have : IsClosedImmersion 𝔓'.toProj :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb ‹_›
  let L := (Scheme.Modules.pullback (a ≫ pullback.fst f s)).obj 𝓛X
  have hL : Scheme.Modules.IsInvertible L := h𝓛.pullback _
  have hFt : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback a).obj F) := hF.pullback _
  obtain ⟨d₁, hd₁⟩ := exists_not_isZero_relativeCohomology_zero 𝔓' hL
    ((Scheme.Modules.pullback a).obj F) hFt
  refine ⟨d₁, fun n hn hz => hd₁ n hn ?_⟩
  exact IsZero.of_iso hz ((DerivedSections.relativeCohomology q 0).mapIso
    (pullbackTwistIso _ a ((Scheme.Modules.pullbackComp a (pullback.fst f s)).app 𝓛X) F n ≪≫
      twistTensorPowIso L _ n)).symm

/-- **Clause 2 of `ProjectiveFibreTwistCohomologyStatement`.** On a nonempty fibre, `H⁰` of all
large twists is nonzero. -/
theorem nonzeroSections (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (𝓛X : X.Modules) (N : ℕ) (𝔓 : 𝓛X.ProjPresentation f N)
    [IsProper f] (h𝓛 : Scheme.Modules.IsInvertible 𝓛X) [IsClosedImmersion 𝔓.toProj]
    (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A))
    (F : (pullback f s).Modules) (hF : Scheme.Modules.IsInvertible F) (t : T)
    (hne : Nonempty (pullback (C := Scheme.{u}) (pullback.snd f s) (T.fromSpecResidueField t))) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ¬ IsZero (fibreCohomology (pullback.snd f s) t
        (twist ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) F n) 0) :=
  nonzeroSections_of_point A f 𝓛X N 𝔓 h𝓛 T s F hF (T.residueField t) (T.fromSpecResidueField t) hne

end Fibre

end Langlands.AlgebraicGeometry.Modules.FibreTwist
