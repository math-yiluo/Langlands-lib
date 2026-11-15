import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsShrink

/-! # Shrinking a chart of Murre's construction to a monomorphism

In the situation of `MurreChartsShrink`, let `A[1/a]` be formally unramified over `R`, so that
the diagonal `Spec A[1/a] ⟶ Spec (A[1/a] ⊗_R A[1/a])` is an open immersion. The points of
`Spec (A[1/a] ⊗_R A[1/a])` where the two pullbacks of `ξ` agree form an open set, and outside
the diagonal this set contains no point over the generic region (primes disjoint from `M`).
Removing its closure gives `b` such that the restriction of `ξ` to `Spec A[1/b]` is a
monomorphism. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

variable {s : Spec R} {Y : Over (Spec ((Spec R).presheaf.stalk s))}
  (e : (baseChange ((Spec R).fromSpecStalk s) F).RepresentableBy Y)
variable {B : Type u} [CommRing B] [Algebra R B]
  (t : Spec (CommRingCat.of B) ⟶ Spec ((Spec R).presheaf.stalk s))
  (ht : t ≫ (Spec R).fromSpecStalk s = (ovR R B).hom)
  (j : Over.mk t ⟶ Y) [IsOpenImmersion j.left]
variable {A : Type u} [CommRing A] [Algebra R A] [Algebra A B] [IsScalarTower R A B]
  (M : Submonoid A) [IsLocalization M B]
  (ξ : F.obj (op (ovR R A)))

/-- A point of `Spec (A[1/a] ⊗_R A[1/a])` where the two pullbacks of `ξ` agree and whose
projections are disjoint from `M` lies on the diagonal. -/
theorem mem_range_comap_lmul
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (a : A) (ha : a ∈ M)
    (c : PrimeSpectrum (Localization.Away a ⊗[R] Localization.Away a))
    (hc : AgreeAt
      (F.map (homR (Algebra.TensorProduct.includeLeft :
        Localization.Away a →ₐ[R] Localization.Away a ⊗[R] Localization.Away a)).op (resA ξ a))
      (F.map (homR (Algebra.TensorProduct.includeRight :
        Localization.Away a →ₐ[R] Localization.Away a ⊗[R] Localization.Away a)).op (resA ξ a))
      c)
    (hdisj : ∀ m ∈ M,
      (algebraMap A (Localization.Away a) m ⊗ₜ[R] (1 : Localization.Away a)) ∉ c.asIdeal ∧
      ((1 : Localization.Away a) ⊗ₜ[R] algebraMap A (Localization.Away a) m) ∉ c.asIdeal) :
    c ∈ Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' R :
      Localization.Away a ⊗[R] Localization.Away a →ₐ[R] Localization.Away a).toRingHom) := by
  let Aa := Localization.Away a
  let C := Aa ⊗[R] Aa
  let κ := c.asIdeal.ResidueField
  let ψ : C →ₐ[R] κ := IsScalarTower.toAlgHom R C κ
  let ψ₁ : Aa →ₐ[R] κ := ψ.comp Algebra.TensorProduct.includeLeft
  let ψ₂ : Aa →ₐ[R] κ := ψ.comp Algebra.TensorProduct.includeRight
  let a' : DivIndex M := DivIndex.mk a ha
  have hunit₁ : ∀ m : M, IsUnit ((ψ₁.comp (IsScalarTower.toAlgHom R A Aa)) m) := fun m => by
    refine isUnit_iff_ne_zero.2 ?_
    change algebraMap C κ (algebraMap A Aa m ⊗ₜ[R] 1) ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact (hdisj m m.2).1
  have hunit₂ : ∀ m : M, IsUnit ((ψ₂.comp (IsScalarTower.toAlgHom R A Aa)) m) := fun m => by
    refine isUnit_iff_ne_zero.2 ?_
    change algebraMap C κ (1 ⊗ₜ[R] algebraMap A Aa m) ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact (hdisj m m.2).2
  let χ₁ : B →ₐ[R] κ := IsLocalization.liftAlgHom hunit₁
  let χ₂ : B →ₐ[R] κ := IsLocalization.liftAlgHom hunit₂
  have hχ₁ : χ₁.comp (toLocₐ M B a') = ψ₁ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    change χ₁ (toLoc M B a' (algebraMap A Aa x)) = ψ₁ (algebraMap A Aa x)
    rw [toLoc_algebraMap]
    exact IsLocalization.lift_eq hunit₁ x
  have hχ₂ : χ₂.comp (toLocₐ M B a') = ψ₂ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    change χ₂ (toLoc M B a' (algebraMap A Aa x)) = ψ₂ (algebraMap A Aa x)
    rw [toLoc_algebraMap]
    exact IsLocalization.lift_eq hunit₂ x
  let g := (Spec R).fromSpecStalk s
  have hξB : ∀ χ : B →ₐ[R] κ, F.map (homR (χ.comp (toLocₐ M B a'))).op (resA ξ a) =
      F.map (homR χ).op (elemEquiv g e (ovR R B) t ht j) := by
    intro χ
    rw [homR_comp, op_comp, Functor.map_comp_apply, map_toLocₐ_resA e t ht j M ξ hξ a ha]
  have hc' : F.map (homR χ₁).op (elemEquiv g e (ovR R B) t ht j) =
      F.map (homR χ₂).op (elemEquiv g e (ovR R B) t ht j) := by
    rw [← hξB, ← hξB, hχ₁, hχ₂]
    have h := hc
    rw [AgreeAt, residueOver,
      map_homR_map_homR (F := F) Algebra.TensorProduct.includeLeft ψ (resA ξ a),
      map_homR_map_homR (F := F) Algebra.TensorProduct.includeRight ψ (resA ξ a)] at h
    exact h
  have ht₁ : ((homR χ₁).left ≫ t) ≫ g = (ovR R κ).hom := by
    rw [Category.assoc, ht]
    exact Over.w (homR χ₁)
  rw [elemEquiv_naturality g e (homR χ₁) _ t ht₁ ht j,
    elemEquiv_naturality g e (homR χ₂) _ t ht₁ ht j] at hc'
  have hk := congrArg (fun k => k.left) ((elemEquiv g e (ovR R κ) _ ht₁).injective hc')
  simp only [Over.comp_left, Over.homMk_left] at hk
  have hk' : (homR χ₁).left = (homR χ₂).left := (cancel_mono j.left).1 hk
  rw [homR_left, homR_left] at hk'
  have hχ : χ₁ = χ₂ :=
    AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective hk'))
  have hψ : ψ₁ = ψ₂ := by rw [← hχ₁, ← hχ₂, hχ]
  have hψm : ψ₁.comp (Algebra.TensorProduct.lmul' R) = ψ := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    rw [AlgHom.comp_apply, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
    have : x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : Aa)) * ((1 : Aa) ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul]
    change ψ₁ x * ψ₁ y = ψ₁ x * ψ₂ y
    rw [hψ]
  refine ⟨PrimeSpectrum.comap ψ₁.toRingHom (IsLocalRing.closedPoint κ), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (Algebra.TensorProduct.lmul' R : C →ₐ[R] Aa).toRingHom
    (Ideal.comap ψ₁.toRingHom (IsLocalRing.maximalIdeal κ)) = c.asIdeal
  rw [Ideal.comap_comap, IsLocalRing.maximalIdeal_eq_bot]
  have h2 : ψ₁.toRingHom.comp (Algebra.TensorProduct.lmul' R : C →ₐ[R] Aa).toRingHom =
      algebraMap C κ := congrArg AlgHom.toRingHom hψm
  rw [h2]
  exact Ideal.ker_algebraMap_residueField _

/-- Monomorphic shrinking. -/
theorem exists_mono (hZ : ZariskiSheaf F) (h2 : FilteredColimits F) (hF : FaithfullyFlatSheaf F)
    (hrep : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    [IsNoetherianRing R] [Algebra.FiniteType R A]
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (a : A) (ha : a ∈ M) [Algebra.FormallyUnramified R (Localization.Away a)] :
    ∃ n ∈ M, ∀ b : A, a * n ∣ b → IsMonoElement F (resA ξ b) := by
  let Aa := Localization.Away a
  let C := Aa ⊗[R] Aa
  let inl : Aa →ₐ[R] C := Algebra.TensorProduct.includeLeft
  let inr : Aa →ₐ[R] C := Algebra.TensorProduct.includeRight
  let ξ₁ := F.map (homR inl).op (resA ξ a)
  let ξ₂ := F.map (homR inr).op (resA ξ a)
  let mul : C →ₐ[R] Aa := Algebra.TensorProduct.lmul' R
  have hmul : Function.Surjective mul := fun x => ⟨x ⊗ₜ[R] 1, by
    change Algebra.TensorProduct.lmul' R (x ⊗ₜ[R] (1 : Aa)) = x
    rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]⟩
  let Δ : Set (PrimeSpectrum C) := Set.range (PrimeSpectrum.comap mul.toRingHom)
  have hΔ : IsClosed Δ := by
    change IsClosed (Set.range (PrimeSpectrum.comap mul.toRingHom))
    rw [range_comap_of_surjective _ _ hmul]
    exact PrimeSpectrum.isClosed_zeroLocus _
  let fl : A →+* C := inl.toRingHom.comp (algebraMap A Aa)
  let fr : A →+* C := inr.toRingHom.comp (algebraMap A Aa)
  let N : Submonoid C := M.map fl ⊔ M.map fr
  have hft : Algebra.FiniteType R Aa := Algebra.FiniteType.trans ‹_›
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) Aa)
  have : Algebra.FiniteType R C := Algebra.FiniteType.trans hft inferInstance
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  have hBad : IsOpen ({c | AgreeAt ξ₁ ξ₂ c} ∩ Δᶜ) :=
    (isOpen_agreeAt hZ h2 hrep ξ₁ ξ₂).inter hΔ.isOpen_compl
  have hG : ∀ c ∈ {c | AgreeAt ξ₁ ξ₂ c} ∩ Δᶜ, ¬ Disjoint (N : Set C) c.asIdeal := by
    rintro c ⟨hc, hcΔ⟩ hdisj
    apply hcΔ
    refine mem_range_comap_lmul e t ht j M ξ hξ a ha c hc fun m hm => ⟨fun h => ?_, fun h => ?_⟩
    · exact Set.disjoint_left.1 hdisj
        (Submonoid.mem_sup_left (Submonoid.mem_map_of_mem fl hm)) h
    · exact Set.disjoint_left.1 hdisj
        (Submonoid.mem_sup_right (Submonoid.mem_map_of_mem fr hm)) h
  obtain ⟨nC, hnC, hdisjC⟩ := exists_mem_basicOpen_disjoint N hBad hG
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submonoid.mem_sup.1 hnC
  obtain ⟨m₁, hm₁, rfl⟩ := hy₁
  obtain ⟨m₂, hm₂, rfl⟩ := hy₂
  refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, fun b hb => ?_⟩
  have hab : a ∣ b := dvd_trans (dvd_mul_right _ _) hb
  have hm₁b : m₁ ∣ b := dvd_trans (dvd_trans (dvd_mul_right m₁ m₂) (dvd_mul_left _ a)) hb
  have hm₂b : m₂ ∣ b := dvd_trans (dvd_trans (dvd_mul_left m₂ m₁) (dvd_mul_left _ a)) hb
  intro T h₁ h₂ heq
  let τ := homR (awayMapₐ (R := R) hab)
  have heq' : F.map (h₁ ≫ τ).op (resA ξ a) = F.map (h₂ ≫ τ).op (resA ξ a) := by
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, resA_awayMapₐ, heq]
  suffices hk : (h₁ ≫ τ).left = (h₂ ≫ τ).left by
    ext1
    rw [← cancel_mono τ.left]
    simpa only [Over.comp_left] using hk
  let q := Spec.map (CommRingCat.ofHom (algebraMap R Aa))
  have hdiag : pullback.diagonal q = Spec.map (CommRingCat.ofHom mul.toRingHom) ≫
      (pullbackSpecIso R Aa Aa).inv := diagonal_SpecMap _ _
  have : IsOpenImmersion (pullback.diagonal q) := by
    rw [hdiag]
    infer_instance
  have w : (h₁ ≫ τ).left ≫ q = (h₂ ≫ τ).left ≫ q :=
    (Over.w (h₁ ≫ τ)).trans (Over.w (h₂ ≫ τ)).symm
  apply eq_of_forall_mem_range_diagonal q _ _ w
  intro x
  let c : PrimeSpectrum C := (pullbackSpecIso R Aa Aa).hom (pullback.lift _ _ w x)
  have e₁ : (pullbackSpecIso R Aa Aa).hom ≫ Spec.map (CommRingCat.ofHom inl.toRingHom) =
      pullback.fst q q := pullbackSpecIso_hom_fst _ _ _
  have e₂ : (pullbackSpecIso R Aa Aa).hom ≫ Spec.map (CommRingCat.ofHom inr.toRingHom) =
      pullback.snd q q := pullbackSpecIso_hom_snd _ _ _
  have hfst : PrimeSpectrum.comap inl.toRingHom c = (h₁ ≫ τ).left x := by
    change (Spec.map (CommRingCat.ofHom inl.toRingHom))
      ((pullbackSpecIso R Aa Aa).hom (pullback.lift _ _ w x)) = _
    rw [← Scheme.Hom.comp_apply, e₁, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have hsnd : PrimeSpectrum.comap inr.toRingHom c = (h₂ ≫ τ).left x := by
    change (Spec.map (CommRingCat.ofHom inr.toRingHom))
      ((pullbackSpecIso R Aa Aa).hom (pullback.lift _ _ w x)) = _
    rw [← Scheme.Hom.comp_apply, e₂, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hc₁ : fl m₁ ∉ c.asIdeal := by
    intro hmem
    have hmem' : algebraMap A Aa m₁ ∈ (PrimeSpectrum.comap inl.toRingHom c).asIdeal := hmem
    rw [hfst, Over.comp_left, Scheme.Hom.comp_apply] at hmem'
    exact algebraMap_notMem_comap hab hm₁b (h₁.left x) hmem'
  have hc₂ : fr m₂ ∉ c.asIdeal := by
    intro hmem
    have hmem' : algebraMap A Aa m₂ ∈ (PrimeSpectrum.comap inr.toRingHom c).asIdeal := hmem
    rw [hsnd, Over.comp_left, Scheme.Hom.comp_apply] at hmem'
    exact algebraMap_notMem_comap hab hm₂b (h₂.left x) hmem'
  have hcD : c ∈ (PrimeSpectrum.basicOpen (fl m₁ * fr m₂) : Set (PrimeSpectrum C)) := by
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro hmem
    rcases c.isPrime.mem_or_mem hmem with h | h
    exacts [hc₁ h, hc₂ h]
  have hcE : AgreeAt ξ₁ ξ₂ c := by
    let ε := T.left.fromSpecResidueField x
    let f := ε ≫ T.hom
    let εx : Over.mk f ⟶ T := Over.homMk ε rfl
    let z : Over.mk f ⟶ ovR R C := Over.homMk (ε ≫ pullback.lift _ _ w ≫
      (pullbackSpecIso R Aa Aa).hom) (by
        change (ε ≫ pullback.lift _ _ w ≫ (pullbackSpecIso R Aa Aa).hom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R C)) = ε ≫ T.hom
        rw [Category.assoc, Category.assoc, pullbackSpecIso_hom_base, pullback.lift_fst_assoc]
        congr 1
        exact Over.w (h₁ ≫ τ))
    have hz₁ : z ≫ homR inl = εx ≫ (h₁ ≫ τ) := by
      ext1
      change (ε ≫ pullback.lift _ _ w ≫ (pullbackSpecIso R Aa Aa).hom) ≫
        Spec.map (CommRingCat.ofHom inl.toRingHom) = ε ≫ (h₁ ≫ τ).left
      rw [Category.assoc, Category.assoc, e₁, pullback.lift_fst]
    have hz₂ : z ≫ homR inr = εx ≫ (h₂ ≫ τ) := by
      ext1
      change (ε ≫ pullback.lift _ _ w ≫ (pullbackSpecIso R Aa Aa).hom) ≫
        Spec.map (CommRingCat.ofHom inr.toRingHom) = ε ≫ (h₂ ≫ τ).left
      rw [Category.assoc, Category.assoc, e₂, pullback.lift_snd]
    refine agreeAt_of_map_eq hF f z (fun x' => ?_) ?_
    · have hx' : ε x' = x := Scheme.fromSpecResidueField_apply x x'
      change (pullbackSpecIso R Aa Aa).hom (pullback.lift _ _ w (ε x')) = c
      rw [hx']
    · have e₃ : F.map z.op ξ₁ = F.map εx.op (F.map (h₁ ≫ τ).op (resA ξ a)) := by
        change F.map z.op (F.map (homR inl).op (resA ξ a)) = _
        rw [← Functor.map_comp_apply F (homR inl).op z.op, ← op_comp, hz₁, op_comp,
          Functor.map_comp_apply]
      have e₄ : F.map z.op ξ₂ = F.map εx.op (F.map (h₂ ≫ τ).op (resA ξ a)) := by
        change F.map z.op (F.map (homR inr).op (resA ξ a)) = _
        rw [← Functor.map_comp_apply F (homR inr).op z.op, ← op_comp, hz₂, op_comp,
          Functor.map_comp_apply]
      have e₅ : F.map εx.op (F.map (h₁ ≫ τ).op (resA ξ a)) =
          F.map εx.op (F.map (h₂ ≫ τ).op (resA ξ a)) := by rw [heq']
      exact e₃.trans (e₅.trans e₄.symm)
  have hcΔ : c ∈ Δ := by
    by_contra hn
    exact Set.disjoint_left.1 hdisjC hcD ⟨hcE, hn⟩
  obtain ⟨d, hd⟩ := hcΔ
  refine ⟨d, ?_⟩
  have h5 : (pullback.diagonal q) d =
      (pullbackSpecIso R Aa Aa).inv (Spec.map (CommRingCat.ofHom mul.toRingHom) d) := by
    rw [hdiag]
    exact Scheme.Hom.comp_apply _ _ _
  rw [h5]
  change (pullbackSpecIso R Aa Aa).inv (PrimeSpectrum.comap mul.toRingHom d) = _
  rw [hd, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
