import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusStep

/-! # Openness near a point over a prime that is not nilpotent

The locus of points `w` of `V(I)` at which `𝔍` vanishes in the stalk at level `c` is the
trace on `V(I)` of an open set (`exists_open_van`): it is the preimage, under the point
`Spec (R'/(𝔍 + I^(c+1))) ⟶ X_c` given by `ξ`, of the open set where finitely many generators of
`𝔍` have zero germ. With the inductive step `van_succ` this gives the open neighbourhood of
Murre's case (a) (`exists_open_of_not_le_nilradical`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'} [IsNoetherianRing R']

/-- The vanishing locus at level `c` is the trace of an open set on `V(I)`. -/
theorem exists_open_van (I : Ideal R')
    (Lvs : ∀ n : ℕ, Level F (Ideal.Quotient.mk (I ^ (n + 1))))
    (ξ : F.obj (op (chart R R' 𝔍))) (c : ℕ) :
    ∃ V : Set (Spec (CommRingCat.of (R' ⧸ 𝔍))), IsOpen V ∧
      ∀ (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) (hw : I ≤ primeOf 𝔍 w),
        haveI : Fact (I ≤ primeOf 𝔍 w) := ⟨hw⟩
        (w ∈ V ↔ VanN 𝔍 I Lvs ξ c w) := by
  have hle₁ : 𝔍 ≤ 𝔍 ⊔ I ^ (c + 1) := le_sup_left
  have hle₂ : I ^ (c + 1) ≤ 𝔍 ⊔ I ^ (c + 1) := le_sup_right
  let u := algHomOver (baseMap R R') (Ideal.Quotient.factorₐ R' hle₁)
  let ξc := F.map u.op ξ
  let tc : Spec (CommRingCat.of (R' ⧸ (𝔍 ⊔ I ^ (c + 1)))) ⟶
      Spec (CommRingCat.of (R' ⧸ I ^ (c + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle₂))
  have htc : tc ≫ levelMap R (Ideal.Quotient.mk (I ^ (c + 1))) =
      (algebraOver (baseMap R R') (R' ⧸ (𝔍 ⊔ I ^ (c + 1)))).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [specMap_ofHom_comp, specMap_ofHom_comp]
    rfl
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Spec (CommRingCat.of (R' ⧸ (𝔍 ⊔ I ^ (c + 1)))) ⟶ (Lvs c).X,
      Φ = ((Charts.elemEquiv (levelMap R (Ideal.Quotient.mk (I ^ (c + 1)))) (Lvs c).e
        (algebraOver (baseMap R R') (R' ⧸ (𝔍 ⊔ I ^ (c + 1)))) tc htc).symm ξc).left :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian 𝔍 : 𝔍.FG)
  have hG' : Ideal.span (G : Set R') = 𝔍 := hG
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Lvs c).X,
      S = ⋂ j ∈ G, {x | (structMap (Lvs c).q x).hom (Ideal.Quotient.mk _ j) = 0} := ⟨_, rfl⟩
  have hS : IsOpen S := by
    rw [hSdef]
    exact isOpen_biInter_finset fun j _ => isOpen_structMap_eq_zero _ _
  have hU : IsOpen (Φ ⁻¹' S) := hS.preimage Φ.continuous
  have hemb : Topology.IsInducing (PrimeSpectrum.comap (Ideal.Quotient.factor hle₁)) :=
    PrimeSpectrum.comap_isInducing_of_surjective _ _ (Ideal.Quotient.factor_surjective hle₁)
  obtain ⟨V, hVo, hV⟩ := hemb.isOpen_iff.1 hU
  refine ⟨V, hVo, fun w hw => ?_⟩
  have : Fact (I ≤ primeOf 𝔍 w) := ⟨hw⟩
  let d := nDatum R 𝔍 I c w
  let κ : R' ⧸ (𝔍 ⊔ I ^ (c + 1)) →+* Ln 𝔍 I c w :=
    Ideal.quotientMap _ (algebraMap R' (Ow 𝔍 w)) Ideal.le_comap_map
  have hk : Spec.map (CommRingCat.ofHom κ) ≫
      (algebraOver (baseMap R R') (R' ⧸ (𝔍 ⊔ I ^ (c + 1)))).hom = d.f := by
    change Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' _)) ≫
      baseMap R R' = Spec.map (CommRingCat.ofHom (algebraMap R' (Ln 𝔍 I c w))) ≫ baseMap R R'
    rw [← Category.assoc, specMap_ofHom_comp]
    rfl
  let k : Over.mk d.f ⟶ algebraOver (baseMap R R') (R' ⧸ (𝔍 ⊔ I ^ (c + 1))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom κ)) hk
  have hkt : k.left ≫ tc = Spec.map (CommRingCat.ofHom d.δ) := by
    change Spec.map (CommRingCat.ofHom κ) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle₂)) = _
    rw [specMap_ofHom_comp]
    congr 2
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl
  have hz : F.map k.op ξc = d.ζ ξ := by
    have hku : k ≫ u = homU d.ℓ d.f d.hf := by
      ext1
      change Spec.map (CommRingCat.ofHom κ) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorₐ R' hle₁ : _ →+* _)) =
        Spec.map (CommRingCat.ofHom d.ℓ)
      rw [specMap_ofHom_comp]
      congr 2
      apply Ideal.Quotient.ringHom_ext
      ext r
      rfl
    rw [LocalDatum.ζ, ← hku, op_comp, Functor.map_comp_apply]
  have hleft := d.left_of_map_eq ξ (Lvs c) tc htc ξc k hkt hz
  rw [← hΦ] at hleft
  have hpt : Φ (Spec.map (CommRingCat.ofHom κ) (closedPoint _)) = d.pt ξ (Lvs c) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun g => g (closedPoint (CommRingCat.of (Ln 𝔍 I c w)))) hleft)
  have hwb : PrimeSpectrum.comap (Ideal.Quotient.factor hle₁)
      (Spec.map (CommRingCat.ofHom κ) (closedPoint (CommRingCat.of (Ln 𝔍 I c w)))) = w := by
    apply PrimeSpectrum.ext
    change ((maximalIdeal (Ln 𝔍 I c w)).comap κ).comap (Ideal.Quotient.factor hle₁) = w.asIdeal
    rw [Ideal.comap_comap]
    convert d.comap_eq using 2
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl
  have h1 : w ∈ V ↔ Spec.map (CommRingCat.ofHom κ) (closedPoint (CommRingCat.of (Ln 𝔍 I c w))) ∈
      Φ ⁻¹' S :=
    (iff_of_eq (congrArg (· ∈ V) hwb)).symm.trans (Set.ext_iff.1 hV _)
  have h2 : Spec.map (CommRingCat.ofHom κ) (closedPoint (CommRingCat.of (Ln 𝔍 I c w))) ∈
      Φ ⁻¹' S ↔ d.pt ξ (Lvs c) ∈ S :=
    iff_of_eq (congrArg (· ∈ S) hpt)
  refine h1.trans (h2.trans ?_)
  rw [hSdef]
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h j hj
    have : Ideal.span (G : Set R') ≤
        RingHom.ker ((d.θ ξ (Lvs c)).hom.comp (Ideal.Quotient.mk _)) :=
      Ideal.span_le.2 fun j hj => RingHom.mem_ker.2 (h j (Finset.mem_coe.1 hj))
    rw [hG'] at this
    exact this hj
  · intro h j hj
    exact h j (hG' ▸ Ideal.subset_span (Finset.mem_coe.2 hj))

/-- Murre's case (a): near a point `y` of the étale locus whose prime in `R` is not
nilpotent, the étale locus contains the points of an open neighbourhood specializing `y`. -/
theorem exists_open_of_not_le_nilradical [Algebra.Etale R R'] (hF5 : NilpotentInjective F)
    (hquot : ∀ I : Ideal R, I ≠ ⊥ → UnramifiedRepresentable
      (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F))
    (ξ : F.obj (op (chart R R' 𝔍))) (y : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    (hy : InfinitesimallyEtaleAt F ξ y)
    (hp : ¬ y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) ≤ nilradical R) :
    ∃ V : Set (Spec (CommRingCat.of (R' ⧸ 𝔍))), IsOpen V ∧ y ∈ V ∧
      ∀ w ∈ V, y.asIdeal ≤ w.asIdeal → InfinitesimallyEtaleAt F ξ w := by
  obtain ⟨𝔭, h𝔭⟩ : ∃ 𝔭, 𝔭 = y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍)) := ⟨_, rfl⟩
  rw [← h𝔭] at hp
  let I := 𝔭.map (algebraMap R R')
  have hne : ∀ n : ℕ, 𝔭 ^ (n + 1) ≠ ⊥ := by
    intro n h
    apply hp
    intro x hx
    rw [mem_nilradical]
    refine ⟨n + 1, ?_⟩
    have := Ideal.pow_mem_pow hx (n + 1)
    rw [h] at this
    exact (Submodule.mem_bot _).1 this
  have Lvs : ∀ n : ℕ, Level F (Ideal.Quotient.mk (I ^ (n + 1))) := fun n =>
    (nonempty_level_quotient F hquot (𝔭 ^ (n + 1)) (hne n) _ (Ideal.map_pow _ _ _)).some
  have hIy : I ≤ primeOf 𝔍 y := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [h𝔭] at hr
    exact hr
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (𝔍 : Submodule R' R')
  have hAR : ∀ m ≥ c + 1, 𝔍 ⊓ I ^ m ≤ I * 𝔍 := by
    intro m hm
    have := hc m (by omega)
    simp only [Ideal.smul_eq_mul, Ideal.mul_top] at this
    rw [inf_comm, this]
    exact Ideal.mul_mono (Ideal.pow_le_self (by omega)) inf_le_right
  have key : ∀ (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) (hw : I ≤ primeOf 𝔍 w),
      (haveI : Fact (I ≤ primeOf 𝔍 w) := ⟨hw⟩; VanN 𝔍 I Lvs ξ c w) →
        InfinitesimallyEtaleAt F ξ w := by
    intro w hw hv
    have : Fact (I ≤ primeOf 𝔍 w) := ⟨hw⟩
    have hall : ∀ n ≥ c, VanN 𝔍 I Lvs ξ n w := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact hv
      | succ n hn ih => exact van_succ I Lvs ξ w c hAR n hn ih
    rw [infinitesimallyEtaleAt_iff hF5]
    intro A _ _ _ β
    exact killAt_of_quotient ξ w I hw β c fun n hn δ' =>
      (nDatum R 𝔍 I n w).killAt_of_van ξ (Lvs n) (hall n hn) A δ'
  obtain ⟨V, hVo, hV⟩ := exists_open_van I Lvs ξ c
  refine ⟨V, hVo, ?_, fun w hwV hyw => ?_⟩
  · have : Fact (I ≤ primeOf 𝔍 y) := ⟨hIy⟩
    apply (hV y hIy).2
    exact fun j hj => (nDatum R 𝔍 I c y).van_of_killAt ξ (Lvs c) hF5
      (fun A _ _ _ δ' => (infinitesimallyEtaleAt_iff hF5 ξ y).1 hy A _) j hj
  · have hIw : I ≤ primeOf 𝔍 w := hIy.trans (Ideal.comap_mono hyw)
    exact key w hIw ((hV w hIw).1 hwV)

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
