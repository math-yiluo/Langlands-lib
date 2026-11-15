import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusStd

/-! # Stability of the étale locus under generization, and the case of a nilpotent `𝔍 O_w`

For a point `w` of `Spec (R'/𝔍)` we use the level `R' → O_w` and the local data
`O_w/𝔍O_w` at `w` (`wDatum`) and `O_y/𝔍O_y` at a generization `y` of `w` (`genDatum`).
The point of the representing scheme given by `y` is a generization of the one given by `w`,
so vanishing of `𝔍` in the stalk passes from `w` to `y`: the set of points at which `ξ` is
infinitesimally étale is stable under generization
(`infinitesimallyEtaleAt_of_le`).

If `𝔍 O_w` is nilpotent and the restriction of `ξ` to `Spec (O_w/𝔍O_w)` lifts to no larger
closed subscheme of `Spec O_w`, then `O_w → 𝒪_{X,x}` is surjective with kernel `𝔍 O_w`, and
`ξ` is infinitesimally étale at `w` (`infinitesimallyEtaleAt_of_noLargerLift`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

/-- A ring map that is surjective modulo the extension of an ideal `𝔦`, where this extension
is nilpotent, is surjective. -/
lemma surjective_of_isNilpotent_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (𝔦 : Ideal A) (h𝔦 : IsNilpotent (𝔦.map φ)) (h : ∀ b, ∃ a, b - φ a ∈ 𝔦.map φ) :
    Function.Surjective φ := by
  let := φ.toAlgebra
  obtain ⟨k, hk⟩ := h𝔦
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have h1 : (⊤ : Submodule A B) ≤ N ⊔ 𝔦 • ⊤ := by
    intro b _
    obtain ⟨a, ha⟩ := h b
    have hb : b = φ a + (b - φ a) := by ring
    rw [hb]
    refine Submodule.add_mem_sup ⟨a, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact ha
  have h2 : ∀ m : ℕ, (⊤ : Submodule A B) ≤ N ⊔ 𝔦 ^ m • ⊤ := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_sup_right
    | succ m ih =>
      calc (⊤ : Submodule A B) ≤ N ⊔ 𝔦 ^ m • ⊤ := ih
        _ ≤ N ⊔ 𝔦 ^ m • (N ⊔ 𝔦 • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (𝔦 ^ m • N ⊔ 𝔦 ^ (m + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ 𝔦 ^ (m + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  have h3 : (𝔦 ^ k • ⊤ : Submodule A B) = ⊥ := by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    change Submodule.restrictScalars A (Ideal.map φ 𝔦 ^ k) = ⊥
    rw [hk, Ideal.zero_eq_bot, Submodule.restrictScalars_eq_bot_iff]
  intro b
  have := h2 k (Submodule.mem_top (x := b))
  rw [h3, sup_bot_eq] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'}

section Data

variable (𝔍) in
/-- The local ring `O_w/𝔍O_w`. -/
abbrev Lw (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : Type u :=
  Ow 𝔍 w ⧸ 𝔍.map (algebraMap R' (Ow 𝔍 w))

instance (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : IsLocalRing (Lw 𝔍 w) :=
  isLocalRing_std (𝔞 := ⊥) bot_le (Ideal.map_mono le_sup_left)

/-- The map `O_w → O_y` for a generization `y` of `w`. -/
def genMap (w y : Spec (CommRingCat.of (R' ⧸ 𝔍))) (h : y.asIdeal ≤ w.asIdeal) :
    Ow 𝔍 w →+* Ow 𝔍 y :=
  IsLocalization.lift (M := (primeOf 𝔍 w).primeCompl) (S := Ow 𝔍 w)
    (g := algebraMap R' (Ow 𝔍 y)) fun s =>
      IsLocalization.map_units (Ow 𝔍 y)
        (⟨s, fun hs => s.2 (Ideal.comap_mono h hs)⟩ : (primeOf 𝔍 y).primeCompl)

lemma genMap_comp (w y : Spec (CommRingCat.of (R' ⧸ 𝔍))) (h : y.asIdeal ≤ w.asIdeal) :
    (genMap w y h).comp (algebraMap R' (Ow 𝔍 w)) = algebraMap R' (Ow 𝔍 y) :=
  IsLocalization.lift_comp _

lemma ringHom_ext_Ow (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) (C : Type u) [CommRing C]
    (δ₁ δ₂ : Ow 𝔍 w →+* C)
    (h : δ₁.comp (algebraMap R' (Ow 𝔍 w)) = δ₂.comp (algebraMap R' (Ow 𝔍 w))) : δ₁ = δ₂ :=
  IsLocalization.ringHom_ext (primeOf 𝔍 w).primeCompl h

variable (R) in
/-- The local datum `O_w/𝔍O_w` at `w` for the level `R' → O_w`. -/
def wDatum (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) :
    LocalDatum R 𝔍 (algebraMap R' (Ow 𝔍 w)) w (Lw 𝔍 w) :=
  stdDatum (ρ := algebraMap R' (Ow 𝔍 w)) (w := w) (ringHom_ext_Ow w) ⊥ bot_le
    (𝔍.map (algebraMap R' (Ow 𝔍 w))) le_rfl (Ideal.map_mono le_sup_left)
    (Ideal.Quotient.mk _) rfl
    (Spec.map (CommRingCat.ofHom (algebraMap R' (Lw 𝔍 w))) ≫ baseMap R R')
    (by rw [specMap_ofHom_comp]; rfl)

variable (R) in
/-- The local datum `O_y/𝔍O_y` at a generization `y` of `w` for the level `R' → O_w`. -/
def genDatum (w y : Spec (CommRingCat.of (R' ⧸ 𝔍))) (h : y.asIdeal ≤ w.asIdeal) :
    LocalDatum R 𝔍 (algebraMap R' (Ow 𝔍 w)) y (Lw 𝔍 y) :=
  stdDatum (ρ := algebraMap R' (Ow 𝔍 w)) (w := y) (ringHom_ext_Ow w) ⊥ bot_le
    (𝔍.map (algebraMap R' (Ow 𝔍 y))) le_rfl (Ideal.map_mono le_sup_left)
    ((Ideal.Quotient.mk _).comp (genMap w y h))
    (by rw [RingHom.comp_assoc, genMap_comp])
    (Spec.map (CommRingCat.ofHom (algebraMap R' (Lw 𝔍 y))) ≫ baseMap R R')
    (by rw [specMap_ofHom_comp]; rfl)

end Data

section Generization

variable [IsNoetherianRing R']

/-- The étale locus is stable under generization. -/
theorem infinitesimallyEtaleAt_of_le (hF5 : NilpotentInjective F) [Algebra.Etale R R']
    (hloc : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    (ξ : F.obj (op (chart R R' 𝔍))) {w y : Spec (CommRingCat.of (R' ⧸ 𝔍))}
    (hw : InfinitesimallyEtaleAt F ξ w) (h : y.asIdeal ≤ w.asIdeal) :
    InfinitesimallyEtaleAt F ξ y := by
  obtain ⟨Lv⟩ := nonempty_level_localization F hloc (primeOf 𝔍 w)
  rw [infinitesimallyEtaleAt_iff hF5] at hw ⊢
  have hvan := (wDatum R w).van_of_killAt ξ Lv hF5 (fun A _ _ _ δ' => hw A _)
  -- the map `κ : O_w/𝔍O_w → O_y/𝔍O_y`
  have hle : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ≤
      (𝔍.map (algebraMap R' (Ow 𝔍 y))).comap (genMap w y h) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, genMap_comp]
  let κ : Lw 𝔍 w →+* Lw 𝔍 y := Ideal.quotientMap _ (genMap w y h) hle
  have hκ : ∀ r : R', κ (algebraMap R' (Lw 𝔍 w) r) = algebraMap R' (Lw 𝔍 y) r := fun r =>
    congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (genMap_comp w y h) r)
  have hk : Spec.map (CommRingCat.ofHom κ) ≫ (wDatum R w).f = (genDatum R w y h).f := by
    change Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (Lw 𝔍 w)))
      ≫ baseMap R R' = Spec.map (CommRingCat.ofHom (algebraMap R' (Lw 𝔍 y))) ≫ baseMap R R'
    rw [← Category.assoc, specMap_ofHom_comp]
    congr 3
    ext r
    exact hκ r
  let k : Over.mk (genDatum R w y h).f ⟶ Over.mk (wDatum R w).f :=
    Over.homMk (Spec.map (CommRingCat.ofHom κ)) hk
  have hku : k ≫ homU (wDatum R w).ℓ (wDatum R w).f (wDatum R w).hf =
      homU (genDatum R w y h).ℓ (genDatum R w y h).f (genDatum R w y h).hf := by
    ext1
    change Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom (wDatum R w).ℓ) =
      Spec.map (CommRingCat.ofHom (genDatum R w y h).ℓ)
    rw [specMap_ofHom_comp]
    congr 2
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact hκ r
  have ht : (Spec.map (CommRingCat.ofHom κ) ≫
      Spec.map (CommRingCat.ofHom (wDatum R w).δ)) ≫ levelMap R (algebraMap R' (Ow 𝔍 w)) =
      (Over.mk (genDatum R w y h).f).hom := by
    rw [Category.assoc, (wDatum R w).hT]
    exact hk
  have e1 := (wDatum R w).map_ζ ξ Lv k _ ht rfl
  have e2 : F.map k.op ((wDatum R w).ζ ξ) = (genDatum R w y h).ζ ξ := by
    rw [LocalDatum.ζ, LocalDatum.ζ, ← Functor.map_comp_apply, ← op_comp, hku]
  have e3 : (genDatum R w y h).ζ ξ = Charts.elemEquiv _ Lv.e _ _ (genDatum R w y h).hT
      ((genDatum R w y h).mor ξ Lv) := (Equiv.apply_symm_apply _ _).symm
  have htt : Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom (wDatum R w).δ) =
      Spec.map (CommRingCat.ofHom (genDatum R w y h).δ) := by
    rw [specMap_ofHom_comp]
    congr 2
  have hleft := left_eq_of_elemEquiv_eq _ Lv.e ht (genDatum R w y h).hT htt _ _
    (e1.symm.trans (e2.trans e3))
  replace hleft : Spec.map (CommRingCat.ofHom κ) ≫ ((wDatum R w).mor ξ Lv).left =
      ((genDatum R w y h).mor ξ Lv).left := hleft
  have hpt : (genDatum R w y h).pt ξ Lv =
      ((wDatum R w).mor ξ Lv).left (Spec.map (CommRingCat.ofHom κ) (closedPoint _)) :=
    (congrArg (fun g => g (closedPoint (CommRingCat.of (Lw 𝔍 y)))) hleft).symm.trans
      (Scheme.Hom.comp_apply _ _ _)
  have hspec : (genDatum R w y h).pt ξ Lv ⤳ (wDatum R w).pt ξ Lv := by
    rw [hpt]
    exact (specializes_closedPoint _).map ((wDatum R w).mor ξ Lv).left.continuous
  have hvan' : ∀ j ∈ 𝔍, ((genDatum R w y h).θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j) = 0 := by
    intro j hj
    rw [LocalDatum.θ, ← structMap_stalkSpecializes Lv.q hspec]
    change (Lv.X.presheaf.stalkSpecializes hspec).hom
      (((wDatum R w).θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j)) = 0
    rw [hvan j hj, map_zero]
  intro A _ _ _ β
  exact killAt_of_localization ξ y (primeOf 𝔍 w) (Ideal.comap_mono h) β
    (fun δ' => (genDatum R w y h).killAt_of_van ξ Lv hvan' A δ')

end Generization

section NoLargerLift

variable [IsNoetherianRing R']

/-- If `𝔍 O_w` is nilpotent and the restriction of `ξ` to `Spec (O_w/𝔍O_w)` lifts to no larger
closed subscheme of `Spec O_w`, then `ξ` is infinitesimally étale at `w`. -/
theorem infinitesimallyEtaleAt_of_noLargerLift (hF5 : NilpotentInjective F) [Algebra.Etale R R']
    (hloc : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F))
    (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    (hnil : IsNilpotent (𝔍.map (algebraMap R' (Ow 𝔍 w))))
    (hNL : NoLargerLift (Ow 𝔍 w) ξ) : InfinitesimallyEtaleAt F ξ w := by
  obtain ⟨Lv⟩ := nonempty_level_localization F hloc (primeOf 𝔍 w)
  let d := wDatum R w
  have hψθ : ∀ o, (d.ψ ξ Lv).hom ((d.θ ξ Lv).hom o) =
      Ideal.Quotient.mk (𝔍.map (algebraMap R' (Ow 𝔍 w))) o :=
    fun o => d.ψ_θ_apply ξ Lv o
  have hK : RingHom.ker (d.ψ ξ Lv).hom ≤
      (𝔍.map (algebraMap R' (Ow 𝔍 w))).map (d.θ ξ Lv).hom := by
    have := d.ker_ψ_le ξ Lv
    rwa [← Ideal.map_map] at this
  have hsurj : Function.Surjective (d.θ ξ Lv).hom := by
    refine surjective_of_isNilpotent_map _ (𝔍.map (algebraMap R' (Ow 𝔍 w))) ?_ ?_
    · obtain ⟨k, hk⟩ := hnil
      refine ⟨k, ?_⟩
      rw [← Ideal.map_pow, hk, Ideal.zero_eq_bot, Ideal.map_bot]
      exact Ideal.zero_eq_bot.symm
    · intro b
      obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective ((d.ψ ξ Lv).hom b)
      refine ⟨o, hK ?_⟩
      rw [RingHom.mem_ker, map_sub, hψθ, ho, sub_self]
  have hQle : RingHom.ker (d.θ ξ Lv).hom ≤ 𝔍.map (algebraMap R' (Ow 𝔍 w)) := by
    intro o ho
    have := hψθ o
    rw [RingHom.mem_ker.1 ho, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  obtain ⟨φe, hφe⟩ : ∃ φe : Lv.X.presheaf.stalk (d.pt ξ Lv) ⟶
      CommRingCat.of (Ow 𝔍 w ⧸ RingHom.ker (d.θ ξ Lv).hom),
      ∀ o, φe.hom ((d.θ ξ Lv).hom o) = Ideal.Quotient.mk _ o :=
    ⟨CommRingCat.ofHom ((RingHom.quotientKerEquivOfSurjective hsurj).symm :
      Lv.X.presheaf.stalk (d.pt ξ Lv) →+* Ow 𝔍 w ⧸ RingHom.ker (d.θ ξ Lv).hom),
      fun o => RingHom.quotientKerEquivOfSurjective_symm_apply hsurj o⟩
  have hθe : d.θ ξ Lv ≫ φe =
      CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (d.θ ξ Lv).hom)) := by
    ext o
    exact hφe o
  have hh : (Spec.map φe ≫ Lv.X.fromSpecStalk (d.pt ξ Lv)) ≫ Lv.q =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (d.θ ξ Lv).hom))) := by
    rw [Category.assoc, ← specMap_structMap, ← Spec.map_comp]
    exact congrArg Spec.map hθe
  have ht : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (d.θ ξ Lv).hom))) ≫
      levelMap R (algebraMap R' (Ow 𝔍 w)) =
      (algebraOver (baseMap R R') (Ow 𝔍 w ⧸ RingHom.ker (d.θ ξ Lv).hom)).hom := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap R' _)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R'))
    rw [levelMap, specMap_ofHom_comp, specMap_ofHom_comp]
  let a₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (RingHom.ker (d.θ ξ Lv).hom)))) ⟶ Over.mk Lv.q := Over.homMk _ hh
  let η := Charts.elemEquiv (levelMap R (algebraMap R' (Ow 𝔍 w))) Lv.e
    (algebraOver (baseMap R R') (Ow 𝔍 w ⧸ RingHom.ker (d.θ ξ Lv).hom))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (d.θ ξ Lv).hom)))) ht a₀
  let fac := algHomOver (baseMap R R') (Ideal.Quotient.factorₐ R' hQle)
  have ht₁ : (fac.left ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (RingHom.ker (d.θ ξ Lv).hom)))) ≫ levelMap R (algebraMap R' (Ow 𝔍 w)) =
      (algebraOver (baseMap R R') (Ow 𝔍 w ⧸ 𝔍.map (algebraMap R' (Ow 𝔍 w)))).hom := by
    rw [Category.assoc, ht]
    exact Over.w fac
  have claim : F.map fac.op η = restrictQuotient (Ow 𝔍 w) ξ := by
    have hr : restrictQuotient (Ow 𝔍 w) ξ = d.ζ ξ := rfl
    rw [hr, elemEquiv_naturality' (levelMap R _) Lv.e fac _ _ ht₁ ht rfl a₀,
      show d.ζ ξ = Charts.elemEquiv _ Lv.e _ _ d.hT (d.mor ξ Lv) from
        (Equiv.apply_symm_apply _ _).symm]
    apply elemEquiv_congr
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorₐ R' hQle : _ →+* _)) ≫
      Spec.map φe ≫ Lv.X.fromSpecStalk (d.pt ξ Lv) = (d.mor ξ Lv).left
    rw [LocalDatum.mor_left, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    obtain ⟨o, rfl⟩ := hsurj b
    change (Ideal.Quotient.factorₐ R' hQle) (φe.hom ((d.θ ξ Lv).hom o)) =
      (d.ψ ξ Lv).hom ((d.θ ξ Lv).hom o)
    rw [hφe, hψθ]
    rfl
  have hQeq : RingHom.ker (d.θ ξ Lv).hom = 𝔍.map (algebraMap R' (Ow 𝔍 w)) := by
    by_contra hne
    exact hNL _ (lt_of_le_of_ne hQle hne) η claim
  have hvan : ∀ j ∈ 𝔍, (d.θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j) = 0 := fun j hj => by
    have : algebraMap R' (Ow 𝔍 w) j ∈ RingHom.ker (d.θ ξ Lv).hom := by
      rw [hQeq]
      exact Ideal.mem_map_of_mem _ hj
    exact this
  rw [infinitesimallyEtaleAt_iff hF5]
  intro A _ _ _ β
  exact killAt_of_localization ξ w (primeOf 𝔍 w) le_rfl β
    (fun δ' => d.killAt_of_van ξ Lv hvan A δ')

end NoLargerLift

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
