import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusGen

/-! # The étale locus of a closed subscheme of an étale scheme, with a given level

For Step 2a of Murre's induction (Bourbaki exp. 294). The Library's analysis of the étale
locus of `ξ ∈ F(Spec (R'/𝔍))`, for `R'` étale over `R`, uses a level `R' → O_w` at a point
`w` of `Spec (R'/𝔍)`, that is, a representing scheme of `F` over `Spec O_w`. Here the level
is an explicit argument, instead of being derived from representability of `F` over all the
local schemes of `Spec R`: generization (`infinitesimallyEtaleAt_of_le_of_level`), and the
criterion that it suffices to solve the lifting problems at `w` for the surjections
`O_w → A` onto local artinian rings (`infinitesimallyEtaleAt_of_killAt_surjective`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'}

omit [Algebra R R'] in
/-- A level `ρ : R' → D` from a representation of `F` over an open subscheme of `Spec R`
containing the image of `Spec D`. -/
lemma nonempty_level_of_range [Algebra R R'] {D : Type u} [CommRing D] (ρ : R' →+* D)
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (hU : UnramifiedRepresentable (baseChange j F))
    (hrange : Set.range (levelMap R ρ) ⊆ Set.range j) : Nonempty (Level F ρ) := by
  obtain ⟨f', hf'⟩ : ∃ f', f' ≫ j = levelMap R ρ :=
    ⟨IsOpenImmersion.lift j _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have h := LocalToGlobal.unramifiedRepresentable_of_iso
    (LocalToGlobal.baseChangeCompIso f' j F)
    (LocalToGlobal.unramifiedRepresentable_baseChange hU f')
  rw [hf'] at h
  obtain ⟨Y, q, ⟨e⟩, -, h₂, h₃⟩ := h
  exact ⟨{ X := Y, q := q, e := e, lft := h₂, fu := h₃ }⟩

variable [IsNoetherianRing R']

/-- The étale locus is stable under generization, for a given level at `w`. -/
theorem infinitesimallyEtaleAt_of_le_of_level (hF5 : NilpotentInjective F) [Algebra.Etale R R']
    (ξ : F.obj (op (chart R R' 𝔍))) {w y : Spec (CommRingCat.of (R' ⧸ 𝔍))}
    (Lv : Level F (algebraMap R' (Ow 𝔍 w)))
    (hw : InfinitesimallyEtaleAt F ξ w) (h : y.asIdeal ≤ w.asIdeal) :
    InfinitesimallyEtaleAt F ξ y := by
  rw [infinitesimallyEtaleAt_iff hF5] at hw ⊢
  have hvan := (wDatum R w).van_of_killAt ξ Lv hF5 (fun A _ _ _ δ' => hw A _)
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

/-- For a given level at `w`, it suffices to solve the lifting problems at `w` for the
surjections `O_w → A` onto local artinian rings. -/
theorem infinitesimallyEtaleAt_of_killAt_surjective (hF5 : NilpotentInjective F)
    [Algebra.Etale R R'] (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    (Lv : Level F (algebraMap R' (Ow 𝔍 w)))
    (H : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (δ' : Ow 𝔍 w →+* A), Function.Surjective δ' →
        KillAt ξ w A (δ'.comp (algebraMap R' (Ow 𝔍 w)))) :
    InfinitesimallyEtaleAt F ξ w := by
  let d := wDatum R w
  have : IsLocallyNoetherian Lv.X := LocallyOfFiniteType.isLocallyNoetherian Lv.q
  have hK : RingHom.ker (d.ψ ξ Lv).hom ≤
      (𝔍.map (algebraMap R' (Ow 𝔍 w))).map (d.θ ξ Lv).hom := by
    have := d.ker_ψ_le ξ Lv
    rwa [← Ideal.map_map] at this
  have hKm : (𝔍.map (algebraMap R' (Ow 𝔍 w))).map (d.θ ξ Lv).hom ≤
      maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv)) := by
    refine le_trans ?_ (d.ker_ψ_le_maximalIdeal ξ Lv)
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [Ideal.mem_comap, RingHom.mem_ker, d.ψ_θ_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ho
  have hvan : ∀ j ∈ 𝔍, (d.θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j) = 0 := by
    intro j hj
    have hmem : ∀ N : ℕ, (d.θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j) ∈
        maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv)) ^ (N + 1) := by
      intro N
      obtain ⟨I, hI⟩ : ∃ I, I = maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv)) ^ (N + 1) :=
        ⟨_, rfl⟩
      rw [← hI]
      have hItop : I ≠ ⊤ := by
        rw [hI]
        exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
          (Ideal.pow_le_self N.succ_ne_zero)
      have : Nontrivial (Lv.X.presheaf.stalk (d.pt ξ Lv) ⧸ I) :=
        Ideal.Quotient.nontrivial_iff.2 hItop
      have : IsLocalRing (Lv.X.presheaf.stalk (d.pt ξ Lv) ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hmax : (maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv))).map (Ideal.Quotient.mk I) =
          maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv) ⧸ I) := by
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        have : IsLocalHom (Ideal.Quotient.mk I) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        simp [sup_eq_left.mpr (le_maximalIdeal hItop)]
      have : IsArtinianRing (Lv.X.presheaf.stalk (d.pt ξ Lv) ⧸ I) := by
        rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
        refine ⟨N + 1, ?_⟩
        rw [← hmax, ← Ideal.map_pow, ← hI, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
          Ideal.mk_ker]
      let χ : Lv.X.presheaf.stalk (d.pt ξ Lv) ⟶
          CommRingCat.of (Lv.X.presheaf.stalk (d.pt ξ Lv) ⧸ I) :=
        CommRingCat.ofHom (Ideal.Quotient.mk I)
      have : IsLocalHom χ.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have hsurj : Function.Surjective (d.θ ξ Lv ≫ χ).hom := by
        refine surjective_of_isNilpotent_map _ (𝔍.map (algebraMap R' (Ow 𝔍 w))) ?_ ?_
        · refine ⟨N + 1, ?_⟩
          rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker]
          intro o ho
          rw [RingHom.mem_ker]
          change Ideal.Quotient.mk I ((d.θ ξ Lv).hom o) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, hI]
          have : (d.θ ξ Lv).hom o ∈ ((𝔍.map (algebraMap R' (Ow 𝔍 w))).map
              (d.θ ξ Lv).hom) ^ (N + 1) := by
            rw [← Ideal.map_pow]
            exact Ideal.mem_map_of_mem _ ho
          exact Ideal.pow_right_mono hKm _ this
        · intro b
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
          obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective ((d.ψ ξ Lv).hom s)
          refine ⟨o, ?_⟩
          have hs : s - (d.θ ξ Lv).hom o ∈
              (𝔍.map (algebraMap R' (Ow 𝔍 w))).map (d.θ ξ Lv).hom := by
            refine hK ?_
            rw [RingHom.mem_ker, map_sub, d.ψ_θ_apply, ← ho]
            exact sub_eq_zero.2 rfl
          have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hs
          rw [Ideal.map_map, map_sub] at this
          exact this
      have := (d.stalk_kill ξ Lv hF5 χ (H _ _ hsurj)).1 j hj
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have : (d.θ ξ Lv).hom (algebraMap R' (Ow 𝔍 w) j) ∈
        (⨅ N : ℕ, maximalIdeal (Lv.X.presheaf.stalk (d.pt ξ Lv)) ^ N) := by
      rw [Ideal.mem_iInf]
      intro N
      cases N with
      | zero => simp
      | succ N => exact hmem N
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at this
    exact this
  rw [infinitesimallyEtaleAt_iff hF5]
  intro A _ _ _ β
  exact killAt_of_localization ξ w (primeOf 𝔍 w) le_rfl β
    (fun δ' => d.killAt_of_van ξ Lv hvan A δ')

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
