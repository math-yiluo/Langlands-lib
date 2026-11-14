import Langlands.AlgebraicGeometry.Picard.BaseChangeMaps
import Langlands.AlgebraicGeometry.IdealSheafGluing
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Gluing ideal sheaves on `X ×_R G` from natural families on affine points of `G` -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) {G : Scheme.{u}}
  (p : G ⟶ Spec (.of R))

lemma ptMap_congr {B : Type u} [CommRing B] [Algebra R B] {k k' : Spec (.of B) ⟶ G}
    (h : k = k') (hk : k ≫ p = specMap R B) (hk' : k' ≫ p = specMap R B) :
    ptMap π p k hk = ptMap π p k' hk' := by
  subst h; rfl

instance {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G) [IsOpenImmersion k]
    (hk : k ≫ p = specMap R B) : IsOpenImmersion (ptMap π p k hk) := by
  unfold ptMap
  infer_instance

lemma range_ptMap {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G)
    (hk : k ≫ p = specMap R B) :
    Set.range (ptMap π p k hk) = pullback.snd π p ⁻¹' Set.range k := by
  rw [ptMap, Scheme.Pullback.range_map]
  simp

lemma ptMap_snd {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G)
    (hk : k ≫ p = specMap R B) :
    ptMap π p k hk ≫ pullback.snd π p = pullback.snd π (specMap R B) ≫ k := by
  simp [ptMap]

/-- The restriction from an affine open to a smaller one, as an algebra map over `R`. -/
def resAlgHom {O O' : G.affineOpens} (h : O'.1 ≤ O.1) :
    letI := affAlg p O; letI := affAlg p O'
    Γ(G, O.1) →ₐ[R] Γ(G, O'.1) :=
  letI := affAlg p O; letI := affAlg p O'
  { (G.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => by
      change (G.presheaf.map (homOfLE h).op) ((p.appLE ⊤ O.1 le_top)
        ((Scheme.ΓSpecIso (.of R)).inv r)) = (p.appLE ⊤ O'.1 le_top)
        ((Scheme.ΓSpecIso (.of R)).inv r)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] }

lemma specMap_resAlgHom {O O' : G.affineOpens} (h : O'.1 ≤ O.1) :
    letI := affAlg p O; letI := affAlg p O'
    Spec.map (CommRingCat.ofHom (resAlgHom p h).toRingHom) ≫ (affPt O) = (affPt O') := by
  letI := affAlg p O; letI := affAlg p O'
  have := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 G) O.2 O'.2 h
  rw [Category.comp_id] at this
  unfold affPt
  rw [← this]
  congr 2

/-- Ideal sheaves on the base changes `X_B` along the `B`-points of `G` satisfying a predicate
stable under base change, natural in the point, with the predicate holding on an affine open
cover of `G`. -/
structure PointIdeals where
  /-- The admissible points. -/
  P : ∀ {B : Type u} [CommRing B] [Algebra R B], (Spec (.of B) ⟶ G) → Prop
  /-- The ideal sheaf attached to an admissible point. -/
  F : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G),
    k ≫ p = specMap R B → P k → (pullback π (specMap R B)).IdealSheafData
  P_comp : ∀ {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ G),
    P k → P (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k)
  F_comp : ∀ {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ G) (hk : k ≫ p = specMap R B) (hP : P k),
    F (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k)
        (by rw [Category.assoc, hk, specMap_comp]) (P_comp φ k hP) =
      (F k hk hP).comap (bcMap (π := π) B' φ)
  cover : ∀ z : G, ∃ O : G.affineOpens, z ∈ O.1 ∧ @P Γ(G, O.1) _ (affAlg p O) (affPt O)

namespace PointIdeals

variable {π p} (D : PointIdeals π p)

lemma F_congr {B : Type u} [CommRing B] [Algebra R B] {k k' : Spec (.of B) ⟶ G} (h : k = k')
    (hk : k ≫ p = specMap R B) (hk' : k' ≫ p = specMap R B) (hP : D.P k) (hP' : D.P k') :
    D.F k hk hP = D.F k' hk' hP' := by
  subst h; rfl

/-- The admissible affine opens. -/
abbrev Adm := {O : G.affineOpens // @D.P Γ(G, O.1) _ (affAlg p O) (affPt O)}

/-- The base change along an admissible affine open. -/
abbrev piece (O : D.Adm) : Scheme.{u} :=
  @pullback _ _ _ _ _ π (@specMap R Γ(G, O.1.1) _ _ (affAlg p O.1)) _

/-- Its inclusion. -/
abbrev pieceι (O : D.Adm) : D.piece O ⟶ pullback π p :=
  @ptMap R _ X π G p Γ(G, O.1.1) _ (affAlg p O.1) (affPt O.1) (affPt_comp p O.1)

/-- The ideal on a piece. -/
abbrev pieceIdeal (O : D.Adm) : (D.piece O).IdealSheafData :=
  @F R _ X π G p D Γ(G, O.1.1) _ (affAlg p O.1) (affPt O.1) (affPt_comp p O.1) O.2

lemma adm_of_le (O : D.Adm) (O'' : G.affineOpens) (h : O''.1 ≤ O.1.1) :
    @D.P Γ(G, O''.1) _ (affAlg p O'') (affPt O'') := by
  letI := affAlg p O.1; letI := affAlg p O''
  have := D.P_comp (resAlgHom p h) _ O.2
  rwa [specMap_resAlgHom] at this

/-- **Ideals on pieces are compatible with restriction to smaller affine opens.** -/
lemma comap_pieceIdeal_of_factor (O : D.Adm) (O'' : G.affineOpens) (h : O''.1 ≤ O.1.1)
    {V : Scheme.{u}} (a : V ⟶ D.piece O) (a'' : V ⟶ D.piece ⟨O'', D.adm_of_le O O'' h⟩)
    (ha : a'' ≫ D.pieceι ⟨O'', D.adm_of_le O O'' h⟩ = a ≫ D.pieceι O) :
    (D.pieceIdeal O).comap a = (D.pieceIdeal ⟨O'', D.adm_of_le O O'' h⟩).comap a'' := by
  letI := affAlg p O.1; letI := affAlg p O''
  have hfac : a'' ≫ bcMap (π := π) Γ(G, O'') (resAlgHom p h) = a := by
    rw [← cancel_mono (D.pieceι O), Category.assoc, bcMap_ptMap, ← ha]
    congr 1
    exact ptMap_congr π p (specMap_resAlgHom p h) _ _
  rw [← hfac, Scheme.IdealSheafData.comap_comp]
  congr 1
  rw [← D.F_comp]
  exact D.F_congr (specMap_resAlgHom p h) _ _ _ _

lemma range_pieceι (O : D.Adm) :
    Set.range (D.pieceι O) = pullback.snd π p ⁻¹' (O.1.1 : Set G) := by
  rw [range_ptMap]
  exact congrArg (fun s => (pullback.snd π p).base ⁻¹' s) (range_affPt O.1)

/-- The admissible pieces form an open cover. -/
def openCover : (pullback π p).OpenCover :=
  Scheme.Cover.mkOfCovers D.Adm D.piece D.pieceι (fun z => by
    obtain ⟨O, hzO, hP⟩ := D.cover ((pullback.snd π p).base z)
    have : z ∈ Set.range (D.pieceι ⟨O, hP⟩) := by
      rw [range_pieceι]; exact hzO
    obtain ⟨y, hy⟩ := this
    exact ⟨⟨O, hP⟩, y, hy⟩) (fun _ => inferInstance)

/-- A morphism into `X ×_R G` whose second component lands in an admissible affine open factors
through the corresponding piece. -/
lemma exists_lift_piece (O : D.Adm) {V : Scheme.{u}} (c : V ⟶ pullback π p)
    (hc : ∀ v, (c ≫ pullback.snd π p).base v ∈ O.1.1) :
    ∃ a : V ⟶ D.piece O, a ≫ D.pieceι O = c := by
  have hr : Set.range c ⊆ Set.range (D.pieceι O) := by
    rw [range_pieceι]
    rintro _ ⟨v, rfl⟩
    exact hc v
  exact ⟨IsOpenImmersion.lift _ c hr, IsOpenImmersion.lift_fac _ _ _⟩

lemma snd_mem_of_factor (O : D.Adm) {V : Scheme.{u}} (a : V ⟶ D.piece O) (v : V) :
    (a ≫ D.pieceι O ≫ pullback.snd π p).base v ∈ O.1.1 := by
  rw [ptMap_snd]
  exact (range_affPt O.1).subset ⟨(a ≫ pullback.snd _ _).base v, rfl⟩

/-- **The compatibility condition for gluing.** -/
lemma compat ⦃O O' : D.Adm⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ D.piece O) (b : V ⟶ D.piece O')
    (hab : a ≫ D.pieceι O = b ≫ D.pieceι O') :
    (D.pieceIdeal O).comap a = (D.pieceIdeal O').comap b := by
  let c := a ≫ D.pieceι O
  let Us : {O'' : G.affineOpens // O''.1 ≤ O.1.1 ⊓ O'.1.1} → V.Opens :=
    fun O'' => (c ≫ pullback.snd π p) ⁻¹ᵁ O''.1.1
  refine Langlands.AlgebraicGeometry.IdealSheafGluing.eq_of_comap_eq Us ?_ fun O'' => ?_
  · refine top_le_iff.mp fun v _ => ?_
    have h1 : (c ≫ pullback.snd π p).base v ∈ O.1.1 := by
      have := D.snd_mem_of_factor O a v
      simpa [c] using this
    have h2 : (c ≫ pullback.snd π p).base v ∈ O'.1.1 := by
      have := D.snd_mem_of_factor O' b v
      simpa [c, hab] using this
    obtain ⟨_, ⟨W, hW, rfl⟩, hvW, hWOO⟩ :=
      G.isBasis_affineOpens.exists_subset_of_mem_open (show _ ∈ O.1.1 ⊓ O'.1.1 from ⟨h1, h2⟩)
        (O.1.1 ⊓ O'.1.1).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWOO⟩, hvW⟩
  · obtain ⟨a'', ha''⟩ := D.exists_lift_piece ⟨O''.1, D.adm_of_le O O''.1
      (O''.2.trans inf_le_left)⟩ ((Us O'').ι ≫ c) fun v => v.2
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      D.comap_pieceIdeal_of_factor O O''.1 (O''.2.trans inf_le_left) ((Us O'').ι ≫ a) a''
        (by rw [ha'', Category.assoc]),
      D.comap_pieceIdeal_of_factor O' O''.1 (O''.2.trans inf_le_right) ((Us O'').ι ≫ b) a''
        (by
          rw [ha'']
          show (Us O'').ι ≫ a ≫ D.pieceι O = ((Us O'').ι ≫ b) ≫ D.pieceι O'
          rw [hab, Category.assoc])]

/-- **The glued ideal sheaf.** -/
theorem exists_glued : ∃ W : (pullback π p).IdealSheafData,
    ∀ O : D.Adm, W.comap (D.pieceι O) = D.pieceIdeal O :=
  Scheme.IdealSheafData.exists_comap_eq_of_openCover D.openCover D.pieceIdeal
    (fun _ _ _ a b hab => D.compat a b hab)

variable {W : (pullback π p).IdealSheafData}
  (hW : ∀ O : D.Adm, W.comap (D.pieceι O) = D.pieceIdeal O)
include hW

/-- The glued ideal on a point factoring through an admissible affine open. -/
lemma comap_ptMap_of_factor {B : Type u} [CommRing B] [Algebra R B] (O : D.Adm)
    (ψ : (letI := affAlg p O.1; Γ(G, O.1.1) →ₐ[R] B)) (k : Spec (.of B) ⟶ G)
    (hψ : (letI := affAlg p O.1; Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (affPt O.1) = k))
    (hk : k ≫ p = specMap R B) (hP : D.P k) :
    W.comap (ptMap π p k hk) = D.F k hk hP := by
  letI := affAlg p O.1
  have h1 := D.F_comp ψ (affPt O.1) (affPt_comp p O.1) O.2
  rw [D.F_congr hψ _ hk _ hP] at h1
  have h2 : D.pieceIdeal O = W.comap (D.pieceι O) := (hW O).symm
  calc W.comap (ptMap π p k hk) = (W.comap (D.pieceι O)).comap (bcMap B ψ) := by
        rw [← Scheme.IdealSheafData.comap_comp, bcMap_ptMap]
        exact congrArg _ (ptMap_congr π p hψ.symm _ _)
    _ = (D.pieceIdeal O).comap (bcMap B ψ) := by rw [h2]
    _ = D.F k hk hP := h1.symm

/-- **The glued ideal sheaf pulls back to the given ideals along all admissible points.** -/
theorem comap_ptMap {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G)
    (hk : k ≫ p = specMap R B) (hP : D.P k) :
    W.comap (ptMap π p k hk) = D.F k hk hP := by
  -- the localizations at elements whose basic open maps into an admissible affine open
  let ι := {f : B // ∃ O : D.Adm, ∀ x ∈ PrimeSpectrum.basicOpen f, k.base x ∈ O.1.1}
  let loc : ∀ f : ι, B →ₐ[R] Localization.Away f.1 :=
    fun f => IsScalarTower.toAlgHom R B (Localization.Away f.1)
  have hopen : ∀ f : ι, IsOpenImmersion (bcMap (π := π) _ (loc f)) := by
    intro f
    unfold bcMap
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (loc f).toRingHom)) :=
      inferInstanceAs (IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f.1)))))
    infer_instance
  refine Langlands.AlgebraicGeometry.IdealSheafGluing.eq_of_comap_eq'
    (fun f : ι => bcMap (π := π) _ (loc f)) ?_ fun f => ?_
  · intro y
    obtain ⟨O, hO, hPO⟩ := D.cover (k.base ((pullback.snd π (specMap R B)).base y))
    obtain ⟨_, ⟨f, rfl⟩, hyf, hfO⟩ :=
      (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open
        (show (pullback.snd π (specMap R B)).base y ∈ k.base ⁻¹' (O.1 : Set G) from hO)
        (O.1.isOpen.preimage k.base.hom.continuous)
    refine ⟨⟨f, ⟨O, hPO⟩, fun x hx => hfO hx⟩, ?_⟩
    rw [bcMap, Scheme.Pullback.range_map]
    refine ⟨by simp, ?_⟩
    change (pullback.snd π (specMap R B)).base y ∈
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f))))
    rw [← Scheme.Hom.coe_opensRange]
    erw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) f]
    exact hyf
  · obtain ⟨O, hfO⟩ := f.2
    letI := affAlg p O.1
    let kf := Spec.map (CommRingCat.ofHom (loc f).toRingHom) ≫ k
    have hkf : kf ≫ p = specMap R (Localization.Away f.1) := by
      rw [Category.assoc, hk, specMap_comp]
    have hrange : Set.range kf ⊆ Set.range (affPt O.1) := by
      rw [range_affPt]
      rintro _ ⟨x, rfl⟩
      apply hfO
      have : (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f.1)))).base x ∈
          (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f.1)))).opensRange :=
        ⟨x, rfl⟩
      erw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) f.1] at this
      exact this
    let lift := IsOpenImmersion.lift (affPt O.1) kf hrange
    have hlift : lift ≫ (affPt O.1) = kf := IsOpenImmersion.lift_fac _ _ _
    let ψ₀ := Spec.preimage lift
    let ψ : Γ(G, O.1.1) →ₐ[R] Localization.Away f.1 :=
      { ψ₀.hom with
        commutes' := fun r => by
          have hs : Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f.1))) =
              Spec.map (CommRingCat.ofHom (algebraMap R Γ(G, O.1.1)) ≫ ψ₀) := by
            have e1 : Spec.map (CommRingCat.ofHom (algebraMap R Γ(G, O.1.1))) =
                affPt O.1 ≫ p := (affPt_comp p O.1).symm
            rw [Spec.map_comp, Spec.map_preimage, e1, ← Category.assoc, hlift, hkf]
          have := congrArg (fun φ => φ.hom r) (Spec.map_injective hs)
          exact this.symm }
    have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (affPt O.1) = kf := by
      rw [← hlift]
      congr 1
      exact Spec.map_preimage lift
    have hPf : D.P kf := D.P_comp (loc f) k hP
    have hA := D.comap_ptMap_of_factor hW O ψ kf hψ hkf hPf
    rw [← D.F_comp (loc f) k hk hP, ← Scheme.IdealSheafData.comap_comp, bcMap_ptMap]
    exact hA

end PointIdeals

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
