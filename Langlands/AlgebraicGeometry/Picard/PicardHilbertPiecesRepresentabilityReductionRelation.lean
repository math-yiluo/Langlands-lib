import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionAbel

/-! # The flat proper equivalence relation of linear equivalence on an open of the divisor
scheme -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist Langlands.AlgebraicGeometry.Modules.DerivedSections

lemma add_add_neg_aux {Y : Scheme.{u}} (a b c : Group Y) : a + c = a + b + c + -b := by
  rw [add_assoc a b c, group_add_comm b c, ← add_assoc, add_neg_cancel_right]

section Relation

variable {S X : Scheme.{u}} (f : X ⟶ S) (𝓛X : X.Modules)
  (h𝓛X : Scheme.Modules.IsInvertible 𝓛X) {D : Scheme.{u}} (d : D ⟶ S)
  (W : RelativeEffectiveDivisor (pullback.snd f d)) (m : ℕ) {κ : Type}
  (U : ∀ (T : Scheme.{u}) (s : T ⟶ S), (pullback f s).Modules → κ → ℕ → T.Opens)

/-- Fibrewise cohomology of the twists on a whole piece, as in the statement. -/
def HU3 : Prop :=
  ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (s : T ⟶ S)
    (L : (pullback f s).Modules), Scheme.Modules.IsInvertible L →
    ∀ (c : κ) (n : ℕ), U T s L c n = ⊤ → ∀ t : T,
      IsZero ((relativeCohomology
          (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 1).obj
        ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
          (twist L ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) n))) ∧
      ¬ IsZero ((relativeCohomology
          (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 0).obj
        ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
          (twist L ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) n)))

/-- On a whole piece, the linear system of `L(m)` is flat, of finite presentation and
surjective. -/
lemma flat_of_top (hU3 : HU3 f 𝓛X U) {T : Scheme.{u}} [IsLocallyNoetherian T] (s : T ⟶ S)
    (L : (pullback f s).Modules) (hL : Scheme.Modules.IsInvertible L) (c : κ)
    (htop : U T s L c m = ⊤) {Λ : Scheme.{u}} (l : Λ ⟶ T)
    (h6 : (∀ t : T, IsZero ((relativeCohomology
          (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 1).obj
        ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
          (twist L ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m)))) →
      Flat l ∧ LocallyOfFinitePresentation l ∧
        ((∀ t : T, ¬ IsZero ((relativeCohomology
          (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) 0).obj
        ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f s) (T.fromSpecResidueField t))).obj
          (twist L ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m)))) →
          Surjective l)) :
    Flat l ∧ LocallyOfFinitePresentation l ∧ Surjective l := by
  obtain ⟨h1, h2, h3⟩ := h6 (fun t => (hU3 T s L hL c m htop t).1)
  exact ⟨h1, h2, h3 (fun t => (hU3 T s L hL c m htop t).2)⟩

/-- The relation of linear equivalence on `Z₀ = U(L_W)`: a flat proper `S`-scheme `R` with two
maps to `Z₀` identifying exactly the pairs of points with the same Abel class. -/
lemma exists_relation (hLS : ProperFlatIntegralLinearSystemStatement.{u})
    (hcl : Classifies f d W) (hbc : RelativeEffectiveDivisorBaseChangeStatement.{u})
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    (hε : ∃ ε : S ⟶ X, ε ≫ f = 𝟙 S) (hU1 : HU1 f U) (hU2 : HU2 f U) (hU3 : HU3 f 𝓛X U)
    [IsLocallyNoetherian D] (c : κ) (Z₀ : D.Opens)
    (hZ₀ : U D d (LW f 𝓛X h𝓛X d W m) c m = Z₀) :
    ∃ (R : Over S) (sR tR : R ⟶ Zo d Z₀), Flat sR.left ∧ IsProper sR.left ∧
      uliftYoneda.{u + 1}.map sR ≫ abelMap f 𝓛X h𝓛X d W m Z₀ =
        uliftYoneda.{u + 1}.map tR ≫ abelMap f 𝓛X h𝓛X d W m Z₀ ∧
      ∀ (T : Over S) [IsLocallyNoetherian T.left] (x y : T ⟶ Zo d Z₀),
        (abelMap f 𝓛X h𝓛X d W m Z₀).app (op T) (ULift.up x) =
            (abelMap f 𝓛X h𝓛X d W m Z₀).app (op T) (ULift.up y) →
          ∃! r : T ⟶ R, r ≫ sR = x ∧ r ≫ tR = y := by
  have hLW := isInvertible_LW f 𝓛X h𝓛X d W m
  have hL0 := isInvertible_pullback (mapX f Z₀.ι rfl) hLW
  have hM := isInvertible_twist hL0 (isInvertible_pullback (pullback.fst f (Z₀.ι ≫ d)) h𝓛X) m
  obtain ⟨Λ, l, WΛ, NΛ, hlp, hN, ⟨e⟩, h4, h5, h6⟩ := hLS Z₀ (pullback.snd f (Z₀.ι ≫ d))
    inferInstance inferInstance inferInstance _ hM
  have htop : U Z₀ (Z₀.ι ≫ d)
      ((Scheme.Modules.pullback (mapX f Z₀.ι rfl)).obj (LW f 𝓛X h𝓛X d W m)) c m = ⊤ := by
    rw [hU2' f hU2 Z₀.ι rfl _ hLW c m, hZ₀]
    exact Scheme.Opens.ι_preimage_self Z₀
  obtain ⟨hlf, hlfp, -⟩ := flat_of_top f 𝓛X m U hU3 _ _ hL0 c htop l h6
  have := hlp
  have := hlf
  have := hlfp
  have : IsLocallyNoetherian Λ := LocallyOfFiniteType.isLocallyNoetherian l
  obtain ⟨y0, wy0, hy0W, hy0⟩ := linsys_class f 𝓛X h𝓛X d W m hcl hbc l WΛ _ hL0 NΛ hN e
  have hpt : pt f 𝓛X h𝓛X d W m y0 wy0 =
      pt f 𝓛X h𝓛X d W m (l ≫ Z₀.ι) (Category.assoc _ _ _) +
        Group.pullback (pullback.snd f (l ≫ Z₀.ι ≫ d)) (icl NΛ hN) := by
    rw [hy0, icl_pullback _ _ hLW, icl_LW, ← pb_comp_apply, mapX_comp]
    rfl
  have hy0Z : y0 ⁻¹ᵁ Z₀ = ⊤ := by
    have h1 := hU2' f hU2 y0 wy0 _ hLW c m
    have h2 := U_eq_preimage f 𝓛X h𝓛X d W m U hU1 hU2 (l ≫ Z₀.ι) (Category.assoc _ _ _) _
      (isInvertible_pullback (mapX f y0 wy0) hLW) (icl NΛ hN)
      (by rw [icl_pullback _ _ hLW, icl_LW]; exact hpt) c
    have h3 := h1.symm.trans h2
    rw [hZ₀] at h3
    rw [h3]
    exact comap_preimage_ι_self l
  let t' : Λ ⟶ Z₀ := IsOpenImmersion.lift Z₀.ι y0 (range_subset_of_preimage_eq_top y0 Z₀ hy0Z)
  have ht' : t' ≫ Z₀.ι = y0 := IsOpenImmersion.lift_fac _ _ _
  let R : Over S := Over.mk (l ≫ Z₀.ι ≫ d)
  let sR : R ⟶ Zo d Z₀ := Over.homMk l rfl
  let tR : R ⟶ Zo d Z₀ := Over.homMk t' (by
    change t' ≫ Z₀.ι ≫ d = l ≫ Z₀.ι ≫ d
    rw [← Category.assoc, ht', wy0])
  refine ⟨R, sR, tR, hlf, hlp, ?_, ?_⟩
  · apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp]
    simp only [uliftYonedaEquiv_uliftYoneda_map]
    rw [abelMap_app, abelMap_app, ab, ab]
    symm
    rw [scl_sym_eq_iff f hε]
    exact ⟨icl NΛ hN, (pt_congr f 𝓛X h𝓛X d W m ht' _ _).trans hpt⟩
  · intro T _ x y hxy
    rw [abelMap_app, abelMap_app, ab, ab, scl_sym_eq_iff f hε] at hxy
    obtain ⟨n, hn⟩ := hxy
    have wx : x.left ≫ Z₀.ι ≫ d = T.hom := Over.w x
    have wy : (y.left ≫ Z₀.ι) ≫ d = T.hom := (Category.assoc _ _ _).trans (Over.w y)
    have wk0 : ∀ k : T.left ⟶ Λ, k ≫ l = x.left → (k ≫ y0) ≫ d = T.hom := fun k hk => by
      rw [Category.assoc, wy0, ← Category.assoc, hk, wx]
    have hkey : ∀ (k : T.left ⟶ Λ) (hk : k ≫ l = x.left),
        (WΛ.ideal.comap (pullback.map (pullback.snd f (Z₀.ι ≫ d)) x.left
          (pullback.snd f (Z₀.ι ≫ d)) l (𝟙 _) k (𝟙 _) (by simp) (by simp [hk]))).comap
            (bcIso f x.left wx).hom =
          W.ideal.comap (mapX f (k ≫ y0) (wk0 k hk)) := by
      intro k hk
      rw [← Scheme.IdealSheafData.comap_comp,
        bcIso_hom_map f l x.left wx k hk (by rw [← Category.assoc, hk, wx]),
        Scheme.IdealSheafData.comap_comp, ← hy0W, ← Scheme.IdealSheafData.comap_comp, mapX_comp]
    have hEk : ∀ (k : T.left ⟶ Λ) (hk : k ≫ l = x.left), k ≫ t' = y.left →
        WΛ.ideal.comap (pullback.map (pullback.snd f (Z₀.ι ≫ d)) x.left
          (pullback.snd f (Z₀.ι ≫ d)) l (𝟙 _) k (𝟙 _) (by simp) (by simp [hk])) =
          (W.ideal.comap (mapX f (y.left ≫ Z₀.ι) wy)).comap (bcIso f x.left wx).inv := by
      intro k hk hk'
      apply comap_injective_of_iso (bcIso f x.left wx)
      rw [hkey k hk, ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
        Scheme.IdealSheafData.comap_id]
      exact congrArg W.ideal.comap (mapX_congr f (by rw [← ht', ← Category.assoc, hk']) _ _)
    obtain ⟨hE0, hdE⟩ := flat_comap (bcIso f x.left wx).inv (pullback.snd f T.hom) _
      (classifies_rel f d W hcl (y.left ≫ Z₀.ι) wy)
    have hE : IsRelativeEffectiveCartierIdeal (pullback.snd (pullback.snd f (Z₀.ι ≫ d)) x.left)
        ((W.ideal.comap (mapX f (y.left ≫ Z₀.ι) wy)).comap (bcIso f x.left wx).inv) := by
      rw [← bcIso_inv_snd f x.left wx]
      exact hE0
    obtain ⟨N', hN', hN'n⟩ := exists_icl (-n)
    have hclass : icl (EffectiveCartierDivisor.lineBundle ⟨_, hE.1⟩).obj
          (isInvertible_lineBundle _) =
        icl _ (isInvertible_pullback (pullback.fst (pullback.snd f (Z₀.ι ≫ d)) x.left) hM) +
          icl _ (isInvertible_pullback (pullback.snd (pullback.snd f (Z₀.ι ≫ d)) x.left) hN') := by
      rw [← dcl_eq_icl, hdE, dcl_comap_mapX f 𝓛X h𝓛X d W m hbc _ wy, icl_pullback _ _ hM,
        icl_pullback _ _ hN', hN'n, icl_twist_pt f 𝓛X h𝓛X d W m Z₀.ι rfl hM,
        ← bcIso_inv_mapX f x.left wx, ← bcIso_inv_snd f x.left wx, pb_comp_apply,
        pb_comp_apply, ← map_add]
      congr 1
      rw [map_add, map_nsmul, pb_mapX_pt, pb_mapX_cP, map_neg, hn]
      exact add_add_neg_aux _ _ _
    obtain ⟨k, hk, hkE⟩ := (h4 T.left x.left _).2
      ⟨hE, N', hN', nonempty_iso_tensor_of_icl _ _ _ hclass⟩
    have hky : k ≫ t' = y.left := by
      apply (cancel_mono Z₀.ι).1
      rw [Category.assoc, ht']
      apply classifies_eq f d W hcl (k ≫ y0) (y.left ≫ Z₀.ι) (wk0 k hk) wy
      rw [← hkey k hk, hkE, ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
        Scheme.IdealSheafData.comap_id]
    refine ⟨Over.homMk k (by
        change k ≫ l ≫ Z₀.ι ≫ d = T.hom
        rw [← Category.assoc, hk, wx]),
      ⟨Over.OverMorphism.ext hk, Over.OverMorphism.ext hky⟩, ?_⟩
    rintro r ⟨hr1, hr2⟩
    have h1 : r.left ≫ l = x.left := congrArg (fun φ => φ.left) hr1
    have h2 : r.left ≫ t' = y.left := congrArg (fun φ => φ.left) hr2
    apply Over.OverMorphism.ext
    exact h5 T.left x.left r.left k h1 hk ((hEk r.left h1 h2).trans (hEk k hk hky).symm)

end Relation

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
