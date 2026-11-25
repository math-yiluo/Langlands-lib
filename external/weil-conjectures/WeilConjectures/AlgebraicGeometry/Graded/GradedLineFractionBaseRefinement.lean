/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedLineFractionChart.GradedLineFractionChart

/-! # Local restriction of one fraction chart to an affine base open

Source: Stacks Project, Constructions, Tags 01NK and 01O9.
(blueprint: lem-trf-graded-line-fraction-base-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
attribute [local irreducible] Scheme.GradedAlgebraData.relProjι

private theorem fractionPower_generator {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    {W : T.Opens} {l : Γ(L, W)} (hl : IsFreeGenerator l) (n : ℕ) :
    IsFreeGenerator (P l n) := by
  induction n with
  | zero => rw [hP0]; exact isFreeGenerator_one W
  | succ n ih => rw [hPs]; exact hl.tmulSection ih

private theorem fractionPower_restrict {T : Scheme.{u}} {L : T.Modules}
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    {W B : T.Opens} (hB : B ≤ W) (l : Γ(L, W)) (n : ℕ) :
    (L.tensorPow n).presheaf.map (homOfLE hB).op (P l n) =
      P (L.presheaf.map (homOfLE hB).op l) n := by
  induction n with
  | zero =>
    rw [hP0, hP0]
    change (𝟙_ T.Modules).presheaf.map (homOfLE hB).op
      (unitSectionsEquiv W 1) = unitSectionsEquiv B 1
    rw [presheaf_map_unitSectionsEquiv, map_one]
  | succ n ih =>
    rw [hPs, hPs]
    change (L ⊗ L.tensorPow n).presheaf.map (homOfLE hB).op (tmulSection l (P l n)) =
      tmulSection (L.presheaf.map (homOfLE hB).op l) _
    rw [tmulSection_map, ih]

private theorem fractionCoefficient_restrict
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (i : GradedLineFractionChart h A L) (V : S.affineOpens) (hV : V ≤ i.U)
    (W : T.affineOpens) (hWi : W ≤ i.W) (hWV : W.1 ≤ h ⁻¹ᵁ V.1)
    (n : ℕ) (a : A.grading i.U n) :
    c V W hWV (L.presheaf.map (homOfLE (X := T.Opens) hWi).op i.l) n
        ⟨A.res hV a, (A.res hV).map_mem a.property⟩ =
      T.presheaf.map (homOfLE (X := T.Opens) hWi).op (c i.U i.W i.hWU i.l n a) := by
  apply (fractionPower_generator P hP0 hPs (i.hl.map hWi) n).smul_left_injective
  dsimp only
  calc
    _ = (L.tensorPow n).val.map (homOfLE hWV).op
        (ψ.component V n ⟨A.res hV a, (A.res hV).map_mem a.property⟩) :=
      hc V W hWV _ (i.hl.map hWi) n _
    _ = (L.tensorPow n).presheaf.map (homOfLE (X := T.Opens) hWi).op
        ((L.tensorPow n).val.map (homOfLE i.hWU).op (ψ.component i.U n a)) := by
      rw [ψ.restriction]
      change (L.tensorPow n).presheaf.map (homOfLE hWV).op
        ((L.tensorPow n).presheaf.map (homOfLE (h.preimage_mono hV)).op
          (ψ.component i.U n a)) =
        (L.tensorPow n).presheaf.map (homOfLE (X := T.Opens) hWi).op
          ((L.tensorPow n).presheaf.map (homOfLE i.hWU).op (ψ.component i.U n a))
      rw [presheaf_map_map_apply, presheaf_map_map_apply]
      exact congrArg (fun f : W.1 ⟶ h ⁻¹ᵁ i.U.1 ↦
        (L.tensorPow n).presheaf.map f.op (ψ.component i.U n a)) (Subsingleton.elim _ _)
    _ = (L.tensorPow n).presheaf.map (homOfLE (X := T.Opens) hWi).op
        (c i.U i.W i.hWU i.l n a • P i.l n) :=
      congrArg ((L.tensorPow n).presheaf.map (homOfLE (X := T.Opens) hWi).op)
        (hc i.U i.W i.hWU i.l i.hl n a).symm
    _ = _ := by
      erw [map_smul]
      rw [fractionPower_restrict P hP0 hPs hWi i.l n]

/-- Restrict one framed fraction chart to a smaller affine base, locally at a point.
The comparison chart uses the restricted original frame and denominator, without a
change of degree. This compares a chart only with its own affine-base restriction.

Source: Stacks Project, Constructions, Tag 01O9, characterization (3) and its proof,
using the localization construction of Tag 01NK.
(blueprint: lem-trf-graded-line-fraction-base-refinement).

Proof: Choose an affine W around the image of x contained in the original framed open
and h inverse V. Restrict the original frame l to W and the denominator e to V, keeping
the degree d. The restriction law of psi, hc, and injectivity of multiplication by the
restricted frame powers show that the new denominator coefficient is the restriction
of the old one. Hence the new localization spectrum is the inverse image of W inside
the old localization spectrum; it is an open neighborhood of x. Its projection to the
old chart is induced by the ordinary-localization map of section restrictions. Identify
this open subscheme with an open O in the old chart, and use its inverse identification
as f. The source equation follows from the affine section restriction square. The
restriction map A(U) to A(V) induces the homogeneous-localization map on standard Proj
charts. The fraction formula hρ and the coefficient restriction identity show that the
two ring maps commute with these localization maps: verify on a/e^n, including n=0,
and use homogeneous-fraction surjectivity. Naturality of the standard Proj embeddings
and the relative-Proj transition equation then give the target equation. No comparison
of different frames or different denominators is involved, and no covering of the whole
source by denominator charts or global generation is required. All denominators are
inverted in ordinary localizations, so zero divisors and nilpotents cause no exception. -/
theorem gradedLineFraction_baseRefinement
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ) (i : GradedLineFractionChart h A L)
    (V : S.affineOpens) (hV : V ≤ i.U) (x : i.domain c)
    (hx : (i.source c ≫ h) x ∈ V.1) :
    ∃ (W : T.affineOpens) (hWi : W ≤ i.W) (hWV : W.1 ≤ h ⁻¹ᵁ V.1),
      let k : GradedLineFractionChart h A L :=
        ⟨V, W, hWV, L.presheaf.map (homOfLE (X := T.Opens) hWi).op i.l, i.hl.map hWi,
          i.d, i.hd, ⟨A.res hV i.e, (A.res hV).map_mem i.e.property⟩⟩
      ∃ (O : (i.domain c).Opens), x ∈ O ∧ ∃ f : O.toScheme ⟶ k.domain c,
        f ≫ k.source c = O.ι ≫ i.source c ∧
          f ≫ k.target c ρ = O.ι ≫ i.target c ρ := by
  classical
  have hxi : i.source c x ∈ i.W.1 := by
    dsimp only [GradedLineFractionChart.source, Scheme.Hom.comp_apply]
    exact Subtype.mem _
  obtain ⟨W₀, hW₀, hxW, hW⟩ := exists_isAffineOpen_mem_and_subset
    (show i.source c x ∈ i.W.1 ⊓ (h ⁻¹ᵁ V.1) from ⟨hxi, hx⟩)
  let W : T.affineOpens := ⟨W₀, hW₀⟩
  have hWi : W ≤ i.W := hW.trans inf_le_left
  have hWV : W.1 ≤ h ⁻¹ᵁ V.1 := hW.trans inf_le_right
  let k : GradedLineFractionChart h A L :=
    ⟨V, W, hWV, L.presheaf.map (homOfLE (X := T.Opens) hWi).op i.l, i.hl.map hWi,
      i.d, i.hd, ⟨A.res hV i.e, (A.res hV).map_mem i.e.property⟩⟩
  let φ : Γ(T, i.W.1) →+* Γ(T, W.1) := (T.presheaf.map (homOfLE (X := T.Opens) hWi).op).hom
  have hcres (n : ℕ) (a : A.grading i.U n) :
      c V W hWV k.l n ⟨A.res hV a, (A.res hV).map_mem a.property⟩ =
        φ (c i.U i.W i.hWU i.l n a) :=
    fractionCoefficient_restrict ψ P hP0 hPs c hc i V hV W hWi hWV n a
  have hb : k.coefficient c = φ (i.coefficient c) := hcres i.d i.e
  have hpowers : Submonoid.powers (i.coefficient c) ≤
      (Submonoid.powers (k.coefficient c)).comap φ := by
    rintro z ⟨n, rfl⟩
    change φ (i.coefficient c ^ n) ∈ Submonoid.powers (k.coefficient c)
    rw [map_pow, ← hb]
    exact ⟨n, rfl⟩
  let R : Localization.Away (i.coefficient c) →+* Localization.Away (k.coefficient c) :=
    IsLocalization.map (Localization.Away (k.coefficient c)) φ hpowers
  let a : k.domain c ⟶ i.domain c := Spec.map (CommRingCat.ofHom R)
  have halg : CommRingCat.ofHom
      (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))) ≫
        CommRingCat.ofHom R = T.presheaf.map (homOfLE (X := T.Opens) hWi).op ≫
          CommRingCat.ofHom (algebraMap Γ(T, W.1) (Localization.Away (k.coefficient c))) := by
    ext z
    change R (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c)) z) =
      algebraMap Γ(T, W.1) (Localization.Away (k.coefficient c)) (φ z)
    exact IsLocalization.map_eq (S := Localization.Away (i.coefficient c))
      (Q := Localization.Away (k.coefficient c)) (g := φ) hpowers z
  have hspec : Spec.map (CommRingCat.ofHom R) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(T, W.1) (Localization.Away (k.coefficient c)))) ≫
          Spec.map (T.presheaf.map (homOfLE (X := T.Opens) hWi).op) := by
    rw [← Spec.map_comp, halg, Spec.map_comp]
  have hsource : a ≫ i.source c = k.source c := by
    dsimp only [a, GradedLineFractionChart.source]
    rw [← Category.assoc, hspec, Category.assoc,
      reassoc_of% (specMap_res_isoSpec_inv (X := T) hWi), Scheme.homOfLE_ι]
  have hfrac : R.comp (ρ i) =
      (ρ k).comp (HomogeneousLocalization.Away.map (A.res hV) i.e.val) := by
    apply RingHom.ext
    intro z
    obtain ⟨n, b, hnum, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (A.grading i.U) i.e.property z
    change R (ρ i _) = ρ k _
    rw [HomogeneousLocalization.Away.map_mk]
    rw [hρ i n ⟨b, hnum⟩, hρ k n ⟨A.res hV b, (A.res hV).map_mem hnum⟩]
    simp only [R, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow]
    rw [← hcres (n • i.d) ⟨b, hnum⟩]
    congr 1
    apply Subtype.ext
    change φ (i.coefficient c) ^ n = k.coefficient c ^ n
    rw [hb]
  have hspecFrac : Spec.map (CommRingCat.ofHom R) ≫
        Spec.map (CommRingCat.ofHom (ρ i)) =
      Spec.map (CommRingCat.ofHom (ρ k)) ≫ Spec.map
        (CommRingCat.ofHom (HomogeneousLocalization.Away.map (A.res hV) i.e.val)) := by
    have heq := congrArg (fun f :
        HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
          Localization.Away (k.coefficient c) ↦ Spec.map (CommRingCat.ofHom f)) hfrac
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using heq
  have hι : Spec.map
        (CommRingCat.ofHom (HomogeneousLocalization.Away.map (A.res hV) i.e.val)) ≫
        Proj.awayι (A.grading i.U) i.e.val i.e.property i.hd ≫ A.relProjι i.U =
      Proj.awayι (A.grading V) k.e.val k.e.property k.hd ≫ A.relProjι V := by
    rw [← Proj.awayι_comp_map_assoc (A.res hV) (A.irrelevant_le_map_res hV)]
    change Proj.awayι (A.grading V) k.e.val k.e.property k.hd ≫
      A.relProjFunctor.map (homOfLE hV) ≫ A.relProjι i.U = _
    rw [A.relProjFunctor_map_relProjι]
  have htarget : a ≫ i.target c ρ = k.target c ρ := by
    dsimp only [a, GradedLineFractionChart.target]
    rw [← Category.assoc, hspecFrac, Category.assoc, hι]
  have hrange (j : GradedLineFractionChart h A L) :
      (j.source c).opensRange = T.basicOpen (j.coefficient c) := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, j.W.1) (Localization.Away (j.coefficient c)))) ≫
        j.W.2.fromSpec).opensRange = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
      j.W.2.fromSpec_image_basicOpen]
  have hmem : i.source c x ∈ (k.source c).opensRange := by
    rw [hrange, hb]
    change i.source c x ∈ T.basicOpen
      (T.presheaf.map (homOfLE (X := T.Opens) hWi).op (i.coefficient c))
    rw [T.basicOpen_res]
    refine ⟨hxW, ?_⟩
    rw [← hrange i]
    exact ⟨x, rfl⟩
  have : IsOpenImmersion (a ≫ i.source c) := by rw [hsource]; infer_instance
  have : IsOpenImmersion a := IsOpenImmersion.of_comp a (i.source c)
  have hxO : x ∈ a.opensRange := by
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, (i.source c).isOpenEmbedding.injective ?_⟩
    change (a ≫ i.source c) z = i.source c x
    rw [hsource]
    exact hz
  refine ⟨W, hWi, hWV, a.opensRange, hxO, a.isoOpensRange.inv, ?_, ?_⟩
  · rw [← hsource, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  · rw [← htarget, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

end AlgebraicGeometry.Scheme.Modules
