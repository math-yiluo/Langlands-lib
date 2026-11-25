/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedLineFractionChart.GradedLineFractionChart
import all WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionSameBase
import all WeilConjectures.AlgebraicGeometry.Line.LineProjChartPullback

/-! # Local comparison for graded line fraction tests

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: lem-trf-graded-line-fraction-test-local).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
attribute [local irreducible] Scheme.GradedAlgebraData.relProjι
attribute [local irreducible] tensorPullbackObj tensorPullbackMap

private theorem localTest_frame {T W : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (L : T.Modules)
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (B : T.Opens) (hB : B ≤ j ''ᵁ (⊤ : W.Opens)) :
    ∃ l : Γ(L, B), IsFreeGenerator l ∧
      e.hom.app (j ⁻¹ᵁ B) (tensorPullbackSection j L B l) =
        unitSectionsEquiv (j ⁻¹ᵁ B) 1 := by
  let a := (restrictAdjunction j).leftAdjointUniq (tensorPullbackSectionAdjunction j)
  let b : L.restrict j ≅ SheafOfModules.unit W.ringCatSheaf := a.app L ≪≫ e
  let s : Γ(L, j ''ᵁ (⊤ : W.Opens)) := b.inv.app ⊤ (unitSectionsEquiv ⊤ 1)
  have hs : IsFreeGenerator (M := L) s :=
    (isFreeGenerator_restrict_iff j L s).mp
      ((isFreeGenerator_one (⊤ : W.Opens)).app_hom b.symm)
  refine ⟨L.presheaf.map (homOfLE hB).op s, hs.map hB, ?_⟩
  have hu := (restrictAdjunction j).unit_leftAdjointUniq_hom_app
    (tensorPullbackSectionAdjunction j) L
  have hunit := congrArg (fun z ↦ z.app B (L.presheaf.map (homOfLE hB).op s)) hu
  have hn : ((tensorPullbackSectionAdjunction j).unit.app L).app B
      (L.presheaf.map (homOfLE hB).op s) =
      tensorPullbackSection j L B (L.presheaf.map (homOfLE hB).op s) :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).1 _ _ _
  replace hunit := hunit.trans hn
  change (a.hom.app L).app (j ⁻¹ᵁ B)
    (L.presheaf.map (homOfLE (j.image_preimage_le B)).op
      (L.presheaf.map (homOfLE hB).op s)) = _ at hunit
  rw [← hunit]
  have hres : L.presheaf.map (homOfLE (j.image_preimage_le B)).op
        (L.presheaf.map (homOfLE hB).op s) =
      (L.restrict j).presheaf.map (homOfLE (le_top : j ⁻¹ᵁ B ≤ ⊤)).op s := by
    rw [presheaf_map_map_apply]
    rfl
  rw [hres]
  change b.hom.app (j ⁻¹ᵁ B)
    ((L.restrict j).presheaf.map (homOfLE le_top).op (b.inv.app ⊤ _)) = _
  rw [Hom.app_presheaf_map]
  have hb : b.hom.app ⊤ (b.inv.app ⊤ (unitSectionsEquiv ⊤ 1)) =
      unitSectionsEquiv ⊤ 1 := by
    exact congrArg (fun z : SheafOfModules.unit W.ringCatSheaf ⟶
      SheafOfModules.unit W.ringCatSheaf ↦ Hom.app z ⊤ (unitSectionsEquiv ⊤ 1)) b.inv_hom_id
  rw [hb]
  change (𝟙_ W.Modules).presheaf.map (homOfLE le_top).op
    (unitSectionsEquiv ⊤ 1) = unitSectionsEquiv (j ⁻¹ᵁ B) 1
  rw [presheaf_map_unitSectionsEquiv, map_one]

private theorem localTest_trivialized_power {W : Scheme.{u}} {M : W.Modules}
    (e : M ≅ SheafOfModules.unit W.ringCatSheaf) (B : W.Opens) (s : Γ(M, B))
    (hs : e.hom.app B s = unitSectionsEquiv B 1) (n : ℕ) :
    (AlgebraicSpace.trivializedPower e n).hom.app B (lineProjFramePower M B s n) =
      unitSectionsEquiv B 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Hom.app (λ_ (Modules.unit W)).hom B
      ((e.hom ⊗ₘ (AlgebraicSpace.trivializedPower e n).hom).app B
        (tmulSection s (lineProjFramePower M B s n))) = _
    rw [tensorHom_app_tmulSection, hs, ih, leftUnitor_hom_app_tmulSection, one_smul]

private theorem localTest_coefficient
    {S T W : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {B : T.Opens}, Γ(L, B) → (n : ℕ) → Γ(L.tensorPow n, B))
    (hP0 : ∀ (B : T.Opens) (l : Γ(L, B)), P l 0 = unitSectionsEquiv B 1)
    (hPs : ∀ (B : T.Opens) (l : Γ(L, B)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (j : W ⟶ T) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (α : A.obj V →+* Γ(W, ⊤))
    (hα : ∀ (n : ℕ) (a : A.grading V n), α a =
      (unitSectionsEquiv ⊤).symm
        ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (ψ.evaluate j V q n a)))
    (B : T.Opens) (hBV : B ≤ h ⁻¹ᵁ V.1) (l : Γ(L, B))
    (hl : e.hom.app (j ⁻¹ᵁ B) (tensorPullbackSection j L B l) =
      unitSectionsEquiv (j ⁻¹ᵁ B) 1)
    (n : ℕ) (a : A.grading V n) (r : Γ(T, B))
    (hr : r • P l n = (L.tensorPow n).presheaf.map (homOfLE hBV).op
      (ψ.component V n a)) :
    W.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ B ≤ ⊤)).op (α a) = j.app B r := by
  let M := (tensorPullback j).obj L
  have hn (N : T.Modules) (U : T.Opens) (s : Γ(N, U)) :
      ((tensorPullbackSectionAdjunction j).unit.app N).app U s =
        tensorPullbackSection j N U s :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).1 N U s
  have heval : (M.tensorPow n).presheaf.map
      (homOfLE (le_top : j ⁻¹ᵁ B ≤ ⊤)).op (ψ.evaluate j V q n a) =
      (boundaryPullbackPowIso j L n).hom.app (j ⁻¹ᵁ B)
        (tensorPullbackSection j (L.tensorPow n) B
          ((L.tensorPow n).presheaf.map (homOfLE hBV).op (ψ.component V n a))) := by
    dsimp only [RelativeGradedLineMap.evaluate]
    rw [hn, ← Hom.app_presheaf_map]
    change (boundaryPullbackPowIso j L n).hom.app (j ⁻¹ᵁ B)
      (((tensorPullback j).obj (L.tensorPow n)).presheaf.map (homOfLE le_top).op
        (((tensorPullback j).obj (L.tensorPow n)).presheaf.map (homOfLE q).op
          (tensorPullbackSection j (L.tensorPow n) (h ⁻¹ᵁ V.1) (ψ.component V n a)))) = _
    rw [presheaf_map_map_apply, tensor_section_map]
    rfl
  have hp (k : ℕ) : P l k = lineProjFramePower L B l k := by
    induction k with
    | zero => exact hP0 B l
    | succ k ih => rw [hPs, ih]; rfl
  have ha0 : unitSectionsEquiv ⊤ (α a) =
      (AlgebraicSpace.trivializedPower e n).hom.app ⊤ (ψ.evaluate j V q n a) := by
    rw [hα]
    exact LinearEquiv.apply_symm_apply _ _
  have hα' := congrArg (fun s : Γ(𝟙_ W.Modules, ⊤) ↦
    (𝟙_ W.Modules).presheaf.map (homOfLE (le_top : j ⁻¹ᵁ B ≤ ⊤)).op s) ha0
  rw [presheaf_map_unitSectionsEquiv] at hα'
  erw [← Hom.app_presheaf_map] at hα'
  rw [heval, ← hr, tensor_section_smul, Hom.app_smul, Hom.app_smul,
    hp, pullback_frame_power] at hα'
  erw [localTest_trivialized_power e _ _ hl n] at hα'
  exact (unitSectionsEquiv (j ⁻¹ᵁ B)).injective
    (hα'.trans (by rw [← unitSectionsEquiv_eq_smul_one]))

private theorem localTest_ringHom_ext {R Q : Type u} [CommRing R] [CommRing Q]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (φ χ : R →+* Q)
    (h : ∀ (n : ℕ) (a : 𝒜 n), φ a.val = χ a.val) : φ = χ := by
  classical
  ext a
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun n _ ↦ h n (DirectSum.decompose 𝒜 a n)

private theorem localTest_source_app
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (c : GradedLineFractionCoefficients h A L) (i : GradedLineFractionChart h A L)
    (q : (⊤ : (i.domain c).Opens) ≤ i.source c ⁻¹ᵁ i.W.1) :
    (i.source c).appLE i.W.1 ⊤ q =
      CommRingCat.ofHom (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))) ≫
        (Scheme.ΓSpecIso _).inv := by
  have hfrom : i.W.2.fromSpec.appLE i.W.1 ⊤ (by simp) =
      (Scheme.ΓSpecIso Γ(T, i.W.1)).inv := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp, ← op_comp]
    simp
  dsimp only [GradedLineFractionChart.source]
  change (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c)))) ≫
        i.W.2.fromSpec).appLE i.W.1 ⊤ q = _
  rw [← Scheme.Hom.appLE_comp_appLE _ _ i.W.1 ⊤ ⊤
    (by simp) (by simp), hfrom]
  change (Scheme.ΓSpecIso Γ(T, i.W.1)).inv ≫ (Spec.map _).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

private theorem localTest_source_range
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (c : GradedLineFractionCoefficients h A L) (i : GradedLineFractionChart h A L) :
    (i.source c).opensRange = T.basicOpen (i.coefficient c) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c)))) ≫
      i.W.2.fromSpec).opensRange = _
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
    i.W.2.fromSpec_image_basicOpen]

private theorem localTest_app_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (B : Y.Opens) (qf : (⊤ : X.Opens) ≤ f ⁻¹ᵁ B) (qg : (⊤ : X.Opens) ≤ g ⁻¹ᵁ B) :
    f.appLE B ⊤ qf = g.appLE B ⊤ qg := by
  subst g
  rfl

attribute [local irreducible] fractionBaseCoefficientRingHom
attribute [local irreducible] GradedLineFractionChart.target
attribute [local irreducible] GradedLineFractionChart.source

private theorem localTest_chart
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {B : T.Opens}, Γ(L, B) → (n : ℕ) → Γ(L.tensorPow n, B))
    (hP0 : ∀ (B : T.Opens) (l : Γ(L, B)), P l 0 = unitSectionsEquiv B 1)
    (hPs : ∀ (B : T.Opens) (l : Γ(L, B)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (B : T.affineOpens) (hBU : B.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, B.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U B hBU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hBU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ) (i : GradedLineFractionChart h A L) :
    ∃ (φ : A.obj i.U →+* Localization.Away (i.coefficient c))
      (hf : (HomogeneousIdeal.irrelevant (A.grading i.U)).toIdeal.map φ = ⊤),
      i.target c ρ = Proj.fromOfGlobalSections (A.grading i.U)
        ((Scheme.ΓSpecIso _).inv.hom.comp φ)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) ≫ A.relProjι i.U ∧
      ∀ (n : ℕ) (a : A.grading i.U n),
        φ a.val = algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))
          (c i.U i.W i.hWU i.l n a) := by
  let φ₀ := fractionBaseCoefficientRingHom ψ P hP0 hPs i.U i.W i.hWU
    i.l i.hl (c i.U i.W i.hWU i.l) (hc i.U i.W i.hWU i.l i.hl)
  let φ := (algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))).comp φ₀
  have hφ (n : ℕ) (a : A.grading i.U n) : φ a.val =
      algebraMap Γ(T, i.W.1) (Localization.Away (i.coefficient c))
        (c i.U i.W i.hWU i.l n a) := by
    dsimp only [φ, RingHom.comp_apply, φ₀]
    rw [fractionBaseCoefficientRingHom_apply]
  have hu : IsUnit (φ i.e.val) := by
    rw [hφ]
    exact IsLocalization.Away.algebraMap_isUnit (i.coefficient c)
  have hf : (HomogeneousIdeal.irrelevant (A.grading i.U)).toIdeal.map φ = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem φ (HomogeneousIdeal.mem_irrelevant_of_mem _ i.hd i.e.property)) hu
  refine ⟨φ, hf, ?_, hφ⟩
  have hfrac (m : ℕ) (b : A.obj i.U) (hb : b ∈ A.grading i.U (m • i.d)) :
      ρ i (HomogeneousLocalization.Away.mk (A.grading i.U) i.e.property m b hb) *
        φ i.e.val ^ m = φ b := by
    rw [hφ i.d i.e, hφ (m • i.d) ⟨b, hb⟩, hρ i m ⟨b, hb⟩]
    simpa only [Localization.mk_eq_mk', map_pow] using
      (IsLocalization.mk'_spec (S := Localization.Away (i.coefficient c))
        (c i.U i.W i.hWU i.l (m • i.d) ⟨b, hb⟩)
        (⟨i.coefficient c ^ m, m, rfl⟩ : Submonoid.powers (i.coefficient c)))
  simpa only [GradedLineFractionChart.target, Category.assoc] using
    congrArg (fun f : i.domain c ⟶ Proj (A.grading i.U) ↦ f ≫ A.relProjι i.U)
      (fractionBase_spec_eq (A.grading i.U) φ hf i.hd i.e.property hu (ρ i) hfrac)

private theorem localTest_denominator {R : Type u} [CommRing R]
    {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (φ : R →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤) (x : X) :
    ∃ (d : ℕ) (a : R), 0 < d ∧ a ∈ 𝒜 d ∧ x ∈ X.basicOpen (φ a) := by
  obtain ⟨⟨d, a, hd, ha⟩, z, hz⟩ :=
    (Proj.openCoverOfMapIrrelevantEqTop 𝒜 φ hf).exists_eq x
  refine ⟨d, a, hd, ha, ?_⟩
  rw [← hz]
  exact z.property

attribute [local irreducible] Proj.fromOfGlobalSections

/-- The comparison of a prescribed fraction morphism with the trivialized Proj map
holds on an open neighbourhood of every point of the test scheme.

This is the local geometric step in the proof of
`gradedLineFraction_test`.  The unit ideal hypothesis supplies a positive-degree
basic-open neighbourhood; the free-frame and fraction formulas identify the two
maps there.  The global equality is obtained from this local statement by
`Scheme.hom_ext_of_forall`.

Source: Stacks Project, Constructions, Tag 01NK, lemma-invertible-map-into-proj,
and Tag 01O9, lemma-invertible-map-into-relative-proj, characterizations (2) and
(3) (blueprint: lem-trf-graded-line-fraction-test-local).
-/
theorem gradedLineFraction_test_local
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
    (hρ : GradedLineFractionChart.FractionFormula c ρ)
    (F : T ⟶ A.relProj)
    (hF : ∀ i : GradedLineFractionChart h A L, i.source c ≫ F = i.target c ρ)
    (W : Scheme.{u}) (j : W ⟶ T) (hj : IsOpenImmersion j)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (α : A.obj V →+* Γ(W, ⊤))
    (hα : ∀ (n : ℕ) (a : A.grading V n), α a =
      (unitSectionsEquiv ⊤).symm
        ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (ψ.evaluate j V q n a)))
    (hαgen : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤) :
    ∀ x : W, ∃ U : W.Opens, x ∈ U ∧
      U.ι ≫ j ≫ F =
        U.ι ≫ (Proj.fromOfGlobalSections (A.grading V) α hαgen ≫ A.relProjι V) := by
  classical
  let : IsOpenImmersion j := hj
  let := A.gradedAlgebra V
  intro x
  obtain ⟨d, a, hd, ha, hxa⟩ := localTest_denominator (A.grading V) α hαgen x
  obtain ⟨B₀, hB₀, hxB, hB⟩ := exists_isAffineOpen_mem_and_subset
    (show j x ∈ (j ''ᵁ (⊤ : W.Opens)) ⊓ h ⁻¹ᵁ V.1 from
      ⟨⟨x, trivial, rfl⟩, q trivial⟩)
  let B : T.affineOpens := ⟨B₀, hB₀⟩
  have hBj : B.1 ≤ j ''ᵁ (⊤ : W.Opens) := hB.trans inf_le_left
  have hBV : B.1 ≤ h ⁻¹ᵁ V.1 := hB.trans inf_le_right
  obtain ⟨l, hl, he⟩ := localTest_frame j L e B.1 hBj
  have hcoef (n : ℕ) (b : A.grading V n) :
      W.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ B.1 ≤ ⊤)).op (α b) =
        j.app B.1 (c V B hBV l n b) :=
    localTest_coefficient ψ P hP0 hPs j V q e α hα B.1 hBV l he n b _
      (hc V B hBV l hl n b)
  let i : GradedLineFractionChart h A L := ⟨V, B, hBV, l, hl, d, hd, ⟨a, ha⟩⟩
  have hxi : j x ∈ T.basicOpen (i.coefficient c) := by
    have hh : x ∈ W.basicOpen (j.app B.1 (i.coefficient c)) := by
      rw [← hcoef d ⟨a, ha⟩, Scheme.basicOpen_res]
      exact ⟨hxB, hxa⟩
    rw [← Scheme.preimage_basicOpen j] at hh
    exact hh
  have hrange := localTest_source_range c i
  have hsourceB : (⊤ : (i.domain c).Opens) ≤ i.source c ⁻¹ᵁ B.1 := by
    intro t _
    apply T.basicOpen_le (i.coefficient c)
    rw [← hrange]
    exact ⟨t, rfl⟩
  have hle : Set.range (i.source c) ⊆ Set.range j := by
    rintro t ⟨y, rfl⟩
    obtain ⟨w, _, hw⟩ := hBj (hsourceB (show y ∈ ⊤ from trivial))
    exact ⟨w, hw⟩
  let β : i.domain c ⟶ W := IsOpenImmersion.lift j (i.source c) hle
  have hβj : β ≫ j = i.source c := IsOpenImmersion.lift_fac j (i.source c) hle
  have hβB : (⊤ : (i.domain c).Opens) ≤ β ⁻¹ᵁ (j ⁻¹ᵁ B.1) := by
    rw [← Scheme.Hom.comp_preimage, hβj]
    exact hsourceB
  obtain ⟨φ, hf, htarget, hφ⟩ := localTest_chart ψ P hP0 hPs c hc ρ hρ i
  have hring : β.appTop.hom.comp α = (Scheme.ΓSpecIso _).inv.hom.comp φ := by
    apply localTest_ringHom_ext (A.grading V)
    intro n b
    have hres : W.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ B.1 ≤ ⊤)).op ≫
        β.appLE (j ⁻¹ᵁ B.1) ⊤ hβB = β.appTop := by
      rw [Scheme.Hom.map_appLE]
      rfl
    have hcomp : j.app B.1 ≫ β.appLE (j ⁻¹ᵁ B.1) ⊤ hβB =
        CommRingCat.ofHom (algebraMap Γ(T, B.1) (Localization.Away (i.coefficient c))) ≫
          (Scheme.ΓSpecIso _).inv := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact (localTest_app_congr hβj B.1 _ hsourceB).trans
        (localTest_source_app c i hsourceB)
    have hh := congrArg (β.appLE (j ⁻¹ᵁ B.1) ⊤ hβB) (hcoef n b)
    change β.appTop (α b) = (Scheme.ΓSpecIso _).inv (φ b)
    rw [hφ n b]
    calc
      _ = (j.app B.1 ≫ β.appLE (j ⁻¹ᵁ B.1) ⊤ hβB) (c V B hBV l n b) := by
        simpa only [← CommRingCat.comp_apply, hres] using hh
      _ = _ := by rw [hcomp]; rfl
  have hgen : (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal.map
      (β.appTop.hom.comp α) = ⊤ := by
    rw [← Ideal.map_map, hαgen, Ideal.map_top]
  have hproj : β ≫ Proj.fromOfGlobalSections (A.grading V) α hαgen =
      Proj.fromOfGlobalSections (A.grading V) ((Scheme.ΓSpecIso _).inv.hom.comp φ)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
    simpa only [hring] using
      Proj.comp_fromOfGlobalSections (A.grading V) β α hαgen hgen
  have heq : β ≫ j ≫ F =
      β ≫ (Proj.fromOfGlobalSections (A.grading V) α hαgen ≫ A.relProjι V) := by
    calc
      _ = i.source c ≫ F := by rw [← Category.assoc, hβj]
      _ = i.target c ρ := hF i
      _ = Proj.fromOfGlobalSections (A.grading V)
          ((Scheme.ΓSpecIso _).inv.hom.comp φ)
          (by rw [← Ideal.map_map, hf, Ideal.map_top]) ≫ A.relProjι V := htarget
      _ = (β ≫ Proj.fromOfGlobalSections (A.grading V) α hαgen) ≫ A.relProjι V :=
        congrArg (fun f : i.domain c ⟶ Proj (A.grading V) ↦ f ≫ A.relProjι V) hproj.symm
      _ = _ := Category.assoc _ _ _
  have : IsOpenImmersion (β ≫ j) := by rw [hβj]; infer_instance
  have : IsOpenImmersion β := IsOpenImmersion.of_comp β j
  have hxO : x ∈ β.opensRange := by
    have hh : j x ∈ (i.source c).opensRange := by rw [hrange]; exact hxi
    obtain ⟨t, ht⟩ := hh
    refine ⟨t, j.isOpenEmbedding.injective ?_⟩
    change (β ≫ j) t = j x
    rw [hβj]
    exact ht
  refine ⟨β.opensRange, hxO, ?_⟩
  have hh := congrArg (fun g ↦ β.isoOpensRange.inv ≫ g) heq
  simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hh

end AlgebraicGeometry.Scheme.Modules
