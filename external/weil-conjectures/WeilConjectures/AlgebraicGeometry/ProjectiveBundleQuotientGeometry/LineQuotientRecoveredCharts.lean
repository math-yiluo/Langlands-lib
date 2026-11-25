/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import all WeilConjectures.AlgebraicGeometry.Line.LineQuotientHomogeneousFractionMap
import all WeilConjectures.AlgebraicGeometry.Graded.GradedLineHomogeneousFractionAtlas
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # LineQuotientRecoveredCharts

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks Project, Constructions, Tags 01OA and 01O4, second inverse calculation
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry
open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj

private theorem fraction_self {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) :
    degreeOneQuotientFraction A U e 1 e = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [degreeOneQuotientFraction, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [pow_one, one_mul]

private theorem fraction_scalar {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) (r : Γ(S, U.1)) :
    degreeOneQuotientFraction A U e 0
      ⟨algebraMap Γ(S, U.1) _ r, SetLike.algebraMap_mem_graded _ r⟩ =
        quotientFractionScalar A U e.val r := by
  apply HomogeneousLocalization.val_injective
  simp only [degreeOneQuotientFraction, HomogeneousLocalization.Away.val_mk,
    quotientFractionScalar, HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.val_mk, pow_zero,
    SetLike.GradeZero.coe_one]

private theorem fraction_add {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) (d : ℕ) (c c' : A.grading U d) :
    degreeOneQuotientFraction A U e d (c + c') =
      degreeOneQuotientFraction A U e d c + degreeOneQuotientFraction A U e d c' := by
  apply HomogeneousLocalization.val_injective
  simp only [degreeOneQuotientFraction, HomogeneousLocalization.val_add,
    HomogeneousLocalization.Away.val_mk, Submodule.coe_add]
  exact (Localization.add_mk_self _ _ _).symm

private theorem fraction_mul {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) (d d' : ℕ)
    (c : A.grading U d) (c' : A.grading U d') :
    degreeOneQuotientFraction A U e (d + d')
        ⟨c.val * c'.val, SetLike.mul_mem_graded c.property c'.property⟩ =
      degreeOneQuotientFraction A U e d c * degreeOneQuotientFraction A U e d' c' := by
  apply HomogeneousLocalization.val_injective
  simp only [degreeOneQuotientFraction, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul]
  congr 1
  apply Subtype.ext
  exact pow_add e.val d d'

private theorem coefficient_eq_fraction {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1))
    (κ : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+* Γ(T, W.1))
    (hscalar : ∀ r : Γ(S, U.1),
      κ (quotientFractionScalar (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m).val r) = h.appLE U.1 W.1 hWU r)
    (hgenerator : ∀ v : Γ(E, U.1),
      q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 v)) =
          κ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
            (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U v)) • l)
    (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d) :
    ψ.quotientCoefficient U W hWU l d c =
      κ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) d c) := by
  let P := fun {V : T.Opens} (l : Γ(L, V)) (n : ℕ) ↦ quotientFramePower l n
  have hP0 : ∀ (V : T.Opens) (l : Γ(L, V)), P l 0 = unitSectionsEquiv V 1 :=
    fun _ _ ↦ rfl
  have hPs : ∀ (V : T.Opens) (l : Γ(L, V)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n) := fun _ _ _ ↦ rfl
  let b := ψ.quotientCoefficient U W hWU l
  have hb : ∀ n z, b n z • P l n =
      (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n z) :=
    quotientCoefficient_smul_frame ψ U W hWU l hl
  let β := atlasCoefficientRingHom ψ P hP0 hPs U W hWU l hl b hb
  have hβ (n : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n) :
      β z.val = b n z :=
    atlasCoefficientRingHom_apply ψ P hP0 hPs U W hWU l hl b hb n z
  have hβscalar (r : Γ(S, U.1)) : β (algebraMap Γ(S, U.1) _ r) =
      h.appLE U.1 W.1 hWU r := by
    have hz : (⟨algebraMap Γ(S, U.1) _ r, Submodule.algebraMap_mem r⟩ :
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 0) =
        r • ⟨1, SetLike.one_mem_graded _⟩ := by
      ext
      change algebraMap Γ(S, U.1) (SymmetricAlgebra Γ(S, U.1) Γ(E, U.1)) r =
        r • (1 : SymmetricAlgebra Γ(S, U.1) Γ(E, U.1))
      simp only [Algebra.smul_def, mul_one]
    calc
      β (algebraMap Γ(S, U.1) _ r) =
          b 0 ⟨algebraMap Γ(S, U.1) _ r, Submodule.algebraMap_mem r⟩ :=
            hβ 0 ⟨algebraMap Γ(S, U.1) _ r, Submodule.algebraMap_mem r⟩
      _ = h.appLE U.1 W.1 hWU r := by
        rw [hz, atlasCoefficient_smul ψ P hP0 hPs U W hWU l hl b hb,
          atlasCoefficient_one ψ P hP0 hPs U W hWU l hl b hb, mul_one]
  have hβgen (v : Γ(E, U.1)) : β (quotientSymmetricGenerator E U v).val =
      κ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U v)) := by
    rw [hβ]
    change ψ.quotientCoefficient U W hWU l 1 (quotientSymmetricGenerator E U v) = _
    rw [quotientCoefficient_generator ψ hψ U W hWU l hl]
    apply hl.smul_left_injective
    dsimp only
    rw [quotientGeneratorCoefficient_smul h E L q U W hWU l hl, hgenerator]
  apply (hβ d c).symm.trans
  obtain ⟨c, hc⟩ := c
  change c ∈ (SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1)).range ^ d at hc
  induction hc using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    rw [hβscalar, fraction_scalar, hscalar]
  | add x y i hx hy ihx ihy =>
    change β (x + y) = κ (degreeOneQuotientFraction _ U _ i (⟨x, hx⟩ + ⟨y, hy⟩))
    rw [map_add, fraction_add, map_add, ihx, ihy]
  | mul_mem i x hx ih v hv =>
    obtain ⟨v, rfl⟩ := hv
    change β (x * (quotientSymmetricGenerator E U v).val) =
      κ (degreeOneQuotientFraction _ U _ (i + 1) _)
    rw [map_mul, ih, hβgen]
    exact (map_mul κ _ _).symm.trans (congrArg κ
      (fraction_mul (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) i 1 ⟨x, hx⟩
        (quotientSymmetricGenerator E U v)).symm)

private theorem affine_factorization {T : Scheme.{u}} (W : T.affineOpens)
    (C : CommRingCat.{u}) (k : W.1.toScheme ⟶ Spec C) :
    W.2.isoSpec.inv ≫ k = Spec.map
      ((Scheme.ΓSpecIso C).inv ≫ k.appTop ≫ W.1.topIso.hom) := by
  rw [IsAffineOpen.isoSpec_inv, Category.assoc, ← Scheme.isoSpec_inv_naturality,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  rfl

private theorem normalized_chart_eq {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : ψ.HasQuotientFractionCharts h E L q F)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1))
    (hm : quotientGeneratorCoefficient h E L q U W hWU l m = 1)
    (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val)))
    (hk : W.1.ι ≫ a = k ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
    (hc : ∀ (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W hWU l d c =
        W.1.topIso.hom (k.appTop ((Scheme.ΓSpecIso _).inv
          (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
            (quotientSymmetricGenerator E U m) d c)))) :
    quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l m) ≫ F =
      quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l m) ≫ a := by
  obtain ⟨ρ, hρ⟩ := (hF.2 U W hWU l hl).2.2.2.1 m
  let κ := (Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom
  have heq : ρ = (algebraMap Γ(T, W.1) _).comp κ.hom := by
    let := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
    ext z
    obtain ⟨d, c, hcd, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).property z
    have hc' : c ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d := by
      simpa only [smul_eq_mul, mul_one] using hcd
    change ρ (degreeOneQuotientFraction _ U _ d ⟨c, hc'⟩) = _
    rw [hρ.1, Localization.mk_eq_mk']
    apply (IsLocalization.mk'_eq_iff_eq_mul).2
    change algebraMap Γ(T, W.1) _ (ψ.quotientCoefficient U W hWU l d ⟨c, hc'⟩) =
      algebraMap Γ(T, W.1) _ (κ _) * algebraMap Γ(T, W.1) _
        (quotientGeneratorCoefficient h E L q U W hWU l m ^ d)
    rw [hm, one_pow, map_one, mul_one, hc]
    rfl
  rw [hρ.2.2.1, heq]
  change Spec.map (κ ≫ CommRingCat.ofHom (algebraMap Γ(T, W.1) _)) ≫ _ = _
  rw [Spec.map_comp, ← affine_factorization W _ k]
  simp only [quotientFractionSource, Category.assoc, hk]

private theorem symmetric_cover {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] (𝒜 : ℕ → Submodule R (SymmetricAlgebra R M)) [GradedAlgebra 𝒜]
    (hι : ∀ m, SymmetricAlgebra.ι R M m ∈ 𝒜 1) :
    (⨆ m : M, Proj.basicOpen 𝒜 (SymmetricAlgebra.ι R M m)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top' 𝒜 (SymmetricAlgebra.ι R M) (fun m ↦ ⟨1, hι m⟩)
  apply top_unique
  intro x hx
  clear hx
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact (Algebra.adjoin (𝒜 0) (Set.range (SymmetricAlgebra.ι R M))).algebraMap_mem
      (algebraMap R (𝒜 0) r)
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul x y hx hy => exact mul_mem hx hy
  | add x y hx hy => exact add_mem hx hy

private theorem symmetric_generator_cover {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (U : S.affineOpens) :
    (⨆ m : Γ(E, U.1), Proj.basicOpen
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val) = ⊤ := by
  let := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
  exact symmetric_cover ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
    (fun m ↦ (quotientSymmetricGenerator E U m).property)

private theorem exists_generator_chart {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (x : T) :
    ∃ (U : S.affineOpens) (W : T.affineOpens) (_ : x ∈ W.1)
      (_hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (_hWa : W.1 ≤ a ⁻¹ᵁ
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
      (m : Γ(E, U.1))
      (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val))),
      W.1.ι ≫ a = k ≫
        Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
          (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
          (by decide : 0 < (1 : ℕ)) ≫
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U := by
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h x) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  let := A.gradedAlgebra U
  have ha' : a ≫ A.relProjHom = h := ha
  have hxU : a x ∈ A.relProjHom ⁻¹ᵁ U.1 := by
    change (a ≫ A.relProjHom) x ∈ U.1
    rw [ha]
    exact hxV
  rw [A.relProjHom_preimage] at hxU
  obtain ⟨y, hy⟩ := hxU
  have hycover : y ∈ ⨆ m : Γ(E, U.1),
      Proj.basicOpen (A.grading U) (quotientSymmetricGenerator E U m).val := by
    rw [symmetric_generator_cover]
    trivial
  obtain ⟨m, hym⟩ := TopologicalSpace.Opens.mem_iSup.mp hycover
  let j := Proj.awayι (A.grading U) (quotientSymmetricGenerator E U m).val
    (quotientSymmetricGenerator E U m).property (by decide : 0 < (1 : ℕ)) ≫ A.relProjι U
  have hxj : x ∈ a ⁻¹ᵁ j.opensRange := by
    change a x ∈ j.opensRange
    rw [Scheme.Hom.opensRange_comp, Proj.opensRange_awayι]
    exact ⟨y, hym, hy⟩
  obtain ⟨W, hW, hxW, hWj⟩ := exists_isAffineOpen_mem_and_subset hxj
  let Wa : T.affineOpens := ⟨W, hW⟩
  have hWa : W ≤ a ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1) := by
    apply hWj.trans
    apply a.preimage_mono
    rw [A.relProjHom_preimage, Scheme.Hom.opensRange_comp]
    exact Set.image_subset_range _ _
  have hWU : W ≤ h ⁻¹ᵁ U.1 := by
    simpa only [← Scheme.Hom.comp_preimage, ha'] using hWa
  have hrange : Set.range (W.ι ≫ a) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hWj z.2
  refine ⟨U, Wa, hxW, hWU, hWa, m, IsOpenImmersion.lift j (W.ι ≫ a) hrange, ?_⟩
  exact (IsOpenImmersion.lift_fac j (W.ι ≫ a) hrange).symm

/-- The pulled tautological quotient has the original morphism's fraction charts. -/
theorem lineQuotient_recovered_charts {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback a).obj D.line))
    (hψ : ψ.ExtendsLineQuotient h E _ (pulledQuotient D h a ha)) :
    ψ.HasQuotientFractionCharts h E _ (pulledQuotient D h a ha) a ∧
      RecoveredFractionCoefficients D h a ψ := by
  have hcoeff : RecoveredFractionCoefficients D h a ψ := by
    intro U W hWU hWa m k hk d c
    obtain ⟨hl, hscalar, hgenerator⟩ :=
      lineQuotient_pulled_chart_normalization h E D a ha U W hWU hWa m k hk
    exact coefficient_eq_fraction h E _ _ ψ hψ U W hWU _ hl m
      ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom).hom
      hscalar hgenerator d c
  have : D.line.IsInvertible := D.invertible
  have := ((invertible_pullback_tensor a).1 D.line).2
  have : Epi (pulledQuotient D h a ha) := by
    let : Epi D.quotient := D.surjective
    let : (tensorPullback a).IsLeftAdjoint := (tensorPullbackSectionAdjunction a).isLeftAdjoint
    unfold pulledQuotient
    infer_instance
  obtain ⟨ψ₀, hψ₀, huniq, _, F, hF, _⟩ :=
    line_quotient_homogeneous_fraction_map h E _ (pulledQuotient D h a ha)
  have hψeq : ψ = ψ₀ := huniq ψ hψ
  have hF : ψ.HasQuotientFractionCharts h E _ (pulledQuotient D h a ha) F :=
    hψeq.symm ▸ hF
  have hFa : F = a := by
    apply Scheme.hom_ext_of_forall
    intro x
    obtain ⟨U, W, hxW, hWU, hWa, m, k, hk⟩ := exists_generator_chart h E a ha x
    obtain ⟨hl, hscalar, hgenerator⟩ :=
      lineQuotient_pulled_chart_normalization h E D a ha U W hWU hWa m k hk
    let l := pulledTautologicalGenerator D a U W.1 hWa m
    have hcm : quotientGeneratorCoefficient h E _ (pulledQuotient D h a ha)
        U W hWU l m = 1 := by
      rw [← quotientCoefficient_generator ψ hψ U W hWU l hl,
        hcoeff U W hWU hWa m k hk 1 (quotientSymmetricGenerator E U m), fraction_self]
      simp only [map_one]
    let f := quotientFractionSource W
      (quotientGeneratorCoefficient h E _ (pulledQuotient D h a ha) U W hWU l m)
    have hf := normalized_chart_eq h E _ _ ψ F a hF U W hWU l hl m hcm k hk
      (hcoeff U W hWU hWa m k hk)
    refine ⟨f.opensRange, ?_, ?_⟩
    · rw [quotientFractionSource_opensRange, hcm, Scheme.basicOpen_one]
      exact hxW
    · rw [← cancel_epi (Scheme.Hom.isoOpensRange f).hom]
      simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using hf
  exact ⟨hFa ▸ hF, hcoeff⟩

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
