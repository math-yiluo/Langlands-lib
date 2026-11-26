import Langlands.GroupScheme.Rational.LanglandsCharacterRestriction
import Langlands.Global.ArthurParabolicSpacesStatement
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.RenardLeviCentralDecompositionProof

/-! # Proof of the comparison of `𝔞_P`, `𝔞_P^*` with the relative root data (Arthur (5.1))

For a standard parabolic `P_S` with standard Levi `M_S` and maximal split torus `T`, the
restriction `X(P_S) ⊗ ℝ → X(T) ⊗ ℝ` factors as `X(P_S) ⊗ ℝ → X(M_S) ⊗ ℝ → X(T) ⊗ ℝ`. The first
map is bijective, because `P_S` and `M_S` are the dynamic parabolic and centralizer of one
standard cocharacter, and the second map is injective with image the coroot annihilator. The
assertions about the transpose follow by linear algebra.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.Global.ArthurParabolicSpaces

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

section LinearAlgebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- If `C` lies in the kernel of `f` and a complement `W` of `C` meets the kernel trivially,
then the kernel is `C`. -/
theorem ker_eq_of_isCompl_of_disjoint (f : E →ₗ[ℝ] F) (W C : Submodule ℝ E)
    (hc : IsCompl W C) (hC : C ≤ LinearMap.ker f) (hW : Disjoint W (LinearMap.ker f)) :
    LinearMap.ker f = C := by
  refine le_antisymm (fun v hv => ?_) hC
  have hv' : v ∈ W ⊔ C := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.mp hv'
  have hac : a ∈ LinearMap.ker f := by
    have h := Submodule.sub_mem _ hv (hC hc')
    rwa [add_sub_cancel_right] at h
  have h0 : a = 0 := (Submodule.disjoint_def.mp hW) a ha hac
  subst h0
  simpa using hc'

/-- A surjective linear map restricts to a bijection on a complement of its kernel. -/
theorem bijective_domRestrict_of_isCompl (f : E →ₗ[ℝ] F) (hf : Function.Surjective f)
    (W : Submodule ℝ E) (hc : IsCompl W (LinearMap.ker f)) :
    Function.Bijective (f.domRestrict W) := by
  apply (Function.bijective_iff_existsUnique _).2
  intro z
  obtain ⟨y, ⟨hy, hfy⟩, huniq⟩ := Langlands.LinearAlgebra.existsUnique_preimage_of_isCompl f hf W hc.symm z
  exact ⟨⟨y, hy⟩, hfy, fun w hw => Subtype.ext (huniq w ⟨w.property, hw⟩)⟩

end LinearAlgebra

/-- **Arthur 2005, (5.1) and p.26, for standard parabolic subgroups.** Restriction of real
rational characters from `P_S` to the maximal split torus is injective with image the coroot
annihilator of `S`; its transpose is surjective with kernel the real span of the coroots of `S`
and restricts to a bijection on the root annihilator of `S`. -/
theorem parabolicSpacesComparison : ParabolicSpacesComparisonStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν D S hS
  -- `P_S` and `M_S` are the dynamic parabolic and centralizer of one standard cocharacter.
  obtain ⟨⟨ζ, hζ⟩, hall⟩ := standardCocharacter k G hG T i hi ν hν S hS
  obtain ⟨hPζ, hLζ, -⟩ := hall ζ hζ
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.parabolicHom i ν S) :=
    hPζ ▸ Standard.isRepresentedBy_parabolicHom i ν S
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.leviHom i ν S) :=
    hLζ ▸ Standard.isRepresentedBy_leviHom i ν S
  have hPc := Standard.isClosedSubgroup_parabolicHom i ν S
  let : Mono (Standard.parabolicHom i ν S) :=
    (Grp.forget _).mono_of_mono_map (f := Standard.parabolicHom i ν S)
      (Standard.isRepresentedBy_parabolicHom i ν S).1
  let : Mono (Standard.leviHom i ν S) :=
    (Grp.forget _).mono_of_mono_map (f := Standard.leviHom i ν S)
      (Standard.isRepresentedBy_leviHom i ν S).1
  have hcl : Dynamic.centralizerToParabolic hP hL = Standard.leviToParabolic i ν S := by
    apply (cancel_mono (Standard.parabolicHom i ν S)).mp
    rw [Dynamic.centralizerToParabolic_comp, Standard.leviToParabolic_comp]
  -- The maximal split torus inside `M_S`.
  let tL : T.toGrp ⟶ Standard.leviScheme i ν S :=
    (Standard.isRepresentedBy_leviHom i ν S).factorHom i
      ((range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν S))
  have htL : tL ≫ Standard.leviHom i ν S = i :=
    (Standard.isRepresentedBy_leviHom i ν S).factorHom_comp i _
  have htP : torusToParabolic k i ν S = tL ≫ Standard.leviToParabolic i ν S := by
    apply (cancel_mono (Standard.parabolicHom i ν S)).mp
    rw [torusToParabolic_comp, Category.assoc, Standard.leviToParabolic_comp, htL]
  -- Restriction from `P_S` factors through `M_S`.
  have hfac : restrictToTorus k i ν S =
      (rationalCharacterRestrictReal tL).comp
        (rationalCharacterRestrictReal (Standard.leviToParabolic i ν S)) := by
    unfold restrictToTorus
    rw [htP]
    apply AlgebraTensorModule.ext
    intro r χ
    change r ⊗ₜ[ℤ] characterRestrict (tL ≫ Standard.leviToParabolic i ν S) χ =
      r ⊗ₜ[ℤ] characterRestrict tL (characterRestrict (Standard.leviToParabolic i ν S) χ)
    rw [characterRestrict_comp, AddMonoidHom.comp_apply]
  -- Restriction from `P_S` to `M_S` is bijective.
  have hbij : Function.Bijective
      (rationalCharacterRestrictReal (Standard.leviToParabolic i ν S)) := by
    let e := LinearEquiv.baseChange ℤ ℝ _ _
      (Dynamic.parabolicCharacterEquiv hP hPc hL).toIntLinearEquiv
    have he : (e : _ →ₗ[ℝ] _) =
        rationalCharacterRestrictReal (Standard.leviToParabolic i ν S) := by
      apply AlgebraTensorModule.ext
      intro r χ
      change r ⊗ₜ[ℤ] Dynamic.parabolicCharacterEquiv hP hPc hL χ =
        r ⊗ₜ[ℤ] characterRestrict (Standard.leviToParabolic i ν S) χ
      rw [Dynamic.parabolicCharacterEquiv_apply, hcl]
    rw [← he]
    exact e.bijective
  -- Restriction from `M_S` to `T` has image the coroot annihilator.
  have hrangeL : (rationalCharacterRestrictReal tL).range = corootAnnihilator i D S :=
    standardLeviCharacterAnnihilator k G hG T i hi ν hν S hS _ (Standard.leviHom i ν S)
      (Standard.isClosedSubgroup_leviHom i ν S) (Standard.isRepresentedBy_leviHom i ν S)
      tL htL D
  -- Restriction from `M_S` to `T` is injective: it is so after further restriction to the
  -- split component of `M_S`.
  have hinjL : Function.Injective (rationalCharacterRestrictReal tL) := by
    have hcentral := standardLeviCentralDirections.2 k G hG T i hi ν hν S hS _
      (Standard.leviHom i ν S) (Standard.isClosedSubgroup_leviHom i ν S)
      (Standard.isRepresentedBy_leviHom i ν S)
    obtain ⟨A, a, ha⟩ := (splitComponentStatement k _ hcentral.1).1
    obtain ⟨_, f, hf, _, _, _, _⟩ := hcentral.2 A a ha
    have hft : CommGroupScheme.groupHom f ≫ tL = a := by
      apply (cancel_mono (Standard.leviHom i ν S)).mp
      rw [Category.assoc, htL, hf]
    have hinjA := (renardLeviCentralDecomposition k _ _ (𝟙 _) hcentral.1 hcentral.1 A A
      a a (𝟙 A) ha ha (by change (𝟙 A.toGrp) ≫ a ≫ 𝟙 _ = a; simp)).1.injective
    have hcomp : (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).comp
        (rationalCharacterRestrictReal tL) = rationalCharacterRestrictReal a := by
      rw [← hft]
      apply AlgebraTensorModule.ext
      intro r χ
      change r ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) (characterRestrict tL χ) =
        r ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f ≫ tL) χ
      rw [characterRestrict_comp, AddMonoidHom.comp_apply]
    intro x y hxy
    apply hinjA
    rw [← hcomp, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  -- Items 1 and 2.
  have hinj : Function.Injective (restrictToTorus k i ν S) := by
    rw [hfac, LinearMap.coe_comp]
    exact hinjL.comp hbij.1
  have hrange : LinearMap.range (restrictToTorus k i ν S) = corootAnnihilator i D S := by
    rw [hfac, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hbij.2), hrangeL]
  -- Item 3: surjectivity of the transpose.
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hp := isPerfPair_of_isSplitTorus hT
  have hsurj : Function.Surjective (toCharacterDual k i ν S) := by
    intro φ
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (restrictToTorus k i ν S)
      (LinearMap.ker_eq_bot.mpr hinj)
    obtain ⟨v, hv⟩ := hp.bijective_right.surjective
      (((realParameterPairing k (Standard.parabolicScheme i ν S)).flip φ).comp g)
    refine ⟨v, DFunLike.ext _ _ fun χ => ?_⟩
    rw [toCharacterDual_apply]
    have h1 := LinearMap.congr_fun hv (restrictToTorus k i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ))
    rw [LinearMap.flip_apply, LinearMap.comp_apply] at h1
    rw [h1, ← LinearMap.comp_apply g, hg, LinearMap.id_apply, LinearMap.flip_apply,
      realParameterPairing_tmul, one_mul]
  -- The decompositions of Renard V.3.13.
  obtain ⟨hcompl₁, hcompl₂, -⟩ :=
    (standardLeviRealDecomposition k G hG T i hi ν hν D).2.2.2 S S le_rfl hS
  -- The coroots of `S` lie in the kernel of the transpose.
  have hC : Submodule.span ℝ (D.realCorootsOf S) ≤ LinearMap.ker (toCharacterDual k i ν S) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    refine DFunLike.ext _ _ fun χ => ?_
    rw [toCharacterDual_apply]
    change _ = (0 : ℝ)
    have hmem : restrictToTorus k i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ) ∈ corootAnnihilator i D S := by
      rw [← hrange]
      exact LinearMap.mem_range_self _ _
    exact (mem_corootAnnihilator i D S _).mp hmem α hα
  -- The root annihilator of `S` meets the kernel of the transpose trivially.
  have hW : Disjoint (rootAnnihilator T S) (LinearMap.ker (toCharacterDual k i ν S)) := by
    rw [Submodule.disjoint_def]
    intro v hv hker
    apply hp.bijective_right.injective
    rw [map_zero]
    apply LinearMap.ext
    intro y
    rw [LinearMap.flip_apply, LinearMap.zero_apply]
    have hy : y ∈ corootAnnihilator i D S ⊔
        Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' S) :=
      hcompl₁.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, LinearMap.add_apply]
    have h₁ : pair T y₁ v = 0 := by
      rw [← hrange] at hy₁
      obtain ⟨m, rfl⟩ := hy₁
      rw [← realParameterPairing_toCharacterDual, LinearMap.mem_ker.mp hker, map_zero]
    have h₂ : pair T y₂ v = 0 := by
      have hv' := (rootAnnihilator_eq_cocharacterAnnihilator (T := T) S) ▸ hv
      exact (mem_cocharacterAnnihilator _ _).mp hv' y₂ hy₂
    rw [h₁, h₂, add_zero]
  -- Items 4 and 5.
  have hker : LinearMap.ker (toCharacterDual k i ν S) = Submodule.span ℝ (D.realCorootsOf S) :=
    ker_eq_of_isCompl_of_disjoint _ _ _ hcompl₂ hC hW
  refine ⟨hinj, hrange, hsurj, hker, ?_⟩
  apply bijective_domRestrict_of_isCompl _ hsurj
  rw [hker]
  exact hcompl₂

end Langlands.Global.ArthurParabolicSpaces
