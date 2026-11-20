import Langlands.GroupScheme.Trigonalizable.PrimeToPart
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitPerfectConnected
import Langlands.GroupScheme.Trigonalizable.EtaleExtensionSplitStatement
import Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction

/-! # Milne 16.26 (b), and the whole of 16.26, from the étale case SGA 3 XVII 5.2.3 i) c) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit

open ClosedAdditivePolynomial in
/-- In characteristic zero no correction is needed: one-step splitting holds for every `D(Λ)`. -/
theorem oneStepSplitting_of_charZero {k : Type u} [Field k] [CharZero k] (Λ : Type u)
    [AddCommGroup Λ] : OneStepSplitting k Λ := by
  intro E _ _ q hflat hsurj _ a ha χ b hconj hlin
  refine exists_section_of_solvable q hflat hsurj a ha χ b hconj hlin fun hf => Or.inl ?_
  have hmonic := closedPolynomial_monic a hf
  have hpos := natDegree_pos a ha hf
  have htaylor := RelativeRoot.AdditivePolynomial.taylor_eq_of_mem_span hmonic hpos
    (taylor_mem_span a ha)
  have h0 : (closedPolynomial a).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact eval_zero a ha
  have hNc : (closedPolynomial a).coeff (closedPolynomial a).natDegree ≠ 0 := by
    rw [hmonic.coeff_natDegree]
    exact one_ne_zero
  have hN1 : (closedPolynomial a).natDegree = 1 := by
    rcases PerfectCorrection.eq_zero_or_eq_pow_of_coeff_ne_zero 1 htaylor hNc with h | ⟨s, hs⟩
    · omega
    · rw [hs, one_pow]
  have hfX : closedPolynomial a = X := by
    rw [eq_X_add_C_of_natDegree_le_one hN1.le, h0, ← hN1, hmonic.coeff_natDegree, C_1, one_mul,
      C_0, add_zero]
  intro m
  exact ⟨m, by rw [hfX, eval_X]⟩

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
  [IsAffineHom G.X.hom] (i : U ⟶ G) {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
  (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- **Milne 16.26(b), from the étale prime-to-`p` case.** Over a perfect field, if the closed
normal unipotent subgroup is smooth and connected, the extension splits. -/
theorem exists_section_of_perfect_of_smooth
    (hP : EtaleDiagonalizableExtensionSplitStatement.{u}) [PerfectField k]
    (hsm : Smooth U.X.hom) (hconn : ConnectedSpace U.X.left)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _ := by
  have hT := admitsTower i q hi hU hN hq
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rcases expChar_is_prime_or_one k p with hprime | h1
  swap
  · subst h1
    have : CharZero k := charZero_of_expChar_one' k
    exact exists_section_of_admitsTower' (oneStepSplitting_of_charZero Λ) hT
  have : Fact p.Prime := ⟨hprime⟩
  have : CharP k p := (expChar_prime_iff (R := k) hprime).mp hp
  obtain ⟨e, he0, he, hek⟩ := PrimeToPart.exists_exponent p Λ
  let K := PrimeToPart.saturation p Λ e
  let g := QuotientAddGroup.mk' K
  let ι₁ := Diagonalizable.restrictMap (CommRingCat.of k) g
  have hι₁ : IsClosedSubgroup ι₁ :=
    Diagonalizable.isClosedImmersion_restrictMap _ g (QuotientAddGroup.mk'_surjective K)
  have h0 : i ≫ q = 0 := SplitSolvable.kernel_comp_eq_zero hq
  let incl := SubgroupPreimage.inclusion q ι₁
  let π₁ := SubgroupPreimage.projection q ι₁
  let z := SubgroupPreimage.kernelInclusion q ι₁ i h0
  have hinclc : IsClosedSubgroup incl := SubgroupPreimage.isClosedSubgroup q ι₁ hι₁
  have : IsClosedImmersion incl.hom.hom.left := hinclc
  have : Mono incl.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom (SubgroupPreimage.groupScheme q ι₁).X.hom :=
    SubgroupPreimage.isAffineHom q ι₁ hι₁
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme q ι₁).X.hom := by
    rw [← Over.w incl.hom.hom]
    infer_instance
  have hzincl : z ≫ incl = i := SubgroupPreimage.kernelInclusion_comp_inclusion q ι₁ i h0
  have hz : IsClosedSubgroup z := by
    have : IsClosedImmersion i.hom.hom.left := hi
    have hc : IsClosedImmersion (z.hom.hom.left ≫ incl.hom.hom.left) := by
      change IsClosedImmersion ((z ≫ incl).hom.hom.left)
      rw [hzincl]
      exact hi
    exact IsClosedImmersion.of_comp z.hom.hom.left incl.hom.hom.left
  have hzq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) π₁ :=
    SubgroupPreimage.isFppfQuotient_projection q ι₁ i h0 hq
  have hzN : (SubgroupFunctor.range z).IsNormal := by
    intro T x y _ hy
    obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    have hmem : (x ≫ incl.hom.hom) * (u ≫ i.hom.hom) * (x ≫ incl.hom.hom)⁻¹ ∈
        (SubgroupFunctor.range i).carrier T :=
      hN T (x ≫ incl.hom.hom) (u ≫ i.hom.hom) trivial (SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩)
    obtain ⟨u', hu'⟩ := SubgroupFunctor.mem_range.mp hmem
    refine SubgroupFunctor.mem_range.mpr ⟨u', ?_⟩
    apply (cancel_mono incl.hom.hom).mp
    have hzi : z.hom.hom ≫ incl.hom.hom = i.hom.hom := by
      rw [← Grp.comp_hom_hom, hzincl]
    rw [Category.assoc, hzi, hu', MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc, hzi]
  obtain ⟨hfin, hcop⟩ :=
    PrimeToPart.finite_and_coprime_card (M := Λ ⧸ K) e he0 he (PrimeToPart.e_smul_eq_zero p e)
  obtain ⟨σ₁', hσ₁'⟩ := hP k p (SubgroupPreimage.groupScheme q ι₁) U z (Λ ⧸ K) π₁ inferInstance
    hfin hcop hz hsm hconn hU hzN hzq
  have hσ₁ : (σ₁' ≫ incl) ≫ q = ι₁ := by
    rw [Category.assoc, subgroupIntersection_condition q ι₁, ← Category.assoc, hσ₁',
      Category.id_comp]
  have hrel : OneStepSplittingRel k Λ ι₁ :=
    oneStepSplittingRel_of ι₁ fun a χ ha hst =>
      PrimeToPart.relativeSolvable p e he hek a χ ha hst
  obtain ⟨s, hs, -⟩ := exists_section_of_admitsTower_rel hrel hT (σ₁' ≫ incl) hσ₁
  exact ⟨s, hs⟩

end Langlands.GroupScheme.TrigonalizableExtensionSplit

namespace Langlands.GroupScheme

open TrigonalizableExtensionSplit

/-- **Milne 16.26**, all three cases, from the étale prime-to-`p` case of SGA 3 XVII 5.2.3. -/
theorem trigonalizableExtensionSplit_of_etale
    (hP : EtaleDiagonalizableExtensionSplitStatement.{u}) :
    TrigonalizableExtensionSplitStatement.{u} := by
  intro k _ G _ _ U i Λ _ _ q hi hU hN hq hcase
  rcases hcase with hac | ⟨hperf, hsm, hconn⟩ | ⟨hperf, hDc⟩
  · exact exists_section_of_isAlgClosed i q hi hU hN hq
  · exact exists_section_of_perfect_of_smooth i q hP hsm hconn hi hU hN hq
  · exact exists_section_of_perfect_of_connected i q hDc hi hU hN hq

end Langlands.GroupScheme
