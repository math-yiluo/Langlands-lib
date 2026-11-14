import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasisProof
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.Geometry.Building.RealTorusInvariantForm
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.Flat.Basic

/-! # Simple relative coroots and real fundamental weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace Langlands.LinearAlgebra

private theorem fundamental_root_basis
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : by
      haveI := hG.isAffineHom
      exact IsGenericCocharacter i ν) :
    haveI := hG.isAffineHom
    ∃ b : Module.Basis (simpleRelativeRoots i ν) ℝ (relativeRootSpanReal i),
      ∀ α, (b α : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] α.1 := by
  have := hG.isAffineHom
  obtain ⟨_, ⟨b, hb⟩, _⟩ := relativeSimpleRootBasis k G hG T i hi ν hν
  let e₁ := Submodule.toBaseChange.toLinearEquiv ℝ (relativeRootSpan i)
  let e₂ := Submodule.equivMapOfInjective
    (rationalRealTensorEquiv (characterLattice T)).toLinearMap
    (rationalRealTensorEquiv (characterLattice T)).injective
    ((relativeRootSpan i).baseChange ℝ)
  let e₃ := LinearEquiv.ofEq _ _ (map_relativeRootSpan_baseChange i)
  refine ⟨(b.baseChange ℝ).map ((e₁.trans e₂).trans e₃), ?_⟩
  intro α
  change rationalRealTensorEquiv (characterLattice T)
    ((relativeRootSpan i).subtype.baseChange ℝ ((b.baseChange ℝ) α)) = _
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, hb]
  change rationalRealTensorEquiv (characterLattice T)
    ((1 : ℝ) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] α.1)) = _
  simp

private theorem fundamental_pair_perfect
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (X C : Submodule ℝ (Vstar T))
    (hXC : IsCompl X C) :
    ((pair T).domRestrict₁₂ X (cocharacterAnnihilator C)).IsPerfPair := by
  have := hT.finite_realCharacterSpace
  have hp := isPerfPair_of_isSplitTorus hT
  let N := cocharacterAnnihilator C
  let p := (pair T).domRestrict₁₂ X N
  apply LinearMap.IsPerfPair.of_injective
  · apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxC : (x : Vstar T) ∈ C := by
      rw [← characterAnnihilator_cocharacterAnnihilator hT C,
        mem_characterAnnihilator]
      intro v hv
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) ⟨v, hv⟩
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hXC.disjoint x x.2 hxC
  · apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro v hv
    apply Subtype.ext
    apply hp.bijective_right.injective
    apply LinearMap.ext
    intro x
    obtain ⟨a, c, ha, hc, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hXC.codisjoint x
    change pair T (a + c) v = pair T (a + c) 0
    rw [map_add, LinearMap.add_apply, map_zero]
    have h₁ : pair T a v = 0 :=
      LinearMap.congr_fun (LinearMap.mem_ker.mp hv) ⟨a, ha⟩
    have h₂ : pair T c v = 0 :=
      (mem_cocharacterAnnihilator C v).mp v.2 c hc
    simp only [h₁, h₂, add_zero]

/-- The simple real coroot basis and both fundamental dual bases of Renard V.3.12. -/
theorem relativeFundamentalWeight : RelativeFundamentalWeightStatement.{u} := by
  classical
  intro k _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro ν hν D
  have hT := hi.isSplitSubtorus.1
  have := hT.finite_realCharacterSpace
  have := hT.finite_realCocharacterSpace
  have : Fintype (relativeWeylGroup i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup i hi)
  have hfin := (relativeSimpleRootBasis k G hG T i hi ν hν).1
  have : Fintype (simpleRelativeRoots i ν) := @Fintype.ofFinite _ hfin
  let X := relativeRootSpanReal i
  let C := LinearMap.range (rationalCharacterRestrictReal i)
  let N := cocharacterAnnihilator C
  let p := (pair T).domRestrict₁₂ X N
  have hp : p.IsPerfPair :=
    fundamental_pair_perfect hT X C (relativeCharacterRootComplement k G hG T i hi).2
  let B := relativeWeylInvariantForm i hT
  have hB : IsWeylInvariantInnerProduct i B :=
    ⟨relativeWeylInvariantForm_symm i hT,
      fun x hx => relativeWeylInvariantForm_pos i hT hx,
      fun w x y => relativeWeylInvariantForm_invariant i hT w x y⟩
  let Br := (B.restrict X).flip
  have hBr : Br.IsPerfPair := by
    have hinj : Function.Injective Br := by
      apply (LinearMap.ker_eq_bot).mp
      apply eq_bot_iff.mpr
      intro x hx
      by_contra hne
      have hxne : (x : Vstar T) ≠ 0 := fun h => hne (Subtype.ext h)
      have hz : B x x = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) x
      exact (hB.2.1 _ hxne).ne' hz
    have hinj' : Function.Injective Br.flip := by
      apply (LinearMap.ker_eq_bot).mp
      apply eq_bot_iff.mpr
      intro x hx
      by_contra hne
      have hxne : (x : Vstar T) ≠ 0 := fun h => hne (Subtype.ext h)
      have hz : B x x = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) x
      exact (hB.2.1 _ hxne).ne' hz
    exact LinearMap.IsPerfPair.of_injective hinj hinj'
  let e : X ≃ₗ[ℝ] N := Br.toPerfPair.trans p.flip.toPerfPair.symm
  have he (x y : X) : p x (e y) = B x y := by
    change p.flip (p.flip.toPerfPair.symm (Br.toPerfPair y)) x = _
    simp [Br]
  obtain ⟨b, hb⟩ := fundamental_root_basis G hG T i hi ν hν
  have hlen (α : simpleRelativeRoots i ν) : B (b α) (b α) ≠ 0 :=
    (hB.2.1 _ (by
      rw [hb]
      exact D.one_tmul_ne_zero i (simpleToRelativeRoot i ν α))).ne'
  let s : simpleRelativeRoots i ν → ℝˣ :=
    fun α => Units.mk0 (2 / B (b α) (b α)) (div_ne_zero (by norm_num) (hlen α))
  let cB : Module.Basis (simpleRelativeRoots i ν) ℝ N := (b.unitsSMul s).map e
  have hcB (α : simpleRelativeRoots i ν) :
      (cB α : V T) = D.realCoroot (simpleToRelativeRoot i ν α) := by
    have hmem : D.realCoroot (simpleToRelativeRoot i ν α) ∈ N := by
      rw [mem_cocharacterAnnihilator]
      rintro _ ⟨z, rfl⟩
      exact D.restrictedCharacter_coroot i B hB z (simpleToRelativeRoot i ν α)
    let c : N := ⟨D.realCoroot (simpleToRelativeRoot i ν α), hmem⟩
    have hEq : cB α = c := by
      apply hp.bijective_right.injective
      apply LinearMap.ext
      intro x
      change p x (cB α) = pair T x (D.realCoroot (simpleToRelativeRoot i ν α))
      rw [show cB α = e (s α • b α) from
        congrArg e (Module.Basis.unitsSMul_apply α), he]
      simp only [Units.smul_def, s, Units.val_mk0, Submodule.coe_smul,
        map_smul, smul_eq_mul]
      rw [RelativeRootReflectionData.realCoroot, D.coroot_formula i B hB]
      rw [hb]
      ring
    exact congrArg Subtype.val hEq
  let wB := cB.dualBasis.map p.toPerfPair.symm
  let vB := b.dualBasis.map p.flip.toPerfPair.symm
  have hwB (α β : simpleRelativeRoots i ν) :
      pair T (wB α) (D.realCoroot (simpleToRelativeRoot i ν β)) =
        if β = α then 1 else 0 := by
    rw [← hcB β]
    change p (p.toPerfPair.symm (cB.dualBasis α)) (cB β) = _
    simp [Finsupp.single_apply]
  have hvB (α β : simpleRelativeRoots i ν) :
      eval T β.1 (vB α) = if β = α then 1 else 0 := by
    rw [eval_eq_pair, ← hb β]
    change p.flip (p.flip.toPerfPair.symm (b.dualBasis α)) (b β) = _
    simp [Finsupp.single_apply]
  refine ⟨⟨cB, hcB⟩, ⟨wB, ?_⟩, ⟨vB, ?_⟩, ?_, ?_⟩
  · intro α
    exact ⟨(wB α).2, by simpa using hwB α α, fun β hβα => by
      simpa [hβα] using hwB α β⟩
  · intro α
    exact ⟨(vB α).2, by simpa using hvB α α, fun β hβα => by
      simpa [hβα] using hvB α β⟩
  · intro α x y hx hy
    have hEq : (⟨x, hx.1⟩ : X) = ⟨y, hy.1⟩ := by
      apply hp.bijective_left.injective
      apply cB.ext
      intro β
      change pair T x (cB β) = pair T y (cB β)
      rw [hcB]
      by_cases hβα : β = α
      · subst β
        exact hx.2.1.trans hy.2.1.symm
      · exact (hx.2.2 β hβα).trans (hy.2.2 β hβα).symm
    exact congrArg Subtype.val hEq
  · intro α v w hv hw
    have hEq : (⟨v, hv.1⟩ : N) = ⟨w, hw.1⟩ := by
      apply hp.bijective_right.injective
      apply b.ext
      intro β
      change pair T (b β) v = pair T (b β) w
      rw [hb β, ← eval_eq_pair]
      by_cases hβα : β = α
      · subst β
        exact hv.2.1.trans hw.2.1.symm
      · exact (hv.2.2 β hβα).trans (hw.2.2 β hβα).symm
    exact congrArg Subtype.val hEq

end Langlands.GroupScheme
