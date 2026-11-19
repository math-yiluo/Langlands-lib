import Langlands.GroupScheme.Lie.OpenTorusLieSlice
import Langlands.GroupScheme.Lie.MaximalTorusLieCentralizer
import Langlands.GroupScheme.Lie.ElementCentralizerTorus
import Langlands.GroupScheme.Lie.InnerAdjoint
import Langlands.GroupScheme.Lie.SmoothFibreRanks
import Langlands.GroupScheme.Cartan.LieInduction
import Langlands.GroupScheme.HomScheme.KernelCorrection

/-! # An open set with prescribed connected Lie centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

private theorem finrank_elementCentralizerLie_le_of_isUnit [LocallyOfFiniteType G.X.hom]
    {r : ℕ} (B : Matrix (Fin d) (Fin r) k) (D : Matrix (Fin r) (Fin d) k)
    (X : lieKernel G k)
    (hu : IsUnit (adjointMatrixAt c k (c.equiv (.of (CommRingCat.of k) k)
      (Additive.ofMul X)) + B * D)) :
    Module.finrank k (elementCentralizerLie G X) ≤ r := by
  let E := elementCentralizerLie G X
  let e := c.equiv (.of (CommRingCat.of k) k)
  let M := adjointMatrixAt c k (e (Additive.ofMul X))
  have hzero (Y : E) : M *ᵥ e Y.val = 0 := by
    calc
      M *ᵥ e Y.val = (adjointRepresentation c).tangentMatrix k Y.val.toMul *ᵥ
          e (Additive.ofMul X) := adjointMatrixAt_mulVec c _ Y.val.toMul
      _ = 0 := (mem_elementCentralizerLie_iff_adjointDifferential c X Y.val.toMul).mp Y.property
  let f := D.mulVecLin ∘ₗ e.toLinearMap ∘ₗ E.subtype
  have hf : Function.Injective f := by
    intro Y Z h
    change D *ᵥ e Y.val = D *ᵥ e Z.val at h
    apply Subtype.ext
    apply e.injective
    apply Matrix.mulVec_injective_iff_isUnit.mpr hu
    change (M + B * D) *ᵥ e Y.val = (M + B * D) *ᵥ e Z.val
    simp only [Matrix.add_mulVec, hzero, zero_add, ← Matrix.mulVec_mulVec, h]
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective hf

variable [CharZero k] {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

private theorem finrank_torusCentralizerCoordinates_eq_dimension
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) [IsAffineHom T.toGrp.X.hom] :
    Module.finrank k (torusCentralizerCoordinates c j) = dimension T.toGrp := by
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let e := c.equiv (.of (CommRingCat.of k) k)
  let f := e.toLinearMap ∘ₗ targetMapLinear j k
  have hf : LinearMap.range f = torusCentralizerCoordinates c j := by
    apply Submodule.ext
    intro v
    rw [mem_maximalTorusCentralizerCoordinates_iff c j hG hj]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.toMul, hx⟩
    · rintro ⟨Y, hY⟩
      exact ⟨Additive.ofMul Y, hY⟩
  have hinj : Function.Injective f := by
    intro x y h
    change e (targetMapLinear j k x) = e (targetMapLinear j k y) at h
    exact targetMapLinear_injective j k (e.injective h)
  rw [← hf, LinearMap.finrank_range_of_inj hinj]
  rfl

section CompleteField

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  {n : ℕ} (cH : FiniteCoordinates H n)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} (s : S.toGrp ⟶ H)

/-- An open set of Lie vectors whose connected centralizers are conjugate to the
chosen maximal torus. The conclusion applies to every affine smooth closed
representative of the centralizer. -/
theorem exists_open_identityComponent_elementCentralizer_conjugate
    (hH : IsConnectedReductive H) (hs : IsMaximalTorus s) :
    ∃ U : Set (Fin n → K), IsOpen U ∧ U.Nonempty ∧ ∀ v ∈ U,
      ∀ (C : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom C.X.hom] [Smooth C.X.hom]
        (i : C ⟶ H), IsClosedSubgroup i →
        (elementCentralizer H ((cH.equiv (.of (CommRingCat.of K) K)).symm v).toMul).IsRepresentedBy i →
        ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
          (a : S.toGrp ≅ identityComponent C),
          a.hom ≫ identityComponentι C ≫ i = s ≫ (H.innerIso g).hom := by
  have : Smooth H.X.hom := hH.smooth
  have : Smooth S.toGrp.X.hom := hs.1.smooth
  have : IsAffineHom S.toGrp.X.hom := hs.2.1.isAffineHom
  have : ConnectedSpace S.toGrp.X.left := hs.1.connectedSpace
  let B := torusCentralizerMatrix cH s
  obtain ⟨D, _, U, hU, hUn, hUv⟩ := exists_open_regularTorusLieSlice cH s hs.1
  refine ⟨U, hU, hUn, fun v hv C _ _ i hi hrep => ?_⟩
  let : CommGroup (lieKernel (identityComponent C) K) :=
    lieKernelCommGroup (identityComponent C)
  let : Module K (Additive (lieKernel (identityComponent C) K)) :=
    lieKernelModule (identityComponent C)
  let : Module.Finite K (Additive (lieKernel (identityComponent C) K)) :=
    finite_lieKernel_of_smooth (identityComponent C)
  obtain ⟨hu, gA, t, hgv⟩ := hUv v hv
  have hBt : B *ᵥ t ∈ torusCentralizerCoordinates cH s := by
    apply (mem_torusCentralizerCoordinates_iff cH s _).2
    intro Y
    rw [adjointDifferentialFamily_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [tangentMatrix_targetMap_mul_eq_zero cH s B
      (fun a Y' => targetMap_mem_elementCentralizerLie_torusCentralizerMatrix cH s Y' a),
      Matrix.zero_mulVec]
  obtain ⟨Y, hY⟩ := (mem_maximalTorusCentralizerCoordinates_iff cH s hH hs _).mp hBt
  let g := HomScheme.basePointOfAffine H gA
  let X := ((cH.equiv (.of (CommRingCat.of K) K)).symm v).toMul
  have hconst : H.constantPoint g ((algSpec (CommRingCat.of K)).obj
      (op (CommAlgCat.of (CommRingCat.of K) K))) = gA := by
    dsimp only [g]
    rw [HomScheme.constantPoint_basePointOfAffine,
      show Algebra.ofId (CommRingCat.of K) K = AlgHom.id _ _ from Subsingleton.elim _ _, affineMap_id]
  have hX : targetMap (s ≫ (H.innerIso g).hom) K Y = X := by
    apply Additive.ofMul.injective
    apply (cH.equiv (.of (CommRingCat.of K) K)).injective
    change cH.equiv (.of (CommRingCat.of K) K)
      (targetMapLinear (s ≫ (H.innerIso g).hom) K (Additive.ofMul Y)) = _
    rw [targetMapLinear_comp, LinearMap.comp_apply, targetMapLinear_innerIso, hconst,
      ← adjointRepresentation_affineAction]
    change (adjointRepresentation cH).affineAction (.of (CommRingCat.of K) K) gA
        (cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul (targetMap s K Y))) =
      cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul X)
    rw [hY, hgv]
    simp only [X, ofMul_toMul, LinearEquiv.apply_symm_apply]
  let z := identityComponentι C ≫ i
  have hz : IsClosedSubgroup z := (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hi
  have : IsClosedImmersion z.hom.hom.left := hz
  have : Mono z.hom.hom := Over.mono_of_mono_left _
  let q := elementCentralizerTorusFactor i hrep (s ≫ (H.innerIso g).hom) ⟨Y, hX⟩
  let q₀ := IdentityComponent.factor C q
  have hq₀ : q₀ ≫ z = s ≫ (H.innerIso g).hom := by
    dsimp only [q₀, z, q]
    rw [IdentityComponent.factor_identityComponentι_assoc, elementCentralizerTorusFactor_comp]
  have hclosed : IsClosedSubgroup q₀ := by
    apply IsClosedSubgroup.of_comp hz
    rw [hq₀]
    exact hs.2.1.comp_iso (H.innerIso g)
  have : IsClosedImmersion q₀.hom.hom.left := hclosed
  have : Mono q₀.hom.hom := Over.mono_of_mono_left _
  have hdimEq : Module.finrank K (elementCentralizerLie H X) = dimension (identityComponent C) := by
    change Module.finrank K ((elementCentralizer H X).lie K) = _
    rw [hrep.lie_eq_range_identityComponent K]
    exact LinearMap.finrank_range_of_inj (targetMapLinear_injective z K)
  have hunit : IsUnit (adjointMatrixAt cH K
      (cH.equiv (.of (CommRingCat.of K) K) (Additive.ofMul X)) + B * D) := by
    simpa only [X, ofMul_toMul, LinearEquiv.apply_symm_apply] using hu
  have hdimLe := finrank_elementCentralizerLie_le_of_isUnit cH B D X hunit
  rw [hdimEq, finrank_torusCentralizerCoordinates_eq_dimension cH s hH hs] at hdimLe
  have hdimGe : dimension S.toGrp ≤ dimension (identityComponent C) :=
    (targetMapLinear q₀ K).finrank_le_finrank_of_injective (targetMapLinear_injective q₀ K)
  have : IsIso q₀ := isIso_of_mono_of_dimension_eq q₀ (le_antisymm hdimGe hdimLe)
  exact ⟨g, asIso q₀, hq₀⟩

/-- A prescribed maximal torus is conjugate to the connected centralizer of each
vector in a nonempty open set of finite Lie coordinates. -/
def OpenMaximalTorusLieCentralizerStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
    (n : ℕ) (cH : FiniteCoordinates H n)
    (S : CommGroupScheme (Spec (CommRingCat.of K))) (s : S.toGrp ⟶ H),
    IsConnectedReductive H → IsMaximalTorus s →
      ∃ U : Set (Fin n → K), IsOpen U ∧ U.Nonempty ∧ ∀ v ∈ U,
        ∀ (C : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom C.X.hom] [Smooth C.X.hom]
          (i : C ⟶ H), IsClosedSubgroup i →
          (elementCentralizer H ((cH.equiv (.of (CommRingCat.of K) K)).symm v).toMul).IsRepresentedBy i →
          ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
            (a : S.toGrp ≅ identityComponent C),
            a.hom ≫ identityComponentι C ≫ i = s ≫ (H.innerIso g).hom

theorem openMaximalTorusLieCentralizer : OpenMaximalTorusLieCentralizerStatement.{u} :=
  fun _ _ _ _ _ _ _ c _ s hH hs => exists_open_identityComponent_elementCentralizer_conjugate c s hH hs

end CompleteField

end Langlands.GroupScheme.Lie
