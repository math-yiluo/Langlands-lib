import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition
import Langlands.GroupScheme.Lie.SubgroupLieBaseChange
import Langlands.GroupScheme.Lie.AdjointTangentBracket
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveProof
import Langlands.Algebra.DualNumberDeterminant

/-! # The trace of `ad` on the Lie algebra of a parabolic, split along its Levi decomposition

For a normal subgroup `V` of `Q`, the adjoint action of `Lie Q` preserves `Lie V`; transported
to `Lie V` it is `normalAdjoint`. For a parabolic `Q = M' ⋉ V` of a connected reductive group
with rational Levi subgroup `M'` and unipotent radical `V`, and `y` in the Lie algebra of `M'`
over a `k`-algebra `A`, the trace of `ad y` on `Lie Q` is the trace on `Lie V` plus the trace on
`Lie M'`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]

attribute [local instance] kernelLieRingOfField kernelLieAlgebraOfField

section Normal

variable {Q V : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom]
  (iV : V ⟶ Q) (hV : (SubgroupFunctor.range iV).IsNormal) [Mono iV.hom.hom]
  (A : Type u) [CommRing A] [Algebra k A]

set_option maxRecDepth 8192 in
include hV in
/-- The bracket of a Lie vector of `Q` with one of a normal subgroup `V` lies in `Lie V`. -/
theorem lie_targetMapLinear_mem_range (x : Additive (lieKernel Q A))
    (w : Additive (lieKernel V A)) :
    ⁅x, targetMapLinear iV A w⁆ ∈ LinearMap.range (targetMapLinear iV A) := by
  have hrep : (SubgroupFunctor.range iV).IsRepresentedBy iV := ⟨inferInstance, rfl⟩
  rw [← SubgroupFunctor.lie_eq_range _ A iV hrep] at ⊢
  refine SubgroupFunctor.lie_lie_mem_of_isNormal_coefficients _ A hV iV hrep x ?_
  rw [SubgroupFunctor.lie_eq_range _ A iV hrep]
  exact LinearMap.mem_range_self _ w

/-- The adjoint action of a Lie vector `x` of `Q` on the Lie algebra of a normal subgroup `V`. -/
def normalAdjoint (x : Additive (lieKernel Q A)) :
    Additive (lieKernel V A) →ₗ[A] Additive (lieKernel V A) :=
  (LinearEquiv.ofInjective (targetMapLinear iV A) (targetMapLinear_injective iV A)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (targetMapLinear iV A))
      ((LieModule.toEnd A (Additive (lieKernel Q A)) (Additive (lieKernel Q A)) x) ∘ₗ
        targetMapLinear iV A)
      (fun w => by
        rw [LinearMap.comp_apply, LieModule.toEnd_apply_apply]
        exact lie_targetMapLinear_mem_range iV hV A x w)

/-- `normalAdjoint x` is `ad x` on `Lie V`. -/
theorem targetMapLinear_normalAdjoint (x : Additive (lieKernel Q A))
    (w : Additive (lieKernel V A)) :
    targetMapLinear iV A (normalAdjoint iV hV A x w) = ⁅x, targetMapLinear iV A w⁆ := by
  have h := LinearEquiv.ofInjective_apply (targetMapLinear iV A)
    (h := targetMapLinear_injective iV A)
    ((LinearEquiv.ofInjective (targetMapLinear iV A) (targetMapLinear_injective iV A)).symm
      ⟨⁅x, targetMapLinear iV A w⁆, lie_targetMapLinear_mem_range iV hV A x w⟩)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Normal

section Reductive

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] (A : Type u) [CommRing A] [Algebra k A]

set_option maxRecDepth 8192 in
/-- On the Lie algebra over `A` of a connected reductive group, `ad y` has trace zero: the
adjoint determinant character is trivial, and its value at the dual-number point of `y` is
`1 + ε tr (ad y)`. -/
theorem trace_toEnd_eq_zero_of_isConnectedReductive (hH : IsConnectedReductive H)
    (y : Additive (lieKernel H A)) :
    LinearMap.trace A (Additive (lieKernel H A))
      (LieModule.toEnd A (Additive (lieKernel H A)) (Additive (lieKernel H A)) y) = 0 := by
  let c := finiteCoordinates H
  let A' := CommAlgCat.of (CommRingCat.of k) (DualNumber A)
  let a := AutomorphicAction.conjugation (𝟙 H)
  let g : H.affinePoints A' := y.toMul.val
  have hval := adjointDeterminantCharacter_affinePoints H A' g
  rw [connectedReductiveAdjointDeterminant k H hH, rationalCharacters.comp_zero, map_one] at hval
  have hred : H.affinePointMap
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) A A)) g = 1 :=
    y.toMul.property
  have hfst : ((a.coordinateMatrix c A' g).val).map
      (TrivSqZeroExt.fst : DualNumber A → A) = 1 := by
    have hnat := a.coordinateMatrix_naturality c
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) A A)) g
    rw [hred, map_one] at hnat
    ext i j
    have h := congrArg (fun M : GL (Fin (Module.finrank k (Additive (lieKernel H k)))) A =>
      M.val i j) hnat
    simp only [Matrix.GeneralLinearGroup.map_apply] at h
    rw [Matrix.map_apply]
    exact h.symm.trans (by simp)
  have hdet := Langlands.Algebra.DualNumberDeterminant.det_eq_of_map_fst_eq_one _ hfst
  have hd := a.coordinateMatrix_det c A' g
  have key : ((a.coordinateMatrix c A' g).val).det = 1 := by
    have h1 : ((LinearEquiv.det (a.differential g)).val : DualNumber A) =
        ((a.coordinateMatrix c A' g).val).det := by
      rw [← hd, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h1, ← hval]
    rfl
  have hsnd := congrArg TrivSqZeroExt.snd (hdet.symm.trans key)
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
    TrivSqZeroExt.snd_one] at hsnd
  rw [trace_toEnd_eq_trace_kernelDifferential c A y]
  exact (congrArg Matrix.trace (coordinateMatrix_conjugation_snd c A y.toMul)).symm.trans hsnd

end Reductive

section Levi

variable {G Q M' V : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom]
  {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q}
  (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
  (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl : IsRationalLeviSubgroup l')
  (A : Type u) [CommRing A] [Algebra k A]

omit [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine M'.X.left]
  [LocallyOfFiniteType M'.X.hom] [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom] in
/-- The Lie algebra over `A` of an affine group of locally finite type over `k` is finite free. -/
theorem free_finite_lieKernel (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] :
    Module.Free A (Additive (lieKernel H A)) ∧ Module.Finite A (Additive (lieKernel H A)) := by
  let e := coordinateEquiv (finiteCoordinates H) A
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

include hG hq hl in
/-- For `y` in the Lie algebra of the rational Levi subgroup `M'` of the parabolic `Q`, the trace
of `ad y` on `Lie Q` is the trace of `ad y` on the Lie algebra of the unipotent radical `V` plus
the trace of `ad y` on `Lie M'`. -/
theorem trace_toEnd_levi [Mono iV.hom.hom] (y : Additive (lieKernel M' A)) :
    LinearMap.trace A (Additive (lieKernel Q A))
        (LieModule.toEnd A (Additive (lieKernel Q A)) (Additive (lieKernel Q A))
          (targetMapLinear l' A y)) =
      LinearMap.trace A (Additive (lieKernel V A))
          (normalAdjoint iV hV.1.isNormal A (targetMapLinear l' A y)) +
        LinearMap.trace A (Additive (lieKernel M' A))
          (LieModule.toEnd A (Additive (lieKernel M' A)) (Additive (lieKernel M' A)) y) := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := hG.isSeparated
  have : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q q hq.isClosedSubgroup).mp hq
  obtain ⟨ψ, -, hP⟩ := hl.exists_centralCocharacter_of_dynamicParabolic hG χ ⟨inferInstance, hχ⟩
  have hZ := hl.centralizer_eq_of_dynamicParabolic hG ψ hP
  have hU := Dynamic.range_comp_radical_eq_unipotent_of_reductive hG (ψ ≫ l' ≫ q) q hP iV hV.1
  have hM'mono : Mono (l' ≫ q).hom.hom := by
    have : IsClosedImmersion l'.hom.hom.left := hl.isClosedSubgroup
    have : Mono l'.hom.hom := Over.mono_of_mono_left _
    rw [Grp.comp_hom_hom]
    infer_instance
  have hVmono : Mono (iV ≫ q).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hZrep : (Dynamic.centralizer (ψ ≫ l' ≫ q)).IsRepresentedBy (l' ≫ q) := ⟨hM'mono, hZ.symm⟩
  have hUrep : (Dynamic.unipotent (ψ ≫ l' ≫ q)).IsRepresentedBy (iV ≫ q) := ⟨hVmono, hU⟩
  have hl' : Dynamic.centralizerToParabolic hP hZrep = l' :=
    hP.hom_ext (Dynamic.centralizerToParabolic_comp hP hZrep)
  have hu' : Dynamic.unipotentToParabolic hP hUrep = iV :=
    hP.hom_ext (Dynamic.unipotentToParabolic_comp hP hUrep)
  obtain ⟨_, _⟩ := free_finite_lieKernel A V
  obtain ⟨_, _⟩ := free_finite_lieKernel A M'
  let E := Dynamic.lieProductEquiv hP hZrep hUrep A
  have hE (a : Additive (lieKernel V A)) (b : Additive (lieKernel M' A)) :
      E (a, b) = targetMapLinear iV A a + targetMapLinear l' A b := by
    change Dynamic.lieProductMap hP hZrep hUrep A (a, b) = _
    rw [Dynamic.lieProductMap, LinearMap.coprod_apply, hl', hu']
  have hconj : E.symm.conj (LieModule.toEnd A (Additive (lieKernel Q A))
      (Additive (lieKernel Q A)) (targetMapLinear l' A y)) =
      LinearMap.prodMap (normalAdjoint iV hV.1.isNormal A (targetMapLinear l' A y))
        (LieModule.toEnd A (Additive (lieKernel M' A)) (Additive (lieKernel M' A)) y) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.prodMap_apply, hE, hE,
      LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply, lie_add,
      targetMapLinear_normalAdjoint, targetMapLinear_lie]
  rw [← LinearMap.trace_conj' _ E.symm, hconj, LinearMap.trace_prodMap']

end Levi

end Langlands.GroupScheme.Lie
