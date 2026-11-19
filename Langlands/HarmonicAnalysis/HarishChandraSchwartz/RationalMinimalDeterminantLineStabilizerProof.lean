import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalDeterminantLineStabilizerStatement
import Langlands.GroupScheme.Lie.InnerAdjoint
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.PositiveRootStabilizerReduction
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.Dynamic.NestedDecomposition
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Trivial stabilizer of the minimal determinant vector in the opposite radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix Module
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.HarishChandraSchwartz

private theorem mem_span_iff_ι_mul_eq_zero
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {d : ℕ}
    {w : Fin d → V} (hw : LinearIndependent k w) (x : V) :
    x ∈ Submodule.span k (Set.range w) ↔
      ExteriorAlgebra.ι k x * (exteriorPower.ιMulti k d w : ExteriorAlgebra k V) = 0 := by
  constructor
  · intro hx
    have hle : Submodule.span k (Set.range w) ≤ LinearMap.ker
        ((LinearMap.mulRight k (exteriorPower.ιMulti k d w : ExteriorAlgebra k V)) ∘ₗ
          ExteriorAlgebra.ι k) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ExteriorAlgebra.ι_mul_prod_list w i
    exact hle hx
  · intro hx
    by_contra hspan
    have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := d + 1) (hw.finCons hspan)
    have hne := hli.ne_zero
      (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin (d + 1))).toOrderEmbedding)
    apply hne
    simp only [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
    apply Subtype.ext
    change ExteriorAlgebra.ιMulti k (d + 1) (Fin.cons x w) = 0
    rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.prod_cons, Fin.cons_zero]
    simpa only [Fin.cons_succ, ← ExteriorAlgebra.ιMulti_apply, exteriorPower.ιMulti_apply_coe]
      using hx

private theorem mapsTo_span_of_exteriorMap_eq_smul
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {d : ℕ}
    {w : Fin d → V} (hw : LinearIndependent k w) (f : V →ₗ[k] V) {a : k} (ha : a ≠ 0)
    (hf : exteriorPower.map d f (exteriorPower.ιMulti k d w) = a • exteriorPower.ιMulti k d w) :
    Set.MapsTo f (Submodule.span k (Set.range w)) (Submodule.span k (Set.range w)) := by
  intro x hx
  apply (mem_span_iff_ι_mul_eq_zero hw (f x)).mpr
  have hline := congrArg (fun y : ⋀[k]^d V => (y : ExteriorAlgebra k V)) hf
  simp only [exteriorPower.coe_map, Submodule.coe_smul] at hline
  have h := congrArg (ExteriorAlgebra.map f) ((mem_span_iff_ι_mul_eq_zero hw x).mp hx)
  rw [map_mul, map_zero, ExteriorAlgebra.map_apply_ι, hline, mul_smul_comm] at h
  exact (smul_eq_zero.mp h).resolve_left ha

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

omit [IsAffineHom G.X.hom] in
private theorem rationalPointEquiv_eq_constantPoint (g : rationalPoints G) :
    rationalPointEquiv k G.X g = G.constantPoint g
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of _ k))) := by
  change rationalPointEquiv k G.X g = G.constantPoint g (ringTest k k)
  rw [← G.constantPoint_naturality g (ringTestSelfIso k).hom, constantPoint_self]
  change (ringTestSelfIso k).hom ≫ g ≫ 𝟙 _ = (ringTestSelfIso k).hom ≫ g
  rw [Category.comp_id]

private theorem basePointAdjoint_mem_tangent_of_exterior_eq_smul
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom] {iU : U ⟶ G}
    (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
    {N d : ℕ} (cG : Lie.FiniteCoordinates G N) (cU : Lie.FiniteCoordinates U d)
    (g : rationalPoints G) {a : k} (ha : a ≠ 0)
    (hg : ((Dynamic.adjointExteriorRepresentation cG (d := d)).rationalMatrix g : Matrix _ _ k) *ᵥ
        Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k) =
        a • Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k)) :
    ∀ {X : Additive (lieKernel G k)}, X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent χ) →
      basePointAdjoint g X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent χ) := by
  let A := CommAlgCat.of (CommRingCat.of k) k
  have : Mono iU.hom.hom := hU.1
  let j := Dynamic.lieInclusionCoordinates cG cU iU A
  let b := Pi.basisFun A (Fin d)
  let w : Fin d → (Fin N → A) := fun i => j (b i)
  have hj : Function.Injective j := Dynamic.lieInclusionCoordinates_injective cG cU A
  have hw : LinearIndependent A w := b.linearIndependent.map' j (LinearMap.ker_eq_bot.mpr hj)
  have hspan : Submodule.span A (Set.range w) = LinearMap.range j := by
    change Submodule.span A (Set.range (j ∘ b)) = _
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, ← LinearMap.range_eq_map]
  have hmem (X : Additive (lieKernel G k)) :
      cG.equiv A X ∈ Submodule.span A (Set.range w) ↔
        X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent χ) := by
    rw [hspan, ← hU.2, RelativeRoot.tangentSubmodule_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(cU.equiv A).symm y, (cG.equiv A).injective hy⟩
    · rintro ⟨Y, rfl⟩
      refine ⟨cU.equiv A Y, ?_⟩
      simp only [j, Dynamic.lieInclusionCoordinates, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
  let gA : G.affinePoints A := G.constantPoint g _
  let act := (Lie.adjointRepresentation cG).affineAction A gA
  have hact : exteriorPower.map d act.toLinearMap (exteriorPower.ιMulti A d w) =
      a • exteriorPower.ιMulti A d w := by
    have h := hg
    rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix, rationalPointEquiv_eq_constantPoint] at h
    change ((Chevalley.exteriorRepresentation N d (CommRingCat.of k) (Lie.adjointRepresentation cG)).affineMatrix
        A gA : Matrix _ _ A) *ᵥ
        ((Chevalley.matrixExteriorBasis N d A).equivFun (exteriorPower.ιMulti A d w)) =
      a • (Chevalley.matrixExteriorBasis N d A).equivFun (exteriorPower.ιMulti A d w) at h
    rw [← affineAction_apply, Chevalley.exteriorRepresentation_affineAction, ← map_smul] at h
    exact (Chevalley.matrixExteriorBasis N d A).equivFun.injective h
  intro X hX
  have h := mapsTo_span_of_exteriorMap_eq_smul hw act.toLinearMap ha hact ((hmem X).mpr hX)
  apply (hmem _).mp
  change (Lie.adjointRepresentation cG).affineAction A gA (cG.equiv A X) ∈ _ at h
  rw [Lie.adjointRepresentation_affineAction] at h
  exact h

private theorem mem_parabolic_of_preserves_tangent
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] (ν : cocharacterLattice S) (hG : IsConnectedReductive G)
    (n : normalizerPoints i)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (hforward : ∀ {X : Additive (lieKernel G k)},
      X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) →
      basePointAdjoint n.val X ∈
        RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)))
    (hbackward : ∀ {X : Additive (lieKernel G k)},
      X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) →
      basePointAdjoint n.val⁻¹ X ∈
        RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) :
    n.val ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).rationalPoints := by
  have : Smooth G.X.hom := hG.smooth
  let χ := CommGroupScheme.groupHom ν ≫ i
  let ψ := χ ≫ (G.innerIso n.val).hom
  let ξ := cocharacterAut (normalizingAut i n) ν
  have hξ : CommGroupScheme.groupHom ξ ≫ i = ψ := groupHom_cocharacterAut_comp i n ν
  have hrotate (X : Additive (lieKernel G k)) :
      X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent χ) ↔
        basePointAdjoint n.val X ∈ RelativeRoot.tangentSubmodule (Dynamic.unipotent ψ) := by
    have hval : (basePointAdjoint n.val X).toMul.val =
        G.constantPoint n.val _ * X.toMul.val * (G.constantPoint n.val _)⁻¹ := by
      rw [basePointAdjoint, ← Lie.targetMapLinear_innerIso, lieKernelTargetLinear_val,
        comp_innerIso_hom]
    rw [RelativeRoot.mem_tangentSubmodule, RelativeRoot.mem_tangentSubmodule, hval]
    exact Dynamic.mem_unipotent_conj χ n.val
  have hinv (X : Additive (lieKernel G k)) :
      basePointAdjoint n.val (basePointAdjoint n.val⁻¹ X) = X := by
    rw [← Module.End.mul_apply, basePointAdjoint_mul_inv, Module.End.one_apply]
  have hab : Dynamic.unipotent χ ≤ Dynamic.unipotent ψ := by
    rw [← hξ]
    apply Dynamic.unipotent_le_of_lieKernel_of_smooth i ν ξ
    intro X hX
    have h := (hrotate (basePointAdjoint n.val⁻¹ (Additive.ofMul X))).mp (hbackward hX)
    rw [hinv, ← hξ] at h
    exact h
  have hba : Dynamic.unipotent ψ ≤ Dynamic.unipotent χ := by
    rw [← hξ]
    apply Dynamic.unipotent_le_of_lieKernel_of_smooth i ξ ν
    intro X hX
    have hy : basePointAdjoint n.val⁻¹ (Additive.ofMul X) ∈
        RelativeRoot.tangentSubmodule (Dynamic.unipotent χ) := by
      apply (hrotate _).mpr
      rw [hinv, ← hξ]
      exact hX
    have h := hforward hy
    rw [hinv] at h
    exact h
  have hZeq : Dynamic.centralizer ψ = Dynamic.centralizer χ :=
    (centralizer_conjugate_eq_torusCentralizer i χ hZ n).trans hZ.symm
  have hP_le {α β : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
      (hZ : Dynamic.centralizer α ≤ Dynamic.centralizer β)
      (hU : Dynamic.unipotent α ≤ Dynamic.unipotent β) :
      Dynamic.parabolic α ≤ Dynamic.parabolic β := by
    intro T g hg
    obtain ⟨m, hm, u, hu, rfl⟩ := Dynamic.exists_centralizer_mul_unipotent α hg
    exact ((Dynamic.parabolic β).carrier T).mul_mem
      (Dynamic.centralizer_le_parabolic β T (hZ T hm))
      (Dynamic.unipotent_le_parabolic β T (hU T hu))
  have hP : Dynamic.parabolic ψ = Dynamic.parabolic χ :=
    le_antisymm (hP_le hZeq.le hba) (hP_le hZeq.ge hab)
  have hn := Dynamic.mem_normalizer_parabolic_of_conjugate_eq χ n.val hP
  rw [dynamicParabolic_normalizer_eq_of_structural_statements
    parabolicDynamic parabolicSelfNormalizer hG χ] at hn
  exact hn

/-- The exterior determinant vector of the actual minimal radical has trivial stabilizer
in the opposite radical on rational points. -/
theorem rationalMinimalDeterminantLineStabilizer : RationalMinimalDeterminantLineStabilizerStatement.{u} := by
  intro k _ G _ hG S i hi ν hν U _ iU hU N d cG cU x hx hxv
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let ρ := Dynamic.adjointExteriorRepresentation cG (d := d)
  let v := Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k)
  have hZ := genericCentralizer k G hG S i hi ν hν
  obtain ⟨n₀, hn₀, p, hp, q, hq, hxEq⟩ := exists_bruhat_factorization hG hi ν hZ x
  let n : normalizerPoints i := ⟨n₀, hn₀⟩
  let iP := Dynamic.Affine.parabolicHom χ
  have hP : (Dynamic.parabolic χ).IsRepresentedBy iP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  have : IsAffine (Dynamic.Affine.parabolicScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom
  have hev (g : rationalPoints G) (hg : g ∈ (Dynamic.parabolic χ).rationalPoints) :
      ∃ a : kˣ, (ρ.rationalMatrix g : Matrix _ _ k) *ᵥ v = (a : k) • v := by
    rw [SubgroupFunctor.rationalPoints_eq_range hP] at hg
    obtain ⟨y, rfl⟩ := hg
    exact ⟨_, Dynamic.adjointExteriorCoordinates_rational_action hP hU cG cU y⟩
  obtain ⟨ap, hap⟩ := hev p⁻¹ ((Dynamic.parabolic χ).rationalPoints.inv_mem hp)
  obtain ⟨aq, haq⟩ := hev q⁻¹ ((Dynamic.parabolic χ).rationalPoints.inv_mem hq)
  let a := aq * ap
  have hnv : (ρ.rationalMatrix n.val : Matrix _ _ k) *ᵥ v = (a : k) • v := by
    have hnEq : n.val = p⁻¹ * x * q⁻¹ := by
      rw [hxEq]
      change n₀ = p⁻¹ * (p * n₀ * q) * q⁻¹
      group
    change (ρ.rationalMatrix x : Matrix _ _ k) *ᵥ v = v at hxv
    rw [hnEq, map_mul, map_mul, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, haq, Matrix.mulVec_smul,
      hxv, Matrix.mulVec_smul, hap, smul_smul]
    rfl
  have hniv : (ρ.rationalMatrix n.val⁻¹ : Matrix _ _ k) *ᵥ v = (a : k)⁻¹ • v := by
    apply Matrix.mulVec_injective_of_isUnit (Units.isUnit (ρ.rationalMatrix n.val))
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, Matrix.one_mulVec, Matrix.mulVec_smul, hnv, smul_smul,
      inv_mul_cancel₀ a.ne_zero, one_smul]
  have hnP := mem_parabolic_of_preserves_tangent ν hG n hZ
    (basePointAdjoint_mem_tangent_of_exterior_eq_smul hU cG cU n.val a.ne_zero hnv)
    (basePointAdjoint_mem_tangent_of_exterior_eq_smul hU cG cU n.val⁻¹
      (inv_ne_zero a.ne_zero) hniv)
  apply Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx
  rw [hxEq]
  exact (Dynamic.parabolic χ).rationalPoints.mul_mem
    ((Dynamic.parabolic χ).rationalPoints.mul_mem hp hnP) hq

end Langlands.HarishChandraSchwartz
