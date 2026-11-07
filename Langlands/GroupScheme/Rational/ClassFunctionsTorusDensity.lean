import Langlands.GroupScheme.Torus.SplitCharacterPoint
import Langlands.AlgebraicGeometry.TangentSmoothness
import Langlands.GroupScheme.Lie.PointTangent
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.DominantPullbackProof
import Langlands.GroupScheme.Rational.PointedTensorWeights
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Absolute.BorelFieldExtensionMaximality
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Dense conjugates of a split maximal torus and class functions vanishing on it -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.TangentSmoothness

namespace Langlands.GroupScheme.TorusConjugation

section Conjugation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- The conjugation morphism `G × T → G`, `(g, t) ↦ g j(t) g⁻¹`. -/
def conjugation : G.X ⊗ T.toGrp.X ⟶ G.X :=
  fst G.X T.toGrp.X * (snd G.X T.toGrp.X ≫ j.hom.hom) * (fst G.X T.toGrp.X)⁻¹

theorem comp_conjugation {Z : Over (Spec (CommRingCat.of k))} (x : Z ⟶ G.X ⊗ T.toGrp.X) :
    x ≫ conjugation j =
      (x ≫ fst G.X T.toGrp.X) * ((x ≫ snd G.X T.toGrp.X) ≫ j.hom.hom) *
        (x ≫ fst G.X T.toGrp.X)⁻¹ := by
  simp only [conjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]

theorem lift_conjugation {Z : Over (Spec (CommRingCat.of k))} (g : Z ⟶ G.X)
    (t : Z ⟶ T.toGrp.X) : lift g t ≫ conjugation j = g * (t ≫ j.hom.hom) * g⁻¹ := by
  rw [comp_conjugation, lift_fst, lift_snd]

end Conjugation

section Points

variable {k : Type u} [Field k]

variable (k) in
/-- The rational test object `Spec k` written as an affine test. -/
abbrev baseTest : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))

variable (k) in
/-- The dual-number test object `Spec k[ε]`. -/
abbrev dualTest : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))

theorem baseTest_hom : (baseTest k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [algSpec_obj_hom]
  exact (congrArg Spec.map CommRingCat.ofHom_id).trans (Spec.map_id _)

/-- The rational point of a group scheme attached to an affine `k`-point. -/
def basePoint {H : GroupScheme (Spec (CommRingCat.of k))} (t : Lie.AffinePoints H k) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
  (Over.homMk (𝟙 _) (by rw [Category.id_comp, baseTest_hom]; rfl) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ baseTest k) ≫ t

theorem constantPoint_basePoint {H : GroupScheme (Spec (CommRingCat.of k))}
    (t : Lie.AffinePoints H k) : H.constantPoint (basePoint t) (baseTest k) = t := by
  unfold constantPoint basePoint
  rw [← Category.assoc]
  convert Category.id_comp t
  exact Over.OverMorphism.ext (by simp; rfl)

/-- The augmentation `Spec k → Spec k[ε]` as a morphism of test objects. -/
def augmentation : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ dualTest k :=
  Over.homMk (dualNumberAugmentation k) dualNumberAugmentation_comp_dualNumberProjection

theorem augmentation_comp_constantPoint (H : GroupScheme (Spec (CommRingCat.of k)))
    (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    augmentation ≫ H.constantPoint m (dualTest k) = m := by
  rw [constantPoint_naturality, constantPoint_self]

theorem constantPoint_comp_hom {H H' : GroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ H')
    (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (U : Over (Spec (CommRingCat.of k))) :
    H.constantPoint m U ≫ f.hom.hom = H'.constantPoint (m ≫ f.hom.hom) U :=
  Category.assoc _ _ _

theorem constant_constantPoint (H : GroupScheme (Spec (CommRingCat.of k)))
    (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    Lie.constant H (H.constantPoint m (baseTest k)) = H.constantPoint m (dualTest k) := by
  rw [Lie.constant, Lie.affineMap_apply, constantPoint_naturality]

variable (H : GroupScheme (Spec (CommRingCat.of k)))

theorem augmentation_comp_lieKernel (X : lieKernel H k) : augmentation ≫ X.val = 1 :=
  Over.OverMorphism.ext (Lie.kernelTangentEquiv H X).property.2

theorem exists_lieKernel_of_augmentation {P : Lie.AffinePoints H (DualNumber k)}
    (h : augmentation ≫ P = 1) : ∃ X : lieKernel H k, X.val = P :=
  ⟨(Lie.kernelTangentEquiv H).symm ⟨P.left, Over.w P, congrArg CommaMorphism.left h⟩,
    Over.OverMorphism.ext rfl⟩

theorem lieKernelMapLinear_ofId_self [IsAffineHom H.X.hom] (X : Additive (lieKernel H k)) :
    lieKernelMapLinear H (Algebra.ofId (CommRingCat.of k) (CommRingCat.of k)) X = X := by
  apply Additive.toMul.injective
  rw [lieKernelMapLinear_toMul]
  have h : Algebra.ofId (CommRingCat.of k) (CommRingCat.of k) =
      AlgHom.id (CommRingCat.of k) (CommRingCat.of k) := by
    ext
  rw [h, lieKernelMap_id]

end Points

section Tangent

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.toGrp.X.hom] (j : T.toGrp ⟶ G)

omit [IsAffineHom T.toGrp.X.hom] in
/-- An eigenvector with eigenvalue `c ≠ 0, 1` of `A` lies in the range of `B - 1` when
`B * A = 1`. -/
theorem mem_range_sub_id_of_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A B : Module.End K V} (hBA : B * A = 1) {c : K} (hc : c ≠ 1) (hc0 : c ≠ 0) {X : V}
    (hX : A X = c • X) : X ∈ LinearMap.range (B - LinearMap.id) := by
  have hB : B X = c⁻¹ • X := by
    have h1 : B (A X) = X := by rw [← Module.End.mul_apply, hBA, Module.End.one_apply]
    rw [hX, map_smul] at h1
    calc B X = c⁻¹ • c • B X := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • X := by rw [h1]
  have hne : c⁻¹ - 1 ≠ 0 := sub_ne_zero.2 fun h => hc (inv_eq_one.1 h)
  refine ⟨(c⁻¹ - 1)⁻¹ • X, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_smul, hB, smul_smul, ← sub_smul,
    ← mul_sub_one, inv_mul_cancel₀ hne, one_smul]

omit [IsAffineHom T.toGrp.X.hom] in
/-- **Linear algebra at a regular point.** If `τ₀` has character value different from `1`
at every root, then every Lie vector `Z` is `Ad(n⁻¹) ξ - ξ + W` with `W` of weight zero,
where `n = j(τ₀)`. -/
theorem exists_adjoint_sub_add [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)
    (τ₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X)
    (hreg : ∀ χ ∈ roots j,
      Lie.characterValue χ (GroupScheme.constantPoint T.toGrp τ₀ (baseTest k)) ≠ 1)
    (Z : Additive (lieKernel G k)) :
    ∃ ξ W, W ∈ weightSpace j 0 ∧
      Z = basePointAdjoint (τ₀ ≫ j.hom.hom)⁻¹ ξ - ξ + W := by
  classical
  have htop : LinearMap.range (basePointAdjoint (τ₀ ≫ j.hom.hom)⁻¹ - LinearMap.id) ⊔
      weightSpace j 0 = ⊤ := by
    rw [eq_top_iff, ← (isInternal_weightSpace_of_isSplitTorus k G T hT j).submodule_iSup_eq_top]
    refine iSup_le fun χ => ?_
    by_cases hχ : χ = 0
    · subst hχ
      exact le_sup_right
    by_cases hbot : weightSpace j χ = ⊥
    · rw [hbot]
      exact bot_le
    intro X hX
    apply Submodule.mem_sup_left
    have hc : (Lie.characterValue χ (GroupScheme.constantPoint T.toGrp τ₀ (baseTest k)) : k) ≠
        1 := fun h => hreg χ ⟨hχ, hbot⟩ (Units.ext h)
    have hAd : basePointAdjoint (τ₀ ≫ j.hom.hom) X =
        (Lie.characterValue χ (GroupScheme.constantPoint T.toGrp τ₀ (baseTest k)) : k) • X := by
      have h := hX (CommRingCat.of k) (GroupScheme.constantPoint T.toGrp τ₀ (baseTest k))
      rw [lieKernelMapLinear_ofId_self, constantPoint_comp_hom] at h
      exact h
    exact mem_range_sub_id_of_eigen (basePointAdjoint_inv_mul _) hc (Units.ne_zero _) hAd
  have hZ : Z ∈ LinearMap.range (basePointAdjoint (τ₀ ≫ j.hom.hom)⁻¹ - LinearMap.id) ⊔
      weightSpace j 0 := htop ▸ Submodule.mem_top
  obtain ⟨_, ⟨ξ, rfl⟩, W, hW, hsum⟩ := Submodule.mem_sup.1 hZ
  exact ⟨ξ, W, hW, hsum.symm⟩

/-- **Tangent surjectivity of conjugation.** At the rational point `(1, τ₀)` of `G × T`, the
conjugation map is surjective on rational tangent vectors, provided `T` is its own centralizer
and every Lie vector decomposes as in `exists_adjoint_sub_add`. -/
theorem isTangentSurjectiveAt_conjugation
    (hmax : torusCentralizer j = SubgroupFunctor.range j)
    (τ₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X)
    (hsplit : ∀ Z : Additive (lieKernel G k), ∃ ξ W, W ∈ weightSpace j 0 ∧
      Z = basePointAdjoint (τ₀ ≫ j.hom.hom)⁻¹ ξ - ξ + W) :
    IsTangentSurjectiveAt (G.X ⊗ T.toGrp.X).hom G.X.hom (conjugation j).left
      (lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) τ₀).left := by
  rintro t ⟨ht₁, ht₂⟩
  let tt : Lie.AffinePoints G (DualNumber k) := Over.homMk t ht₁
  set n := τ₀ ≫ j.hom.hom with hn
  set C := G.constantPoint n (dualTest k) with hC
  have hat : augmentation ≫ tt = n := by
    have h : augmentation ≫ tt = lift 1 τ₀ ≫ conjugation j := Over.OverMorphism.ext ht₂
    rw [h, lift_conjugation, one_mul, inv_one, mul_one]
  obtain ⟨Z, hZ⟩ := exists_lieKernel_of_augmentation G (P := C⁻¹ * tt) (by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hC, augmentation_comp_constantPoint, hat,
      inv_mul_cancel])
  obtain ⟨ξ, W, hW, hZW⟩ := hsplit (Additive.ofMul Z)
  have hWc := (Lie.mem_torusCentralizer_iff_mem_weightSpace_zero j W.toMul).2 hW
  rw [hmax] at hWc
  obtain ⟨σ₀, hσ₀⟩ := SubgroupFunctor.mem_range.1 hWc
  set σ₁ := (GroupScheme.constantPoint T.toGrp (augmentation ≫ σ₀) (dualTest k))⁻¹ * σ₀ with hσ₁def
  have hσ₁ : σ₁ ≫ j.hom.hom = W.toMul.val := by
    rw [hσ₁def, MonObj.mul_comp, GrpObj.inv_comp, constantPoint_comp_hom, Category.assoc, hσ₀,
      augmentation_comp_lieKernel, constantPoint_one, inv_one, one_mul]
  have haσ₁ : augmentation ≫ σ₁ = 1 := by
    rw [hσ₁def, MonObj.comp_mul, GrpObj.comp_inv, augmentation_comp_constantPoint,
      inv_mul_cancel]
  let s : dualTest k ⟶ G.X ⊗ T.toGrp.X :=
    lift ξ.toMul.val (GroupScheme.constantPoint T.toGrp τ₀ (dualTest k) * σ₁)
  have hs₁ : augmentation ≫ s = lift 1 τ₀ := by
    rw [comp_lift, augmentation_comp_lieKernel, MonObj.comp_mul, augmentation_comp_constantPoint,
      haσ₁, mul_one]
  have hZv : Z.val = C⁻¹ * ξ.toMul.val * C * ξ.toMul.val⁻¹ * W.toMul.val := by
    have h := congrArg (fun x : Additive (lieKernel G k) => x.toMul.val) hZW
    simp only [toMul_ofMul, toMul_add, toMul_sub, div_eq_mul_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, adjoint_val] at h
    rw [h, constant_constantPoint, constantPoint_inv, inv_inv]
  have hcomm : ξ.toMul.val⁻¹ * W.toMul.val = W.toMul.val * ξ.toMul.val⁻¹ := by
    have h := congrArg Subtype.val (mul_comm ξ.toMul⁻¹ W.toMul)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have htt : tt = C * Z.val := by
    rw [hZ, mul_inv_cancel_left]
  have hs₂ : s ≫ conjugation j = tt := by
    rw [lift_conjugation, MonObj.mul_comp, hσ₁, constantPoint_comp_hom, ← hn, ← hC, htt, hZv]
    calc ξ.toMul.val * (C * W.toMul.val) * ξ.toMul.val⁻¹
        = ξ.toMul.val * C * (W.toMul.val * ξ.toMul.val⁻¹) := by simp only [mul_assoc]
      _ = ξ.toMul.val * C * (ξ.toMul.val⁻¹ * W.toMul.val) := by rw [hcomm]
      _ = C * (C⁻¹ * ξ.toMul.val * C * ξ.toMul.val⁻¹ * W.toMul.val) := by
        simp only [mul_assoc, mul_inv_cancel_left]
  exact ⟨s.left, ⟨Over.w s, congrArg CommaMorphism.left hs₁⟩, congrArg CommaMorphism.left hs₂⟩

end Tangent

section Density

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

/-- **Regular torus points.** Over an algebraically closed field, a split torus has a rational
point at which no root takes the value `1`. -/
theorem exists_regular [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) :
    ∃ τ₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X, ∀ χ ∈ roots j,
      Lie.characterValue χ (GroupScheme.constantPoint T.toGrp τ₀ (baseTest k)) ≠ 1 := by
  classical
  have hfin : (roots j).Finite := (hT.finite_weightSupport j).subset fun _ h => h.2
  have : AddMonoid.FG (characterLattice T) :=
    AddGroup.fg_iff_addMonoid_fg.mp (Module.Finite.iff_addGroup_fg.mp hT.finite_characterLattice)
  have : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T) := IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
  have : IsDomain (AddMonoidAlgebra k (characterLattice T)) := NoZeroDivisors.to_isDomain _
  let P : AddMonoidAlgebra k (characterLattice T) :=
    ∏ χ ∈ hfin.toFinset, (AddMonoidAlgebra.single χ 1 - 1)
  have hP : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun χ hχ => sub_ne_zero.2 fun h => ?_
    apply (hfin.mem_toFinset.1 hχ).1
    rw [AddMonoidAlgebra.one_def] at h
    exact (AddMonoidAlgebra.single_left_inj one_ne_zero).1 h
  obtain ⟨φ, hφ⟩ := BorelFieldExtension.exists_algHom_ne_zero (K := k) hP
  let t₀ : Lie.AffinePoints T.toGrp k :=
    Lie.affineMap T.toGrp φ (SplitCharacterPoint.universalPoint hT)
  refine ⟨basePoint t₀, fun χ hχ h => hφ ?_⟩
  rw [constantPoint_basePoint] at h
  have hv : (SplitCharacterPoint.value χ t₀ : k) = φ (AddMonoidAlgebra.single χ 1) := by
    rw [SplitCharacterPoint.value_affineMap, SplitCharacterPoint.value_universalPoint,
      SplitCharacterPoint.monomialUnit_val]
  have h1 : (SplitCharacterPoint.value χ t₀ : k) = 1 := congrArg Units.val h
  rw [map_prod]
  exact Finset.prod_eq_zero (hfin.mem_toFinset.2 hχ) (by rw [map_sub, map_one, ← hv, h1, sub_self])

/-- **Density of torus conjugates.** For a split maximal torus of a connected reductive group
over an algebraically closed field, the conjugation morphism `G × T → G` has dense range. -/
theorem denseRange_conjugation [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hj : IsMaximalTorus j) (hT : IsSplitTorus T.toGrp) :
    DenseRange (conjugation j).left := by
  have := hG.smooth
  have := hG.connectedSpace
  have := hT.isAffineHom
  have : Smooth (G.X ⊗ T.toGrp.X).hom := smooth_tensor _ _ hG.smooth hT.smooth
  have := DynamicConnected.irreducibleSpace_of_smooth G
  obtain ⟨τ₀, hreg⟩ := exists_regular j hT
  exact denseRange_of_isTangentSurjectiveAt (conjugation j).left (Over.w (conjugation j))
    (Over.w (lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) τ₀))
    (isTangentSurjectiveAt_conjugation j (maximalTorusCentralizer k G hG T j hj) τ₀
      (exists_adjoint_sub_add j hT τ₀ hreg))

/-- Coordinates of points of `G` factor through the comparison of the two chosen coordinate
algebras of `G.X`. -/
theorem pointCoordinates_eq_comp {A : Type u} [CommRing A] [Algebra k A]
    (y : Lie.AffinePoints G A) :
    Lie.pointCoordinates G y = (PointedCoordinateWeights.pointCoordinates y).comp
      (Lie.pointCoordinates G (PointedCoordinateWeights.universalPoint G.X)) := by
  have hy : Lie.affineMap G (PointedCoordinateWeights.pointCoordinates y)
      (PointedCoordinateWeights.universalPoint G.X) = y := by
    apply PointedCoordinateWeights.pointCoordinates.injective
    change PointedCoordinateWeights.pointCoordinates (PointedCoordinateWeights.pointsMap _ _) = _
    rw [PointedCoordinateWeights.pointCoordinates_naturality,
      PointedCoordinateWeights.coordinates_universalPoint, AlgHom.comp_id]
  conv_lhs => rw [← hy]
  rw [Lie.pointCoordinates_naturality]

/-- The comparison of the two chosen coordinate algebras of `G.X` is injective. -/
theorem pointCoordinates_universalPoint_injective :
    Function.Injective
      (Lie.pointCoordinates G (PointedCoordinateWeights.universalPoint G.X)) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h := DFunLike.congr_fun
    (pointCoordinates_eq_comp ((Lie.pointCoordinates G).symm (AlgHom.id _ _))) g
  rw [Equiv.apply_symm_apply, AlgHom.id_apply, AlgHom.comp_apply, hg, map_zero] at h
  exact h

/-- **Class functions vanishing on a split maximal torus vanish.** Over an algebraically
closed field, a conjugation-invariant regular function on a connected reductive group which
vanishes at every algebra-valued point of a split maximal torus is zero. -/
theorem classFunction_eq_zero [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hj : IsMaximalTorus j) (hT : IsSplitTorus T.toGrp) (f : ClassFunctions.algebra G)
    (hf : ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints T.toGrp A),
      Lie.pointCoordinates G (s ≫ j.hom.hom) f.val = 0) :
    f = 0 := by
  have := hG.smooth
  have := hG.connectedSpace
  have := hT.isAffineHom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  have hinj := PointedCoordinateWeights.dominantPullbackStatement k (G.X ⊗ T.toGrp.X) G.X
    (conjugation j) inferInstance ⟨denseRange_conjugation j hG hj hT⟩
  suffices h : f.val = 0 from Subtype.ext h
  apply pointCoordinates_universalPoint_injective
  rw [map_zero]
  apply hinj
  rw [map_zero]
  let u := PointedCoordinateWeights.universalPoint (G.X ⊗ T.toGrp.X)
  change PointedCoordinateWeights.pointCoordinates (u ≫ conjugation j) _ = 0
  have h1 := DFunLike.congr_fun (pointCoordinates_eq_comp (u ≫ conjugation j)) f.val
  rw [AlgHom.comp_apply] at h1
  rw [← h1, comp_conjugation]
  exact ((ClassFunctions.mem_algebra_iff_invariant G).1 f.property _ _ _).trans (hf _ _)

end Density

end Langlands.GroupScheme.TorusConjugation
