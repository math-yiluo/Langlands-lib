import Langlands.GroupScheme.Rational.RationalCenterComparisonStatement
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.RingTheory.LocalFieldDensity.Density
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # The scheme center of a reductive group over a local field

For a connected reductive group `M` over a nonarchimedean local field `F`, the full scheme center
evaluated on `F` equals the abstract center of `M(F)`.

The forward inclusion is `schemeCenterPoints_le_center`. For the reverse inclusion, let `z` be a
central `F`-point. Since `Spec F` is terminal over itself, it suffices that `z` commutes with the
identity point of `M`, that is, that left and right multiplication by `z` agree on the coordinate
algebra `O(M)`. The two coordinate maps `O(M) → O(M)` agree after composing with every `F`-point
`O(M) → F`, because `z` commutes with all `F`-points. They therefore agree, because the `F`-points
of the smooth domain `O(M)` separate its elements (`exists_algHom_apply_ne_zero`, using the
normed field structure of `F` defined by its rank-one valuation).
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry ValuativeRel
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RationalCenterComparisonProof

section Separating

variable {k : Type u} [CommRing k] (M : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom M.X.hom]

/-- If the `k`-points of an affine group `M` separate the elements of its coordinate algebra,
then every point in the center of `M(k)` lies in the scheme center of `M`. -/
theorem center_le_schemeCenterPoints
    (hsep : ∀ d : Lie.coordinateAlgebra M, d ≠ 0 →
      ∃ y : Lie.coordinateAlgebra M →ₐ[CommRingCat.of k] CommRingCat.of k, y d ≠ 0) :
    Subgroup.center (rationalPoints M) ≤ schemeCenterPoints M := by
  intro z hz
  let e := Lie.coordinateIso M
  let τ : M.X ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.mkIdTerminal.from M.X
  let u : Lie.AffinePoints M (Lie.coordinateAlgebra M) := e.hom
  let p₁ : Lie.AffinePoints M (Lie.coordinateAlgebra M) := (u ≫ τ ≫ z) * u
  let p₂ : Lie.AffinePoints M (Lie.coordinateAlgebra M) := u * (u ≫ τ ≫ z)
  -- after evaluation at a `k`-point, `z` commutes with the universal point
  have hpt : ∀ y : Lie.coordinateAlgebra M →ₐ[CommRingCat.of k] CommRingCat.of k,
      Lie.affineMap M y p₁ = Lie.affineMap M y p₂ := by
    intro y
    let T₀ := (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)))
    let i : T₀ ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.mkIdTerminal.from T₀
    have : IsIso i := by
      have : IsIso ((Over.forget _).map i) := by
        change IsIso i.left
        rw [Over.mkIdTerminal_from_left]
        exact (inferInstance : IsIso (Spec.map (𝟙 (CommRingCat.of k))))
      exact isIso_of_reflects_iso i (Over.forget _)
    let s := (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom y).op
    let w : T₀ ⟶ M.X := s ≫ u
    have hw : w = i ≫ (inv i ≫ w) := by simp
    have hτ : s ≫ u ≫ τ = i := Over.mkIdTerminal.hom_ext _ _
    have hz' : s ≫ u ≫ τ ≫ z = i ≫ z := by
      rw [← hτ]
      simp only [Category.assoc]
    change s ≫ ((u ≫ τ ≫ z) * u) = s ≫ (u * (u ≫ τ ≫ z))
    rw [MonObj.comp_mul, MonObj.comp_mul, hz']
    change (i ≫ z) * w = w * (i ≫ z)
    rw [hw, ← MonObj.comp_mul, ← MonObj.comp_mul, Subgroup.mem_center_iff.mp hz (inv i ≫ w)]
  -- `z` commutes with the identity point of `M`
  have key : (τ ≫ z) * 𝟙 M.X = 𝟙 M.X * (τ ≫ z) := by
    apply (cancel_epi e.hom).mp
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id]
    change p₁ = p₂
    apply (Lie.pointCoordinates M).injective
    ext d
    by_contra hd
    obtain ⟨y, hy⟩ := hsep _ (sub_ne_zero.mpr hd)
    have h₁ := Lie.pointCoordinates_naturality M y p₁
    rw [hpt y, Lie.pointCoordinates_naturality] at h₁
    apply hy
    rw [map_sub, sub_eq_zero]
    exact (DFunLike.congr_fun h₁ d).symm
  intro T' a h
  have ha : a = h ≫ τ := Over.mkIdTerminal.hom_ext _ _
  have hc := congrArg (h ≫ ·) key
  simp only [MonObj.comp_mul, Category.comp_id] at hc
  rw [ha, Category.assoc]
  exact hc

end Separating

/-- Over a nonarchimedean local field `F`, the `F`-points of a smooth `F`-domain with an
`F`-point separate its elements. -/
theorem exists_algHom_apply_ne_zero_of_localField (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {A : Type*} [CommRing A] [Algebra F A]
    [Algebra.Smooth F A] [IsDomain A] (x : A →ₐ[F] F) {a : A} (ha : a ≠ 0) :
    ∃ y : A →ₐ[F] F, y a ≠ 0 := by
  let _ := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let _ : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let _ : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  have : CompleteSpace F := inferInstance
  exact Langlands.RingTheory.LocalFieldDensity.exists_algHom_apply_ne_zero x ha

end RationalCenterComparisonProof

open RationalCenterComparisonProof in
/-- For a connected reductive group over a nonarchimedean local field, the full scheme center
evaluated on `F` equals the abstract center of the group of `F`-points. -/
theorem rationalCenterComparison : RationalCenterComparisonStatement.{u} := by
  intro F _ _ _ _ M hM
  have := hM.smooth
  have := hM.isAffineHom
  have := hM.connectedSpace
  have := CharacterLatticeProof.isDomain_coord M
  set D := Lie.coordinateAlgebra M
  have hsm : Smooth ((algSpec (CommRingCat.of F)).obj (op D)).hom := by
    have : IsIso (Lie.coordinateIso M).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso M).hom))
    have h : Smooth ((Lie.coordinateIso M).hom.left ≫ M.X.hom) := inferInstance
    simpa only [Over.w] using h
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of F) D))) at hsm
  have : Algebra.Smooth (CommRingCat.of F) D :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hsm)
  refine le_antisymm (schemeCenterPoints_le_center M)
    (center_le_schemeCenterPoints M fun d hd => ?_)
  exact exists_algHom_apply_ne_zero_of_localField F (A := D) (Lie.coordinateOrigin M) hd

end Langlands.GroupScheme
