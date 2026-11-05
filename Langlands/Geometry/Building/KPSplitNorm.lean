import Langlands.Geometry.Building.KPSplitUnitKernel
import Langlands.Geometry.Building.KPTorusNormNaturality

/-! # Surjectivity of bounded norms for split tori -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {Γk ΓL : Type*} [LinearOrderedCommGroupWithZero Γk]
  [LinearOrderedCommGroupWithZero ΓL]
  (vk : Valuation k Γk) (vL : Valuation L ΓL)

private instance gm_isAffine : IsAffine (Gm (Spec (CommRingCat.of k))).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (Gm.toSpecZ (Spec (CommRingCat.of k))))
  infer_instance

/-- Scalar unit-norm surjectivity lifts bounded points of the actual multiplicative group. -/
theorem gm_kernel_le_torusNormIwahori
    (hunit : ∀ a : kˣ, vk (a : k) = 1 →
      ∃ b : Lˣ, vL (b : L) = 1 ∧ Units.map (Algebra.norm k) b = a) :
    characterValuationKernel vk (Gm (Spec (CommRingCat.of k))).toGrp ≤
      torusNormIwahori k L vL (Gm (Spec (CommRingCat.of k))) := by
  intro t ht
  obtain ⟨b, hb, hnorm⟩ := hunit
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k))) t)
    ((mem_gm_characterValuationKernel k vk t).mp ht)
  let y := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))).symm b
  have hy : y ∈ characterValuationKernel vL (Gm (Spec (CommRingCat.of L))).toGrp := by
    rw [mem_gm_characterValuationKernel]
    simpa only [y, MulEquiv.apply_symm_apply] using hb
  let x := rationalPoints.map (Gm.baseChangeIso (baseMap k L)).inv y
  have hx : x ∈ characterValuationKernel vL
      ((CommGroupScheme.baseChange (baseMap k L)).obj
        (Gm (Spec (CommRingCat.of k)))).toGrp :=
    map_characterValuationKernel_le vL (Gm.baseChangeIso (baseMap k L)).inv ⟨y, hy, rfl⟩
  refine (mem_torusNormIwahori k L).mpr ⟨x, hx, ?_⟩
  apply (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).injective
  rw [GaloisPoint.gm_rational_units_norm]
  have hxunits :
      Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
        (Gm.baseChangeUnitsEquiv (baseMap k L)
          (Over.mk (𝟙 (Spec (CommRingCat.of L)))) x) = b := by
    change Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
      (Gm.baseChangeUnitsEquiv (baseMap k L)
        (Over.mk (𝟙 (Spec (CommRingCat.of L))))
          (y ≫ (Gm.baseChangeIso (baseMap k L)).inv.hom.hom)) = b
    rw [Gm.baseChangeUnitsEquiv_baseChangeIso_inv]
    exact (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))).apply_symm_apply b
  rw [hxunits, hnorm]

/-- The norm of bounded points of a split torus reaches every bounded base point,
provided the corresponding assertion holds on scalar units. -/
theorem split_kernel_le_torusNormIwahori
    (hunit : ∀ a : kˣ, vk (a : k) = 1 →
      ∃ b : Lˣ, vL (b : L) = 1 ∧ Units.map (Algebra.norm k) b = a)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    (hT : IsSplitTorus T.toGrp) :
    characterValuationKernel vk T.toGrp ≤ torusNormIwahori k L vL T := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  intro t ht
  let s := rationalPoints.map e.hom t
  have hs : s ∈ characterValuationKernel vk (splitTorus (Spec (CommRingCat.of k)) I) :=
    map_characterValuationKernel_le vk e.hom ⟨t, ht, rfl⟩
  have hdec := congrArg (rationalPoints.map e.inv) (splitPoint_decomposition k I s)
  rw [map_prod] at hdec
  have he : rationalPoints.map e.inv s = t := by
    change (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = t
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
    rfl
  rw [he] at hdec
  rw [hdec]
  apply Subgroup.prod_mem
  intro i _
  let a := rationalPoints.map
    (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i)) s
  have ha : a ∈ characterValuationKernel vk (Gm (Spec (CommRingCat.of k))).toGrp :=
    map_characterValuationKernel_le vk
      (CommGroupScheme.groupHom (splitTorus.proj (Spec (CommRingCat.of k)) I i))
      ⟨s, hs, rfl⟩
  have hanorm := gm_kernel_le_torusNormIwahori k L vk vL hunit ha
  have hmap := map_torusNormIwahori_le k L vL
    (splitTorus.single (Spec (CommRingCat.of k)) I i ≫ eC.inv)
    ⟨a, hanorm, rfl⟩
  change (a ≫ (CommGroupScheme.groupHom
    (splitTorus.single (Spec (CommRingCat.of k)) I i ≫ eC.inv)).hom.hom) ∈ _ at hmap
  rw [comp_groupHom_comp] at hmap
  exact hmap

variable [vk.HasExtension vL]
  (hinv : ∀ (σ : L ≃ₐ[k] L) (z : L), vL (σ z) = vL z)

/-- The actual rational norm restricted to its character-valuation kernels. -/
def boundedRationalNorm (T : CommGroupScheme (Spec (CommRingCat.of k)))
    [IsAffine T.X.left] :
    characterValuationKernel vL ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp →*
      characterValuationKernel vk T.toGrp :=
  ((rationalNorm k L T).comp
    (characterValuationKernel vL
      ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp).subtype).codRestrict _
        (fun x => torusNormIwahori_le_characterValuationKernel vk vL hinv T
          ⟨x.val, x.property, rfl⟩)

/-- Surjectivity of the restricted norm on split tori reduces to scalar unit norms. -/
theorem boundedRationalNorm_surjective_of_split
    (hunit : ∀ a : kˣ, vk (a : k) = 1 →
      ∃ b : Lˣ, vL (b : L) = 1 ∧ Units.map (Algebra.norm k) b = a)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]
    (hT : IsSplitTorus T.toGrp) :
    Function.Surjective (boundedRationalNorm k L vk vL hinv T) := by
  intro t
  obtain ⟨x, hx, hxt⟩ := (mem_torusNormIwahori k L).mp
    (split_kernel_le_torusNormIwahori k L vk vL hunit T hT t.property)
  exact ⟨⟨x, hx⟩, Subtype.ext hxt⟩

end Langlands.Geometry.Building
