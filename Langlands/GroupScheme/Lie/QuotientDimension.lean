import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.MultiplicativeLaurent

/-! # Strict Lie-dimension decrease for smooth quotients killing Gm -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The dual-number unit `1 + ε`. -/
def gmInfinitesimalUnit (k : Type u) [CommRing k] : (DualNumber k)ˣ where
  val := (1, 1)
  inv := (1, -1)
  val_inv := by
    apply TrivSqZeroExt.ext <;> simp
  inv_val := by
    apply TrivSqZeroExt.ext <;> simp

/-- The actual identity-kernel point of Gm given by `1 + ε`. -/
def gmTangent (k : Type u) [CommRing k] :
    lieKernel (Gm (Spec (CommRingCat.of k))).toGrp k :=
  ⟨(Gm.affineUnitsEquiv (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (DualNumber k))).symm
      (gmInfinitesimalUnit k), by
    apply (Gm.affineUnitsEquiv (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) k)).injective
    change Gm.affineUnitsEquiv (CommRingCat.of k) _
      (affinePointMap (Gm (Spec (CommRingCat.of k))).toGrp
        (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k)) _) =
      Gm.affineUnitsEquiv (CommRingCat.of k) _ 1
    rw [Gm.affineUnitsEquiv_naturality, MulEquiv.apply_symm_apply, map_one]
    apply Units.ext
    rfl⟩

/-- This actual Gm tangent is nonzero over a nontrivial coefficient ring. -/
theorem gmTangent_ne_one (k : Type u) [CommRing k] [Nontrivial k] :
    gmTangent k ≠ 1 := by
  intro h
  have hu : gmInfinitesimalUnit k = 1 := by
    have he := congrArg
      (fun x : lieKernel (Gm (Spec (CommRingCat.of k))).toGrp k =>
        Gm.affineUnitsEquiv (CommRingCat.of k)
          (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) x.val) h
    simpa only [gmTangent, MulEquiv.apply_symm_apply, OneMemClass.coe_one,
      map_one] using he
  have hs := congrArg (fun z : (DualNumber k)ˣ => (z.val).snd) hu
  exact one_ne_zero hs

variable {k : Type u} [Field k]

/-- A smooth affine homomorphism with a nonzero infinitesimal identity point
in its kernel strictly lowers the dimension of the actual Lie kernel. -/
theorem dimension_lt_of_smooth_of_kernel
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (q : G ⟶ Q) (hq : Smooth q.hom.hom.left)
    (X : Additive (lieKernel G k)) (hX : X ≠ 0)
    (hkill : targetMapLinear q k X = 0) :
    dimension Q < dimension G := by
  have hsurj := targetMapLinear_surjective_of_smooth q k hq
  have hle : dimension Q ≤ dimension G :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  apply lt_of_le_of_ne hle
  intro heq
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := targetMapLinear q k) heq.symm).mpr hsurj
  exact hX (hinj (hkill.trans (map_zero (targetMapLinear q k)).symm))

/-- A smooth affine homomorphism killing a monomorphic actual copy of Gm
strictly lowers the actual Lie dimension. -/
theorem dimension_lt_of_smooth_kills_gm
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (q : G ⟶ Q) (hq : Smooth q.hom.hom.left)
    (s : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    [Mono s.hom.hom] (hkill : s.hom.hom ≫ q.hom.hom = 1) :
    dimension Q < dimension G := by
  have : IsAffine (Gm.relativeLaurent (CommRingCat.of k)).left := by
    dsimp [Gm.relativeLaurent]
    infer_instance
  have : IsAffine (Gm (Spec (CommRingCat.of k))).X.left :=
    IsAffine.of_isIso (Gm.relativeLaurentIso (CommRingCat.of k)).hom.left
  have : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom := inferInstance
  let Y : Additive (lieKernel (Gm (Spec (CommRingCat.of k))).toGrp k) :=
    Additive.ofMul (gmTangent k)
  have hY : Y ≠ 0 := by
    intro h
    exact gmTangent_ne_one k (congrArg Additive.toMul h)
  apply dimension_lt_of_smooth_of_kernel q hq (targetMapLinear s k Y)
  · intro h
    apply hY
    exact targetMapLinear_injective s k
      (h.trans (map_zero (targetMapLinear s k)).symm)
  · apply Additive.toMul.injective
    apply Subtype.ext
    change (gmTangent k).val ≫ s.hom.hom ≫ q.hom.hom = 1
    rw [hkill, MonObj.comp_one]

end Langlands.GroupScheme.Lie
