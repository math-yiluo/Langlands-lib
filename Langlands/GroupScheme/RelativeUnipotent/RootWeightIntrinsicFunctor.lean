import Langlands.GroupScheme.RelativeUnipotent.RootWeightIntrinsicCutoff

/-! # Intrinsic root-weight subgroup functors on all scheme tests -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  (C : RootHeightChart U) (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

/-- Read an arbitrary scheme point in the actual affine-point group over its
relative global sections. The equivalence respects the actual group law. -/
def intrinsicPoints (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ U.X) ≃* U.affinePointFunctor.obj ((algΓ (CommRingCat.of R)).obj T).unop :=
  (AffineLinearEmbedding.pointsMulEquiv U C.chart T).symm.trans
    (pointsEquiv U.affinePointFunctor C.polynomialCorepresentation T)

/-- This passage to relative global sections retains the original root coordinates. -/
theorem intrinsicPoints_coord (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ U.X)
    (k : Fin C.dimension) :
    coord C.polynomialCorepresentation (C.intrinsicPoints T x) (X k) =
      C.coordinates T x k := by
  change (C.polynomialCorepresentation.homEquiv.symm
    (pointsEquiv U.affinePointFunctor C.polynomialCorepresentation T
      (x ≫ C.chart.inv))).hom (X k) = _
  rw [pointsEquiv_apply, Equiv.symm_apply_apply]
  rfl

/-- Reading points in this model commutes with restriction along any scheme map. -/
theorem intrinsicPoints_natural {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ U.X) :
    C.intrinsicPoints T' (a ≫ x) =
      U.affinePointFunctor.map ((algΓ (CommRingCat.of R)).map a).unop
        (C.intrinsicPoints T x) := by
  change pointsEquiv U.affinePointFunctor C.polynomialCorepresentation T'
    ((a ≫ x) ≫ C.chart.inv) = _
  rw [Category.assoc, pointsEquiv_naturality]
  rfl

/-- The intrinsic cyclic cutoff on the chart group, defined on every scheme
via its actual group-valued relative-section coordinates. -/
def intrinsicCutoff (v : I → ℤ) (r : ℕ) : SubgroupFunctor U where
  carrier T := (weightSubgroup C.polynomialCorepresentation
    ((C.polynomialTorusAction j hroot hu).alongCocharacter v)
      (cyclicTail (fun _ : PUnit => (1 : ℤ)) r)
        ((algΓ (CommRingCat.of R)).obj T).unop).comap
          (C.intrinsicPoints T).toMonoidHom
  comp_mem a x hx := by
    change C.intrinsicPoints _ (a ≫ x) ∈ weightSubgroup _ _ _ _
    rw [C.intrinsicPoints_natural]
    exact map_mem_weightSubgroup _ _ _ ((algΓ (CommRingCat.of R)).map a).unop hx

/-- The intrinsic subgroup agrees with the supported root coordinates on every
scheme test, without requiring that test scheme to be affine or reduced. -/
theorem mem_intrinsicCutoff_iff (v : I → ℤ) (w : Fin C.dimension → ℕ)
    (hw : ∀ k, coPairing (ch (index k)) v = w k)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ U.X) {r : ℕ} (hr : 0 < r) :
    x ∈ (C.intrinsicCutoff j hroot hu v r).carrier T ↔
      ∀ k, w k < r → C.coordinates T x k = 0 := by
  have ha : (fun _ : PUnit => (1 : ℤ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h PUnit.unit)
  change C.intrinsicPoints T x ∈ weightSubgroup _ _ _ _ ↔ _
  rw [(C.cyclicCoordinates j hroot hu v w hw).mem_iff ha _ hr]
  change (∀ k, w k < r →
    coord C.polynomialCorepresentation (C.intrinsicPoints T x) (X k) = 0) ↔ _
  simp only [C.intrinsicPoints_coord]

/-- A positive cocharacter realization of the root weights identifies the entire
intrinsic subgroup functor with the original unscaled represented term. -/
theorem intrinsicCutoff_eq_weightSubgroup (W : RootWeightData C)
    (v : I → ℤ) (q : ℕ) (hq : 0 < q)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k) (d : ℕ) :
    C.intrinsicCutoff j hroot hu v (q * (d + 1)) = W.subgroup d := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [C.mem_intrinsicCutoff_iff j hroot hu v (fun k => q * W.weight k)
    (by intro k; simpa only [Nat.cast_mul] using hw k) T x
    (Nat.mul_pos hq (Nat.zero_lt_succ d)), W.mem_subgroup_iff]
  simp only [Nat.mul_lt_mul_left hq]

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart
