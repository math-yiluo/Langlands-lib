import Langlands.GroupScheme.RelativeUnipotent.RootWeightTermPolynomial
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Intrinsic cyclic filtrations on the actual positive subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

/-- The actual group homomorphism to the explicit polynomial corepresentation.
Its underlying map is the identity of the term's coordinate affine space. -/
def toTermPolynomialModel (d : ℕ) :
    W.groupScheme d ⟶ Corepresented.groupScheme (W.groupScheme d).affinePointFunctor
      (W.termPolynomialCorepresentation d) :=
  AffineCorepresentation.toModel (W.groupScheme d) (W.termChart d)

/-- Reading a term point in its explicit polynomial model retains its own
coordinate functions on every scheme test. -/
theorem points_toTermPolynomialModel_coord (d : ℕ)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme d).X)
    (k : Fin (Nat.card (W.support d))) :
    coord (W.termPolynomialCorepresentation d)
      (pointsEquiv (W.groupScheme d).affinePointFunctor (W.termPolynomialCorepresentation d)
        T (x ≫ (W.toTermPolynomialModel d).hom.hom)) (X k) =
      (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd k := by
  rw [coord, pointsEquiv_apply, Equiv.symm_apply_apply]
  change _ = (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd k
  simp only [toTermPolynomialModel, AffineCorepresentation.toModel,
    AffineCorepresentation.iso, termChart, Iso.refl_inv, Category.comp_id]
  rfl

/-- The intrinsic cyclic weight subgroup functor on the actual represented
positive subgroup, rather than the auxiliary full regular root-chart group. -/
def positiveIntrinsicCutoff (v : I → ℤ) (r : ℕ) : SubgroupFunctor (W.groupScheme 0) :=
  (cutSubgroupFunctor (isCutOutBy_weightIdeal (W.termPolynomialCorepresentation 0)
    ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
      (cyclicTail (fun _ : PUnit => (1 : ℤ)) r))).comap (W.toTermPolynomialModel 0)

/-- The original coordinate cutoff restricted to the positive subgroup is
exactly low-coordinate vanishing in that subgroup's own affine space. -/
theorem mem_comap_zeroInclusion_iff (d : ℕ)
    (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme 0).X) :
    x ∈ ((W.subgroup d).comap (W.inclusion 0)).carrier T ↔
      ∀ k, W.weight (W.enumeration 0 k).val < d + 1 →
        (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd k = 0 := by
  rw [SubgroupFunctor.mem_comap, W.mem_subgroup_iff]
  constructor
  · intro hx k hk
    have h := hx (W.enumeration 0 k).val hk
    rw [W.coordinates_inclusion] at h
    simpa only [dite_eq_left (W.enumeration 0 k).property,
      Subtype.coe_eta, Equiv.symm_apply_apply] using h
  · intro hx k hk
    rw [W.coordinates_inclusion]
    split_ifs with hpos
    · have h := hx ((W.enumeration 0).symm ⟨k, hpos⟩)
      simpa only [Equiv.apply_symm_apply] using h (by
        simpa only [Equiv.apply_symm_apply] using hk)
    · rfl

/-- The intrinsic positive-subgroup cutoff has its exact supported-coordinate
meaning on every scheme test. -/
theorem mem_positiveIntrinsicCutoff_iff (v : I → ℤ) (q : ℕ) (hq : 0 < q)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)
    (d : ℕ) (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (W.groupScheme 0).X) :
    x ∈ (W.positiveIntrinsicCutoff j hroot hu v (q * (d + 1))).carrier T ↔
      ∀ k, W.weight (W.enumeration 0 k).val < d + 1 →
        (VectorGroup.coordinates (CommRingCat.of R) _ T x).toAdd k = 0 := by
  have ha : (fun _ : PUnit => (1 : ℤ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h PUnit.unit)
  rw [positiveIntrinsicCutoff, SubgroupFunctor.mem_comap, mem_cutSubgroupFunctor]
  rw [(W.positiveTermCyclicCoordinates j hroot hu v q hw).mem_iff ha _
    (Nat.mul_pos hq (Nat.zero_lt_succ d))]
  change (∀ k, q * W.weight (W.enumeration 0 k).val < q * (d + 1) →
    coord (W.termPolynomialCorepresentation 0)
      (pointsEquiv (W.groupScheme 0).affinePointFunctor (W.termPolynomialCorepresentation 0)
        T (x ≫ (W.toTermPolynomialModel 0).hom.hom)) (X k) = 0) ↔ _
  simp only [W.points_toTermPolynomialModel_coord, Nat.mul_lt_mul_left hq]

/-- Every original filtration term, viewed inside the actual positive subgroup,
is an intrinsic cyclic subgroup on ALL scheme tests. The original weights and
cutoff d+1 remain unscaled. -/
theorem positiveIntrinsicCutoff_eq_comap (v : I → ℤ) (q : ℕ) (hq : 0 < q)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k) (d : ℕ) :
    W.positiveIntrinsicCutoff j hroot hu v (q * (d + 1)) =
      (W.subgroup d).comap (W.inclusion 0) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [W.mem_positiveIntrinsicCutoff_iff j hroot hu v q hq hw,
    W.mem_comap_zeroInclusion_iff]

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
