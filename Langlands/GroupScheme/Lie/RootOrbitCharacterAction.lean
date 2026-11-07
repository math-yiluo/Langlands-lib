import Langlands.GroupScheme.Lie.RootOrbitRelativeWeights
import Langlands.GroupScheme.Rational.CoordinateCotangentWeights
import Langlands.GroupScheme.Lie.ActionDifferential
import Langlands.GroupScheme.GaloisPointRational

/-! # The actual torus action on root-orbit field coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section PointBaseChange

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K

/-- Actual affine points of a scheme base change commute with the base change
of a group-scheme homomorphism. -/
theorem affineBaseChangeEquiv_comp_baseChange
    {H G : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : Lie.AffinePoints ((GroupScheme.baseChange b).obj H) A) :
    Lie.affineBaseChangeEquiv k K G A (x ≫ ((GroupScheme.baseChange b).map i).hom.hom) =
      Lie.affineBaseChangeEquiv k K H A x ≫ i.hom.hom := by
  apply Over.OverMorphism.ext
  simp only [Lie.affineBaseChangeEquiv_left]
  change (x.left ≫ ((Over.pullback b).map i.hom.hom).left) ≫ _ =
    (x.left ≫ _) ≫ i.hom.hom.left
  simp only [Over.pullback_map_left, Category.assoc, CategoryTheory.Limits.pullback.lift_fst]
  rfl

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T

/-- An original-field point of a torus, viewed as a `K`-point of its actual
scheme base change. -/
def rationalBaseChangePoint (h : Lie.AffinePoints T.toGrp k) :
    Lie.AffinePoints (T_K).toGrp K :=
  (Lie.affineBaseChangeEquiv k K T.toGrp K).symm
    (Lie.affineMap T.toGrp (Algebra.ofId k K) h)

@[simp]
theorem affineBaseChangeEquiv_rationalBaseChangePoint (h : Lie.AffinePoints T.toGrp k) :
    Lie.affineBaseChangeEquiv k K T.toGrp K (rationalBaseChangePoint k K T h) =
      Lie.affineMap T.toGrp (Algebra.ofId k K) h :=
  (Lie.affineBaseChangeEquiv k K T.toGrp K).apply_symm_apply _

/-- The coefficient map inverse to `σ`, as a `K`-algebra map out of the twisted test. -/
private def galoisTestInverse (σ : K ≃ₐ[k] K) : Lie.GaloisTestAlgebra σ K →ₐ[K] K where
  toRingHom := (σ.symm.toRingHom : K →+* K)
  commutes' c := σ.symm_apply_apply c

/-- Canonical Galois transport of a character, evaluated at an original-field
point, is the coefficient automorphism applied to the original value. -/
theorem characterValue_galoisRepresentation_rationalBaseChangePoint
    (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) (h : Lie.AffinePoints T.toGrp k) :
    (Lie.characterValue (characterLattice.galoisRepresentation k K T σ χ)
        (rationalBaseChangePoint k K T h) : K) =
      σ (Lie.characterValue χ (rationalBaseChangePoint k K T h) : K) := by
  have hp : Lie.affineMap ((GroupScheme.baseChange b).obj T.toGrp) (galoisTestInverse k K σ)
      (Lie.galoisTestPoint k K σ K T.toGrp (rationalBaseChangePoint k K T h)) =
        rationalBaseChangePoint k K T h := by
    apply (Lie.affineBaseChangeEquiv k K T.toGrp K).injective
    rw [Lie.affineBaseChangeEquiv_naturality, Lie.affineBaseChangeEquiv_galoisTestPoint,
      affineBaseChangeEquiv_rationalBaseChangePoint]
    change Lie.affineMap T.toGrp ((galoisTestInverse k K σ).restrictScalars k)
        (Lie.affineMap T.toGrp (Algebra.ofId k (Lie.GaloisTestAlgebra σ K)) h) = _
    rw [← Lie.affineMap_comp]
    exact congrArg (fun f => Lie.affineMap T.toGrp f h) (Subsingleton.elim _ _)
  have h2 : Lie.characterValue χ (rationalBaseChangePoint k K T h) =
      Units.map (galoisTestInverse k K σ).toRingHom.toMonoidHom
        (Lie.characterValue χ
          (Lie.galoisTestPoint k K σ K T.toGrp (rationalBaseChangePoint k K T h))) :=
    (congrArg (Lie.characterValue χ) hp).symm.trans
      (CoordinateWeights.characterValue_affineMap (galoisTestInverse k K σ) χ _)
  rw [Lie.characterValue_galoisRepresentation, h2]
  change _ = σ (σ.symm _)
  rw [AlgEquiv.apply_symm_apply]

end PointBaseChange

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- Extending coefficients and passing to the actual scheme base change carries
the adjoint action of an original torus point to that of its base change. -/
theorem kernelBaseChange_adjoint_rationalBaseChangePoint
    (h : Lie.AffinePoints T.toGrp k) (w : Additive (lieKernel G k)) :
    (Lie.kernelBaseChangeLinearEquiv k L G L).symm
        (lieKernelMapLinear G (Algebra.ofId k L) (adjoint G k (h ≫ j.hom.hom) w)) =
      adjoint G_L L (rationalBaseChangePoint k L T h ≫ (j_L).hom.hom)
        ((Lie.kernelBaseChangeLinearEquiv k L G L).symm
          (lieKernelMapLinear G (Algebra.ofId k L) w)) := by
  apply (Lie.kernelBaseChangeLinearEquiv k L G L).injective
  rw [LinearEquiv.apply_symm_apply, Lie.kernelBaseChangeLinearEquiv_adjoint,
    LinearEquiv.apply_symm_apply, adjoint_naturality]
  congr 2
  rw [affineBaseChangeEquiv_comp_baseChange k L j,
    affineBaseChangeEquiv_rationalBaseChangePoint]
  rfl

omit [IsAffineHom G.X.hom] in
/-- On an actual weight space of the split base change, the adjoint action of
a base-changed original torus point is scalar multiplication by the character value. -/
theorem adjoint_rationalBaseChangePoint_of_mem_weightSpace
    [IsAffineHom G.X.hom] (χ : characterLattice T_L)
    {y : Additive (lieKernel G_L L)} (hy : y ∈ weightSpace (T := T_L) j_L χ)
    (h : Lie.AffinePoints T.toGrp k) :
    adjoint G_L L (rationalBaseChangePoint k L T h ≫ (j_L).hom.hom) y =
      (Lie.characterValue χ (rationalBaseChangePoint k L T h) : L) • y := by
  have hid : lieKernelMapLinear G_L (Algebra.ofId (CommRingCat.of L) L) y = y := by
    have he : Algebra.ofId (CommRingCat.of L) L = AlgHom.id (CommRingCat.of L) L :=
      AlgHom.ext fun _ => rfl
    rw [he]
    exact Lie.kernelCoefficientMap_id G_L y
  have hy' := hy L (rationalBaseChangePoint k L T h)
  rw [hid] at hy'
  exact hy'

/-- The value of an actual split root at a base-changed original torus point
lies in the stabilizer field of that root. -/
def rootOrbitCharacterValue (β : roots (T := T_L) (G := G_L) j_L)
    (h : Lie.AffinePoints T.toGrp k) : rootOrbitField k L j β :=
  ⟨Lie.characterValue β.val (rationalBaseChangePoint k L T h), by
    rw [mem_rootOrbitField_iff]
    intro σ hσ
    rw [← characterValue_galoisRepresentation_rationalBaseChangePoint, hσ]⟩

@[simp]
theorem rootOrbitCharacterValue_coe (β : roots (T := T_L) (G := G_L) j_L)
    (h : Lie.AffinePoints T.toGrp k) :
    (rootOrbitCharacterValue k L j β h : L) =
      Lie.characterValue β.val (rationalBaseChangePoint k L T h) := rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- The embedding attached to an orbit root sends the field value to that
root's own value. -/
theorem rootOrbitEmbeddingEquiv_characterValue (β : roots (T := T_L) (G := G_L) j_L)
    (ρ : MulAction.orbit (L ≃ₐ[k] L) β) (h : Lie.AffinePoints T.toGrp k) :
    rootOrbitEmbeddingEquiv k L j β ρ (rootOrbitCharacterValue k L j β h) =
      Lie.characterValue ρ.val.val (rationalBaseChangePoint k L T h) := by
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ρ.property
  have hρ : ρ = σ • Langlands.Algebra.FiniteGaloisOrbits.orbitBasepoint k L β := by
    apply Subtype.ext
    rw [MulAction.orbit.coe_smul]
    exact hσ.symm
  subst hρ
  change Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv k L β
      (σ • Langlands.Algebra.FiniteGaloisOrbits.orbitBasepoint k L β)
      (rootOrbitCharacterValue k L j β h) = _
  rw [Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_smul,
    Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_basepoint]
  change σ (Lie.characterValue β.val (rationalBaseChangePoint k L T h) : L) = _
  rw [← characterValue_galoisRepresentation_rationalBaseChangePoint]
  rfl

variable [LocallyOfFiniteType G.X.hom]

attribute [local instance] orbitFintype

/-- The fixed ambient vector of a field coordinate is the sum of its coherent
root-line vectors at the conjugate embeddings. -/
theorem rootOrbitFieldFixedSpanEquiv_val
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := T_L) (G := G_L) j_L) (x : rootOrbitField k L j β) :
    (rootOrbitFieldFixedSpanEquiv k L j hG hj hT β x).val.val =
      ∑ ρ, ((rootOrbitLineEquiv k L j hG hj hT β ρ
        (rootOrbitEmbeddingEquiv k L j β ρ x) : weightSpace (T := T_L) j_L ρ.val.val) :
          Additive (lieKernel G_L L)) :=
  rootOrbitSumEquiv_val k L j hT β _

/-- Every original torus point acts on the constructed actual relative-weight
vector of a field coordinate by multiplication with the actual root value. -/
theorem adjoint_rootOrbitFieldWeightSpaceEquiv
    (f : S ⟶ T) (a : characterLattice S)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (ha : a ≠ 0) (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (h : Lie.AffinePoints T.toGrp k) (x : rootOrbitField k L j β) :
    adjoint G k (h ≫ j.hom.hom)
        (rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit x).val =
      (rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit
        (rootOrbitCharacterValue k L j β h * x)).val := by
  apply (Lie.baseChangeFixedLieEquiv k L G).injective
  apply Subtype.ext
  rw [Lie.baseChangeFixedLieEquiv_val, kernelBaseChange_adjoint_rationalBaseChangePoint,
    ← Lie.baseChangeFixedLieEquiv_val, rootOrbitFieldWeightSpaceEquiv_baseChange,
    rootOrbitFieldWeightSpaceEquiv_baseChange, rootOrbitFieldFixedSpanEquiv_val,
    rootOrbitFieldFixedSpanEquiv_val, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [adjoint_rationalBaseChangePoint_of_mem_weightSpace k L j ρ.val.val
      (rootOrbitLineEquiv k L j hG hj hT β ρ (rootOrbitEmbeddingEquiv k L j β ρ x)).property h,
    map_mul, rootOrbitEmbeddingEquiv_characterValue, ← smul_eq_mul, LinearEquiv.map_smul]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- Base-field scalars act compatibly on the constructed relative-weight vectors. -/
theorem rootOrbitFieldWeightSpaceEquiv_smul
    (f : S ⟶ T) (a : characterLattice S)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (ha : a ≠ 0) (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (c : k) (x : rootOrbitField k L j β) :
    rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit (c • x) =
      (c • rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit x :
        weightSpace (CommGroupScheme.groupHom f ≫ j) a) := by
  apply Subtype.ext
  apply (Lie.baseChangeFixedLieEquiv k L G).injective
  apply Subtype.ext
  rw [rootOrbitFieldWeightSpaceEquiv_baseChange, Submodule.coe_smul,
    Lie.baseChangeFixedLieEquiv_val, LinearMap.map_smulₛₗ (G.lieKernelMapLinear (Algebra.ofId k L)),
    LinearEquiv.map_smul,
    ← Lie.baseChangeFixedLieEquiv_val, rootOrbitFieldWeightSpaceEquiv_baseChange,
    rootOrbitFieldFixedSpanEquiv_val, rootOrbitFieldFixedSpanEquiv_val, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [map_smul, ← algebraMap_smul L c, LinearEquiv.map_smul, Submodule.coe_smul]
  rfl

/-- The actual field coordinates of a relative-weight space, as a linear
equivalence over the base field. -/
def rootOrbitFieldWeightSpaceLinearEquiv
    (f : S ⟶ T) (a : characterLattice S)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (ha : a ≠ 0) (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a) :
    rootOrbitField k L j β ≃ₗ[k] weightSpace (CommGroupScheme.groupHom f ≫ j) a :=
  { rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit with
    map_smul' := rootOrbitFieldWeightSpaceEquiv_smul k L j f a hG hj hS hT ha β horbit }

@[simp]
theorem rootOrbitFieldWeightSpaceLinearEquiv_apply
    (f : S ⟶ T) (a : characterLattice S)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (ha : a ≠ 0) (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (x : rootOrbitField k L j β) :
    rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha β horbit x =
      rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit x := rfl

/-- The same action, stated through the differential of actual conjugation at a
rational point of the torus. -/
theorem conjugation_differential_rootOrbitFieldWeightSpaceEquiv
    (f : S ⟶ T) (a : characterLattice S)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (ha : a ≠ 0) (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (z : rationalPoints T.toGrp) (x : rootOrbitField k L j β) :
    (AutomorphicAction.conjugation j).differential
        (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)
        (rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit x).val =
      (rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit
        (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) * x)).val := by
  rw [AutomorphicAction.differential_conjugation]
  exact adjoint_rootOrbitFieldWeightSpaceEquiv k L j f a hG hj hS hT ha β horbit _ x

end Langlands.GroupScheme
