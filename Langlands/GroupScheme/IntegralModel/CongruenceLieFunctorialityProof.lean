import Langlands.GroupScheme.IntegralModel.CongruenceLieStatements

/-! # Functoriality of the congruence–Lie homomorphism

For smooth integral models `M` of `G` and `N` of `H` over a local domain `R` and a
model homomorphism `φ : M.Hom N f`, the congruence–Lie homomorphisms of
`M` and `N` (KP Proposition A.5.19(3)) commute with `φ` on congruence
subgroups and with the differential of `f` on the Lie-lattice quotients.

The square-zero reduction kernels part gives `Lie.SquareZero.kernelTargetMap`
(postcomposition with a homomorphism) and its compatibility
`kernelTensorAddEquiv_target` with the ideal–Lie tensor comparison, together
with the analogous compatibility `kernelTensorAddEquiv_conjugation` for
conjugation by a point coming from the base.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 120000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie.SquareZero

section Target

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A)

/-- Postcomposition with a homomorphism maps the reduction kernel modulo `I`
of the source into that of the target. -/
def kernelTargetMap (f : G ⟶ H) : kernel G I →* kernel H I where
  toFun x := ⟨x.val ≫ f.hom.hom, by
    change affineMap H (Ideal.Quotient.mkₐ R I) (x.val ≫ f.hom.hom) = 1
    rw [affineMap_apply, ← Category.assoc]
    change reduction G I x.val ≫ f.hom.hom = 1
    rw [x.property, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem kernelTargetMap_val (f : G ⟶ H) (x : kernel G I) :
    (kernelTargetMap I f x).val = x.val ≫ f.hom.hom := rfl

/-- Evaluation of tangent vectors in ideal elements commutes with postcomposition. -/
theorem kernelTargetMap_tangentPoint (f : G ⟶ H) (hI : I ^ 2 = ⊥) (i : I)
    (X : lieKernel G A) :
    kernelTargetMap I f (tangentPoint G I hI i X) =
      tangentPoint H I hI i (Lie.targetMap f A X) := by
  apply Subtype.ext
  rw [kernelTargetMap_val, tangentPoint_val, tangentPoint_val, lieKernelTarget_val,
    affineMap_apply, affineMap_apply, Category.assoc]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [Smooth G.X.hom] [Smooth H.X.hom]

/-- Under the ideal–Lie tensor comparison, postcomposition with a homomorphism on
square-zero reduction kernels is the ideal tensored with its differential. -/
theorem kernelTensorAddEquiv_target (f : G ⟶ H) (hI : I ^ 2 = ⊥)
    (z : I ⊗[R] Additive (lieKernel G R)) :
    kernelTensorAddEquiv H I hI (Additive.ofMul
        (kernelTargetMap I f ((kernelTensorAddEquiv G I hI).symm z).toMul)) =
      TensorProduct.map LinearMap.id (Lie.targetMapLinear f R) z := by
  induction z using TensorProduct.inductionOn with
  | tmul i X =>
    apply (kernelTensorAddEquiv H I hI).symm.injective
    rw [AddEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      kernelTensorAddEquiv_symm_tmul, kernelTensorAddEquiv_symm_tmul, toMul_ofMul,
      kernelTargetMap_tangentPoint, ← lieKernelMap_target]
    rfl
  | add z w hz hw =>
    rw [map_add, toMul_add, map_mul, ofMul_mul, map_add, hz, hw, map_add]

/-- Under the ideal–Lie tensor comparison, conjugation of square-zero reduction
kernels by a coefficient point coming from the base is the ideal tensored with
the adjoint action of that point. -/
theorem kernelTensorAddEquiv_conjugation (hI : I ^ 2 = ⊥) (c : AffinePoints G R)
    (z : I ⊗[R] Additive (lieKernel G R)) :
    kernelTensorAddEquiv G I hI (Additive.ofMul
        (kernelConjugation G I (affineMap G (Algebra.ofId R A) c)
          ((kernelTensorAddEquiv G I hI).symm z).toMul)) =
      TensorProduct.map LinearMap.id (adjoint G R c) z := by
  induction z using TensorProduct.inductionOn with
  | tmul i X =>
    apply (kernelTensorAddEquiv G I hI).symm.injective
    rw [AddEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      kernelTensorAddEquiv_symm_tmul, kernelTensorAddEquiv_symm_tmul, toMul_ofMul]
    have h := tangentPoint_adjoint G I hI i (affineMap G (Algebra.ofId R A) c)
      (lieKernelMapLinear G (Algebra.ofId R A) X)
    rw [← adjoint_naturality] at h
    exact (congrArg Additive.ofMul h).symm
  | add z w hz hw =>
    rw [map_add, toMul_add, map_mul, ofMul_mul, map_add, hz, hw, map_add]

end Target

end Langlands.GroupScheme.Lie.SquareZero

namespace Langlands.GroupScheme.IntegralModel

section TensorNaturality

variable {R K A B : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {M : IntegralModel R K G} {N : IntegralModel R K H}

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- The ideal–Lie tensor comparisons of two smooth models are compatible with a
map of Lie modules and a linear map of generic Lie algebras that agree under the
Lie maps. -/
theorem congruenceLieTensorEquiv_map (hM : M.IsSmooth) (hN : N.IsSmooth)
    (d : M.LieModule →ₗ[R] N.LieModule) (D : GenericLie R G →ₗ[R] GenericLie R H)
    (hD : ∀ X, N.lieMap (d X) = D (M.lieMap X))
    (hL : M.lieLattice ≤ N.lieLattice.comap D)
    (h𝔪 : (𝔪).map (RingHom.id R) ≤ 𝔪) {n m : ℕ+} (h : n ≤ m)
    (z : congruenceTransitionIdeal R h ⊗[R] M.LieModule) :
    N.congruenceLieTensorEquiv hN h (TensorProduct.map LinearMap.id d z) =
      M.lieLatticeQuotientMap N D hL h𝔪 n m (M.congruenceLieTensorEquiv hM h z) := by
  induction z using TensorProduct.inductionOn with
  | tmul i X =>
    obtain ⟨a, rfl⟩ := congruenceIdealReduction_surjective R h i
    rw [TensorProduct.map_tmul, LinearMap.id_apply, congruenceLieTensorEquiv_tmul,
      congruenceLieTensorEquiv_tmul]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    change (a : R) • N.lieMap (d X) = D ((a : R) • M.lieMap X)
    rw [hD, map_smul]
  | add z w hz hw =>
    rw [LinearMap.map_add, LinearEquiv.map_add, hz, hw, LinearEquiv.map_add, LinearMap.map_add]

end TensorNaturality

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}

/-- The congruence–Lie homomorphism, written through its three factors. -/
theorem congruenceLieHom_apply [IsAffineHom G.X.hom] (hM : M.IsSmooth) {n m : ℕ+}
    (h : n ≤ m) (hm : (m : ℕ) ≤ 2 * (n : ℕ)) (g : M.congruenceSubgroupAt n) :
    haveI : Smooth M.group.X.hom := hM
    M.congruenceLieHom hM h hm g = Multiplicative.ofAdd (M.congruenceLieTensorEquiv hM h
      (Lie.SquareZero.kernelTensorAddEquiv M.group (congruenceTransitionIdeal R h)
        (congruenceTransitionAlgHom_ker_sq R h (by omega))
        (Additive.ofMul (M.congruenceReductionToKernel h g)))) := rfl

/-- A model homomorphism commutes with the reduction of level-`n` points to the
transition kernel. -/
theorem Hom.congruenceReductionToKernel_naturality (φ : M.Hom N f) {n m : ℕ+} (h : n ≤ m)
    (g : M.congruenceSubgroupAt n) :
    N.congruenceReductionToKernel h (φ.congruenceSubgroupMap n g) =
      Lie.SquareZero.kernelTargetMap (congruenceTransitionIdeal R h) φ.hom
        (M.congruenceReductionToKernel h g) := by
  obtain ⟨x, rfl⟩ := (M.congruenceSubgroupEquiv n).surjective g
  have hx : φ.congruenceSubgroupMap n (M.congruenceSubgroupEquiv n x) =
      N.congruenceSubgroupEquiv n
        ⟨rationalPoints.map φ.hom x.val, φ.map_mem_congruenceKernelAt n x.property⟩ :=
    Subtype.ext (φ.integralPointMap_naturality x.val).symm
  apply Subtype.ext
  rw [hx, N.congruenceReductionToKernel_section, Lie.SquareZero.kernelTargetMap_val,
    M.congruenceReductionToKernel_section, φ.reductionAt_naturality]
  exact baseChangeBasePointsEquiv_comp (congruenceBaseMap R m) φ.hom (M.reductionAt m x.val)

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- **KP Proposition A.5.19(3), functoriality.** -/
theorem Hom.congruenceLieHom_naturality (hM : M.IsSmooth) (hN : N.IsSmooth)
    (φ : M.Hom N f) {n m : ℕ+} (h : n ≤ m) (hm : (m : ℕ) ≤ 2 * (n : ℕ)) :
    (N.congruenceLieHom hN h hm).comp (φ.congruenceSubgroupMap n) =
      ((φ.congruenceLieQuotientMap n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm) := by
  have : Smooth M.group.X.hom := hM
  have : Smooth N.group.X.hom := hN
  have hI := congruenceTransitionAlgHom_ker_sq R h (by omega)
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, congruenceLieHom_apply,
    congruenceLieHom_apply, φ.congruenceReductionToKernel_naturality]
  set k := M.congruenceReductionToKernel h g
  obtain ⟨z, hz⟩ := (Lie.SquareZero.kernelTensorAddEquiv M.group
    (congruenceTransitionIdeal R h) hI).symm.surjective (Additive.ofMul k)
  have hk : k = ((Lie.SquareZero.kernelTensorAddEquiv M.group
      (congruenceTransitionIdeal R h) hI).symm z).toMul := by rw [hz]; rfl
  rw [hk, Lie.SquareZero.kernelTensorAddEquiv_target, ofMul_toMul, AddEquiv.apply_symm_apply]
  exact congrArg Multiplicative.ofAdd (congruenceLieTensorEquiv_map hM hN _ _
    (fun X => φ.lieMap_naturality X) (Submodule.map_le_iff_le_comap.mp φ.map_lieLattice_le)
    (by simp) h z)

/-- **KP Proposition A.5.19(3), functoriality.** -/
theorem congruenceLieFunctoriality : CongruenceLieFunctorialityStatement.{u} := by
  intro R K _ _ _ _ _ _ G H _ _ M N hM hN f φ n m h hm
  exact φ.congruenceLieHom_naturality hM hN h hm

end Langlands.GroupScheme.IntegralModel
