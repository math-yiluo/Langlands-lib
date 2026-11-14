import Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero
import Langlands.GroupScheme.Torus.FixedSubgroupSmoothAlgebraBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Nilpotent.Basic

set_option backward.isDefEq.respectTransparency false

/-! # A trace criterion for smoothness of norm-one tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Algebra

section TraceOne

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Some element of `B` has trace one over `A`. -/
def HasTraceOne : Prop := ∃ b : B, Algebra.trace A B b = 1

variable {A B}

/-- An element of trace one exists exactly when the trace map is surjective. -/
theorem hasTraceOne_iff_surjective :
    HasTraceOne A B ↔ Function.Surjective (Algebra.trace A B) := by
  constructor
  · rintro ⟨b, hb⟩ a
    exact ⟨a • b, by rw [map_smul, hb, smul_eq_mul, mul_one]⟩
  · intro h
    exact h 1

/-- If the rank of a finite free algebra is a unit, the inverse rank has trace one. -/
theorem hasTraceOne_of_isUnit_finrank [Nontrivial A] [Module.Free A B] [Module.Finite A B]
    (h : IsUnit (Module.finrank A B : A)) : HasTraceOne A B := by
  refine ⟨algebraMap A B ((h.unit⁻¹ : Aˣ) : A), ?_⟩
  rw [Algebra.trace_algebraMap, nsmul_eq_mul]
  exact h.mul_val_inv

end TraceOne

variable {A B S S' : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']

variable [Module.Free A B] [Module.Finite A B]

/-- First-order norm formula: if `r ^ 2 = 0`, the norm of `1 + b ⊗ r` is
`1 + r Tr(b)`. -/
theorem tensorNorm_one_add_tmul (b : B) {r : S} (hr : r ^ 2 = 0) :
    tensorNorm A B S (1 + b ⊗ₜ r) = 1 + r * algebraMap A S (Algebra.trace A B b) := by
  classical
  let β := Module.Free.chooseBasis A B
  have hcomm : Algebra.TensorProduct.comm A B S (1 + b ⊗ₜ r) =
      1 + r • ((1 : S) ⊗ₜ[A] b) := by
    rw [map_add, map_one, Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  have hmat : Algebra.leftMulMatrix (β.baseChange S) ((1 : S) ⊗ₜ[A] b) =
      (Algebra.leftMulMatrix β b).map (algebraMap A S) := by
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.smul_def]
  change Algebra.norm S (Algebra.TensorProduct.comm A B S (1 + b ⊗ₜ r)) = _
  rw [hcomm, Algebra.norm_eq_matrix_det (β.baseChange S), map_add, map_one, map_smul,
    hmat, Matrix.det_one_add_smul, hr, mul_zero, add_zero,
    Algebra.trace_eq_matrix_trace β, AddMonoidHom.map_trace, mul_comm]

omit [Module.Free A B] [Module.Finite A B] in
/-- If `φ` is surjective with square-zero kernel, then `id_B ⊗ φ` also has
square-zero kernel: any two elements killed by `id_B ⊗ φ` multiply to zero. -/
theorem lTensor_mul_eq_zero (φ : S →ₐ[A] S') (hφ : Function.Surjective φ)
    (hK : RingHom.ker φ ^ 2 = ⊥) {x y : B ⊗[A] S}
    (hx : Algebra.TensorProduct.lTensor (S := B) B φ x = 0)
    (hy : Algebra.TensorProduct.lTensor (S := B) B φ y = 0) : x * y = 0 := by
  have hN : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B) φ) ^ 2 = ⊥ := by
    rw [Algebra.TensorProduct.lTensor_ker φ hφ, ← Ideal.map_pow, hK, Ideal.map_bot]
  exact CommutativeAlgebra.GradedFormallySmooth.mul_eq_zero_of_sq_eq_bot hN _
    (RingHom.mem_ker.mpr hx) _ (RingHom.mem_ker.mpr hy)

/-- **Square-zero lifting of norm-one units.** If some element of `B` has
trace one and `φ : S → S'` is surjective with square-zero kernel, every
norm-one unit of `B ⊗ S'` lifts to a norm-one unit of `B ⊗ S`. -/
theorem exists_tensorNormUnits_lift (hb : HasTraceOne A B)
    (φ : S →ₐ[A] S') (hφ : Function.Surjective φ) (hK : RingHom.ker φ ^ 2 = ⊥)
    (u' : (tensorNormUnits A B S').ker) :
    ∃ u : (tensorNormUnits A B S).ker,
      Units.map (Algebra.TensorProduct.lTensor (S := B) B φ).toMonoidHom u.val = u'.val := by
  classical
  have isUnit_of_sq : ∀ {x : B ⊗[A] S}, (x - 1) * (x - 1) = 0 → IsUnit x := fun {x} hx => by
    simpa using (show IsNilpotent (x - 1) from ⟨2, by rw [pow_two]; exact hx⟩).isUnit_add_one
  obtain ⟨b₀, hb₀⟩ := hb
  let Ψ := Algebra.TensorProduct.lTensor (S := B) B φ
  have hΨs : Function.Surjective Ψ :=
    Algebra.TensorProduct.map_surjective (AlgHom.id B B) φ (fun x => ⟨x, rfl⟩) hφ
  obtain ⟨z₀, hz₀⟩ := hΨs (u'.val : B ⊗[A] S')
  obtain ⟨w₀, hw₀⟩ := hΨs ((u'.val⁻¹ : (B ⊗[A] S')ˣ) : B ⊗[A] S')
  have hn : Ψ (z₀ * w₀ - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hz₀, hw₀, Units.mul_inv, sub_self]
  have hz : IsUnit z₀ := isUnit_of_mul_isUnit_left
    (isUnit_of_sq (lTensor_mul_eq_zero φ hφ hK hn hn))
  have hu' : tensorNorm A B S' (u'.val : B ⊗[A] S') = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.mp u'.property)
    simpa [tensorNormUnits] using h
  set k := tensorNorm A B S z₀ - 1 with hk
  have hkφ : φ k = 0 := by
    have h := tensorNorm_naturality (B := B) φ z₀
    change tensorNorm A B S' (Ψ z₀) = _ at h
    rw [hz₀, hu'] at h
    rw [hk, map_sub, map_one, ← h, sub_self]
  have hkK : k ∈ RingHom.ker φ := RingHom.mem_ker.mpr hkφ
  have hk2 : k ^ 2 = 0 := by
    rw [pow_two]
    exact CommutativeAlgebra.GradedFormallySmooth.mul_eq_zero_of_sq_eq_bot hK _ hkK _ hkK
  set c₀ : B ⊗[A] S := 1 + b₀ ⊗ₜ (-k) with hc₀
  have hc₀N : tensorNorm A B S c₀ = 1 - k := by
    rw [hc₀, tensorNorm_one_add_tmul b₀ (by rw [neg_sq]; exact hk2), hb₀, map_one, mul_one,
      sub_eq_add_neg]
  have hc₀Ψ : Ψ (c₀ - 1) = 0 := by
    simp [Ψ, hc₀, hkφ]
  have hc : IsUnit c₀ := isUnit_of_sq (lTensor_mul_eq_zero φ hφ hK hc₀Ψ hc₀Ψ)
  refine ⟨⟨(hz.mul hc).unit, ?_⟩, ?_⟩
  · apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change tensorNorm A B S (z₀ * c₀) = 1
    have hzN : tensorNorm A B S z₀ = 1 + k := by rw [hk]; ring
    rw [map_mul, hzN, hc₀N]
    linear_combination (-1 : S) * hk2
  · apply Units.ext
    change Ψ (z₀ * c₀) = (u'.val : B ⊗[A] S')
    have hc1 : Ψ c₀ = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at hc₀Ψ
      exact hc₀Ψ
    rw [map_mul, hz₀, hc1, mul_one]

end Langlands.Algebra

namespace Langlands.GroupScheme.WeilGm

variable (A : CommRingCat.{u})

/-- An algebra is identified with the global sections of its spectrum by the
counit of the relative `Γ`–`Spec` adjunction. -/
def specSectionsIso (C : CommAlgCat.{u} A) :
    C ≅ ((algΓ A).obj ((algSpec A).obj (op C))).unop :=
  (asIso ((algΓAlgSpecAdjunction A).counit.app (op C))).unop

/-- The sections identification is natural in the algebra. -/
theorem specSectionsIso_naturality {C D : CommAlgCat.{u} A} (g : C ⟶ D) :
    (specSectionsIso A C).hom ≫ ((algΓ A).map ((algSpec A).map g.op)).unop =
      g ≫ (specSectionsIso A D).hom := by
  have h := congrArg Quiver.Hom.unop ((algΓAlgSpecAdjunction A).counit.naturality g.op)
  exact h

variable (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]

/-- The norm-one kernel is locally of finite type over its base. -/
instance normOne_locallyOfFiniteType : LocallyOfFiniteType (normOne A B).X.hom := by
  have : Smooth (groupScheme A B).X.hom := smooth A B
  have : IsSeparated (Gm (Spec A)).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  have : IsClosedImmersion (kernelι (norm A B)).hom.hom.left := inferInstance
  change LocallyOfFiniteType (kernel (norm A B)).X.hom
  rw [← (kernelι (norm A B)).hom.hom.w]
  infer_instance

/-- **Trace criterion, formal part.** If some element of `B` has trace one, the
coordinate algebra of the norm-one kernel is formally smooth over `A`. -/
theorem normOne_formallySmooth_of_hasTraceOne (hb : Langlands.Algebra.HasTraceOne A B) :
    Algebra.FormallySmooth A (Lie.coordinateAlgebra (normOne A B)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ I hI f => ?_
  let Cc : CommAlgCat.{u} A := CommAlgCat.of A C
  let Dc : CommAlgCat.{u} A := CommAlgCat.of A (C ⧸ I)
  let q : Cc ⟶ Dc := CommAlgCat.ofHom (Ideal.Quotient.mkₐ A I)
  let a := (algSpec A).map q.op
  let x₀ : Lie.AffinePoints (normOne A B) (C ⧸ I) := (Lie.pointCoordinates (normOne A B)).symm f
  let u₀ := normOnePointsEquiv A B ((algSpec A).obj (op Dc)) x₀
  let φ := ((algΓ A).map a).unop.hom
  let eC := specSectionsIso A Cc
  let eD := specSectionsIso A Dc
  have hφ : ∀ c : C, φ (eC.hom.hom c) = eD.hom.hom (Ideal.Quotient.mk I c) := fun c =>
    congrArg (fun g => g.hom c) (specSectionsIso_naturality A q)
  have hCinv : ∀ y, eC.hom.hom (eC.inv.hom y) = y := fun y =>
    congrArg (fun g => g.hom y) eC.inv_hom_id
  have hDinv : ∀ z, eD.inv.hom (eD.hom.hom z) = z := fun z =>
    congrArg (fun g => g.hom z) eD.hom_inv_id
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (eD.inv.hom y)
    refine ⟨eC.hom.hom c, ?_⟩
    rw [hφ, hc]
    exact congrArg (fun g => g.hom y) eD.inv_hom_id
  have hmem : ∀ y, φ y = 0 → eC.inv.hom y ∈ I := by
    intro y hy
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hDinv (Ideal.Quotient.mk I _), ← hφ, hCinv, hy,
      map_zero]
  have hker : RingHom.ker φ ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro y₁ hy₁ y₂ hy₂
    have h := CommutativeAlgebra.GradedFormallySmooth.mul_eq_zero_of_sq_eq_bot hI _
      (hmem y₁ hy₁) _ (hmem y₂ hy₂)
    rw [Ideal.mem_bot, ← hCinv y₁, ← hCinv y₂, ← map_mul, h, map_zero]
  obtain ⟨u₁, hu₁⟩ := Langlands.Algebra.exists_tensorNormUnits_lift hb φ hsurj hker u₀
  let x₁ := (normOnePointsEquiv A B ((algSpec A).obj (op Cc))).symm u₁
  have hx : Lie.affineMap (normOne A B) (Ideal.Quotient.mkₐ A I) x₁ = x₀ := by
    apply (normOnePointsEquiv A B ((algSpec A).obj (op Dc))).injective
    rw [Lie.affineMap_apply]
    change normOnePointsEquiv A B _ (a ≫ x₁) = u₀
    rw [normOnePointsEquiv_naturality]
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply]
    exact hu₁
  refine ⟨Lie.pointCoordinates (normOne A B) x₁, ?_⟩
  have h := Lie.pointCoordinates_naturality (normOne A B) (Ideal.Quotient.mkₐ A I) x₁
  rw [hx] at h
  rw [← h]
  exact (Lie.pointCoordinates (normOne A B)).apply_symm_apply f

/-- **Trace criterion.** Over a noetherian base, the norm-one kernel of a finite
free algebra with an element of trace one is smooth. -/
theorem normOne_smooth_of_hasTraceOne [IsNoetherianRing A]
    (hb : Langlands.Algebra.HasTraceOne A B) : Smooth (normOne A B).X.hom := by
  have := normOne_formallySmooth_of_hasTraceOne A B hb
  have : Algebra.FinitePresentation A (Lie.coordinateAlgebra (normOne A B)) :=
    Algebra.FinitePresentation.of_finiteType.mp (Lie.coordinateAlgebraFiniteType _)
  have : Algebra.Smooth A (Lie.coordinateAlgebra (normOne A B)) := {}
  exact Diagonalizable.FixedSubgroupSmoothAlgebraBridge.smooth_of_coordinateAlgebra_smooth _

end Langlands.GroupScheme.WeilGm
