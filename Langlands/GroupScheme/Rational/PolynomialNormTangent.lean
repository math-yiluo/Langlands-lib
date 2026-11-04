import Langlands.GroupScheme.Rational.PolynomialNormInput
import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.GroupScheme.Lie.Functoriality

/-! # Nonzero tangents of scalar-parameter central Galois norms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.PolynomialPoint

variable {k : Type u} [Field k] {n : ℕ}

/-- A coordinate tuple gives an actual tangent point of the standard vector group. -/
def vectorTangent {A : Type u} [CommRing A] [Algebra k A] (v : Fin n → A) :
    lieKernel (VectorGroup.groupScheme (CommRingCat.of k) n) A :=
  ⟨evaluate (𝟙 (VectorGroup.groupScheme (CommRingCat.of k) n).X)
    (fun i => TrivSqZeroExt.inr (v i)), by
    change Lie.reduction _ _ = 1
    simp only [Lie.reduction, evaluate, ← Lie.affineMap_comp, comp_aeval,
      TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_inr]
    exact evaluate_zero _ (isAdditive_hom
      (𝟙 (VectorGroup.groupScheme (CommRingCat.of k) n))) A⟩

/-- The vector tangent has exactly its prescribed pure epsilon coordinates. -/
theorem vectorCoordinates_vectorTangent {A : Type u} [CommRing A] [Algebra k A]
    (v : Fin n → A) :
    vectorCoordinates (vectorTangent (k := k) v).val =
      fun i => TrivSqZeroExt.inr (v i) := by
  exact (congrArg vectorCoordinates (Category.comp_id _)).trans
    (vectorCoordinates_aeval (k := k) (fun i => TrivSqZeroExt.inr (v i)))

/-- The zero group point has zero vector coordinates. -/
@[simp] theorem vectorCoordinates_one {A : Type u} [CommRing A] [Algebra k A] :
    vectorCoordinates (k := k) (n := n)
      (1 : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) = 0 := by
  have h := vectorCoordinates_mul (k := k) (n := n)
    (1 : Lie.AffinePoints (VectorGroup.groupScheme (CommRingCat.of k) n) A) 1
  rw [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- A tuple with a nonzero coordinate gives a nonidentity tangent point. -/
theorem vectorTangent_ne_one {A : Type u} [CommRing A] [Algebra k A]
    (v : Fin n → A) (j : Fin n) (hv : v j ≠ 0) : vectorTangent (k := k) v ≠ 1 := by
  intro h
  have hc := congrFun (congrArg vectorCoordinates (congrArg Subtype.val h)) j
  rw [vectorCoordinates_vectorTangent, Subgroup.coe_one, vectorCoordinates_one] at hc
  exact hv (by simpa using congrArg TrivSqZeroExt.snd hc)

/-- Coefficient change acts coordinatewise on the vector tangent. -/
theorem vectorTangent_map {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (v : Fin n → A) :
    lieKernelMap (VectorGroup.groupScheme (CommRingCat.of k) n) f (vectorTangent v) =
      vectorTangent (fun i => f (v i)) := by
  apply Subtype.ext
  simp only [vectorTangent, lieKernelMap_val, evaluate, ← Lie.affineMap_comp,
    comp_aeval]
  have h : (aeval (fun i => (GeneralLinear.DualNumber.coefficientAlgMap
      (R := CommRingCat.of k) f)
      (TrivSqZeroExt.inr (v i))) :
      MvPolynomial (Fin n) k →ₐ[k] DualNumber B) =
        aeval (fun i => TrivSqZeroExt.inr (f (v i))) := by
    apply congrArg aeval
    funext i
    exact GeneralLinear.DualNumber.coefficientMap_inr f.toRingHom (v i)
  rw [h]

/-- Postcomposing a vector tangent evaluates the polynomial morphism at that tangent. -/
theorem vectorTangent_comp {A : Type u} [CommRing A] [Algebra k A]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (f : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ H) (v : Fin n → A) :
    (Lie.targetMap f A (vectorTangent v)).val =
      evaluate f.hom.hom (fun i => TrivSqZeroExt.inr (v i)) := by
  change (_ ≫ 𝟙 (VectorGroup.groupScheme (CommRingCat.of k) n).X) ≫ f.hom.hom = _
  exact congrArg (fun q => q ≫ f.hom.hom) (Category.comp_id _)

/-- Evaluation of a polynomial point commutes with coefficient maps. -/
theorem affineMap_evaluate {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] {H : GroupScheme (Spec (CommRingCat.of k))}
    (f : A →ₐ[k] B) (p : Lie.AffinePoints H (MvPolynomial (Fin n) k))
    (v : Fin n → A) :
    Lie.affineMap H f (evaluate p v) = evaluate p (fun i => f (v i)) := by
  simp only [evaluate, ← Lie.affineMap_comp, comp_aeval]

variable (k) (L : Type u) [Field L] [Algebra k L]

/-- Evaluate at a base-field vector times epsilon, retaining extension-field constants. -/
def epsilonEvaluation (v : Fin n → k) :
    MvPolynomial (Fin n) L →ₐ[k] DualNumber L :=
  (aeval (fun i => TrivSqZeroExt.inr (algebraMap k L (v i))) :
    MvPolynomial (Fin n) L →ₐ[L] DualNumber L).restrictScalars k

/-- Evaluation on a base-field tangent commutes with coefficient automorphisms. -/
theorem epsilonEvaluation_map (v : Fin n → k) (σ : L ≃ₐ[k] L) :
    (epsilonEvaluation k L v).comp (MvPolynomial.mapAlgHom σ.toAlgHom) =
      (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k)
        σ.toAlgHom).comp (epsilonEvaluation k L v) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    apply TrivSqZeroExt.ext <;>
      simp [epsilonEvaluation, MvPolynomial.mapAlgHom_apply,
        GeneralLinear.DualNumber.coefficientAlgMap,
        GeneralLinear.DualNumber.coefficientMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro i
    apply TrivSqZeroExt.ext <;>
      simp [epsilonEvaluation, MvPolynomial.mapAlgHom_apply,
        GeneralLinear.DualNumber.coefficientAlgMap,
        GeneralLinear.DualNumber.coefficientMap]

/-- Evaluating after polynomial coefficient extension agrees with extending
an actual base-field tangent point. -/
theorem epsilonEvaluation_extend
    (v : Fin n → k) :
    (epsilonEvaluation k L v).comp
        (MvPolynomial.mapAlgHom (Algebra.ofId k L)) =
      (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k)
        (Algebra.ofId k L)).comp
          (aeval (fun i => TrivSqZeroExt.inr (v i))) := by
  apply MvPolynomial.algHom_ext
  intro i
  apply TrivSqZeroExt.ext <;>
    simp [epsilonEvaluation, MvPolynomial.mapAlgHom_apply,
      GeneralLinear.DualNumber.coefficientAlgMap,
      GeneralLinear.DualNumber.coefficientMap, Algebra.smul_def]

variable (G : GroupScheme (Spec (CommRingCat.of k)))
local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- The original extension-field tangent, viewed in the base group's actual kernel. -/
def inputTangent (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (v : Fin n → k) : Additive (lieKernel G L) :=
  Additive.ofMul (Lie.kernelBaseChangeEquiv k L G L
    (Lie.targetMap f L (vectorTangent (k := L) (fun i => algebraMap k L (v i)))))

/-- Evaluating the unscaled input gives the original actual tangent. -/
theorem epsilonEvaluation_centralInput
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (v : Fin n → k) :
    Lie.affineMap G (epsilonEvaluation k L v) (centralInput k L G f hf).val =
      (inputTangent k L G f v).toMul.val := by
  rw [centralInput_val, epsilonEvaluation, ← Lie.affineBaseChangeEquiv_naturality]
  apply congrArg (Lie.affineBaseChangeEquiv k L G (DualNumber L))
  exact (vectorTangent_comp f (fun i => algebraMap k L (v i))).symm

/-- Scalar precomposition of the input scales its actual tangent. -/
theorem epsilonEvaluation_scalarCentralInput
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (v : Fin n → k) (a : L) :
    Lie.affineMap G (epsilonEvaluation k L v) (scalarCentralInput k L G f hf a).val =
      (lieKernelScale G a (inputTangent k L G f v).toMul).val := by
  rw [scalarCentralInput_val, epsilonEvaluation,
    ← Lie.affineBaseChangeEquiv_naturality]
  change _ = Lie.affineMap G
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of k) a)
      (Lie.affineBaseChangeEquiv k L G (DualNumber L) _)
  have hscale :
      GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of k) a =
      (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of L) a).restrictScalars k := rfl
  rw [hscale, ← Lie.affineBaseChangeEquiv_naturality]
  apply congrArg (Lie.affineBaseChangeEquiv k L G (DualNumber L))
  change evaluate (evaluate f.hom.hom (fun i => C a * X i))
    (fun i => TrivSqZeroExt.inr (algebraMap k L (v i))) =
    Lie.affineMap G_L
    (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of L) a)
      (Lie.targetMap f L
        (vectorTangent (k := L) (fun i => algebraMap k L (v i)))).val
  rw [vectorTangent_comp, affineMap_evaluate, evaluate_evaluate]
  have he :
      (fun i : Fin n => aeval (fun j => TrivSqZeroExt.inr (algebraMap k L (v j)))
        (C a * X i)) =
      fun i => (GeneralLinear.DualNumber.epsilonScaleAlg
        (R := CommRingCat.of L) a) (TrivSqZeroExt.inr (algebraMap k L (v i))) := by
    funext i
    apply TrivSqZeroExt.ext <;>
      simp [GeneralLinear.DualNumber.epsilonScaleAlg, TrivSqZeroExt.algebraMap_eq_inl]
  rw [he]

/-- A monomorphic input preserves a nonzero base-field coordinate direction. -/
theorem inputTangent_ne_zero
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) [Mono f.hom.hom]
    (v : Fin n → k) (j : Fin n) (hv : v j ≠ 0) :
    inputTangent k L G f v ≠ 0 := by
  intro h
  have hker : Lie.kernelBaseChangeEquiv k L G L
      (Lie.targetMap f L (vectorTangent (k := L) (fun i => algebraMap k L (v i)))) = 1 :=
    congrArg Additive.toMul h
  have htarget := (Lie.kernelBaseChangeEquiv k L G L).injective
    (hker.trans (map_one _).symm)
  have hvector := (lieKernelHom_injective (A := L) f)
    (htarget.trans (map_one _).symm)
  exact vectorTangent_ne_one (k := L) (fun i => algebraMap k L (v i)) j
    (by simpa only [map_zero] using (algebraMap k L).injective.ne hv) hvector

attribute [local instance] centralAffinePointsCommGroup

variable [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L]

/-- On actual dual-number kernels the differential of the norm is the product
of the coefficient-conjugate scaled input tangents. -/
theorem normOfCentralHom_tangent_product
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (v : Fin n → k) (a : L) :
    lieKernelMap G (Algebra.ofId k L)
        (Lie.targetMap (normOfCentralHom k L G f hf a) k (vectorTangent v)) =
      ∏ σ : L ≃ₐ[k] L,
        lieKernelMap G σ.toAlgHom
          (lieKernelScale G a (inputTangent k L G f v).toMul) := by
  classical
  apply Subtype.ext
  rw [lieKernelMap_val, vectorTangent_comp, evaluate, ← Lie.affineMap_comp,
    ← epsilonEvaluation_extend, Lie.affineMap_comp, normOfCentralHom_extension]
  have he (σ : L ≃ₐ[k] L) :
      Lie.affineMap G (epsilonEvaluation k L v)
          (centralConjugate k G L (Fin n) σ (scalarCentralInput k L G f hf a)).val =
        (lieKernelMap G σ.toAlgHom
          (lieKernelScale G a (inputTangent k L G f v).toMul)).val := by
    change Lie.affineMap G (epsilonEvaluation k L v)
        (Lie.affineMap G (MvPolynomial.mapAlgHom σ.toAlgHom)
          (scalarCentralInput k L G f hf a).val) = _
    rw [← Lie.affineMap_comp, epsilonEvaluation_map, Lie.affineMap_comp,
      epsilonEvaluation_scalarCentralInput, lieKernelMap_val]
  change Lie.affineMap G (epsilonEvaluation k L v)
      (∏ σ : L ≃ₐ[k] L,
        centralConjugate k G L (Fin n) σ (scalarCentralInput k L G f hf a)).val = _
  have hs (s : Finset (L ≃ₐ[k] L)) :
      Lie.affineMap G (epsilonEvaluation k L v)
          (∏ σ ∈ s,
            centralConjugate k G L (Fin n) σ (scalarCentralInput k L G f hf a)).val =
        (∏ σ ∈ s, lieKernelMap G σ.toAlgHom
          (lieKernelScale G a (inputTangent k L G f v).toMul)).val := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert σ s hσ ih =>
      simp only [Finset.prod_insert hσ, Subgroup.coe_mul, map_mul, ih, he]
  exact hs Finset.univ

/-- The norm differential is the scalar-weighted sum of conjugate tangents. -/
theorem normOfCentralHom_tangent_sum
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (v : Fin n → k) (a : L) :
    lieKernelMapLinear G (Algebra.ofId k L)
        (Additive.ofMul
          (Lie.targetMap (normOfCentralHom k L G f hf a) k (vectorTangent v))) =
      ∑ σ : L ≃ₐ[k] L,
        σ a • lieKernelMapLinear G σ.toAlgHom (inputTangent k L G f v) := by
  apply Additive.toMul.injective
  change lieKernelMap G (Algebra.ofId k L)
      (Lie.targetMap (normOfCentralHom k L G f hf a) k (vectorTangent v)) = _
  rw [normOfCentralHom_tangent_product, toMul_sum]
  apply Finset.prod_congr rfl
  intro σ _
  exact lieKernelMap_scale G σ.toAlgHom a (inputTangent k L G f v).toMul

omit [IsAffine G.X.left] [IsGalois k L] in

/-- Independence of field automorphisms prevents every scalar-weighted sum
of a family with a nonzero coefficient from vanishing. -/
theorem exists_galois_smul_sum_ne_zero {M : Type v} [AddCommGroup M] [Module L M]
    (w : (L ≃ₐ[k] L) → M) (σ₀ : L ≃ₐ[k] L) (hw : w σ₀ ≠ 0) :
    ∃ a : L, ∑ σ : L ≃ₐ[k] L, σ a • w σ ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero L hw
  have hsum : ∑ σ : L ≃ₐ[k] L, ℓ (w σ) • (fun a => σ a) = 0 := by
    funext a
    have ha := congrArg ℓ (h a)
    simpa only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, mul_comm] using ha
  exact hℓ ((Fintype.linearIndependent_iff.mp
    (Descent.galoisFunctions_linearIndependent k L)) (fun σ => ℓ (w σ)) hsum σ₀)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The identity coefficient automorphism acts identically on actual Lie kernels. -/
theorem lieKernelMapLinear_galois_one (x : Additive (lieKernel G L)) :
    lieKernelMapLinear G (1 : L ≃ₐ[k] L).toAlgHom x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change Lie.affineMap G
    (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k)
      (1 : L ≃ₐ[k] L).toAlgHom) x.toMul.val = x.toMul.val
  have he : GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k)
      (1 : L ≃ₐ[k] L).toAlgHom = AlgHom.id k (DualNumber L) := by
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext <;> rfl
  rw [he, Lie.affineMap_id]

/-- Some extension-field scalar gives a nonzero actual base-field tangent
whenever the original input tangent is nonzero. -/
theorem exists_normOfCentralHom_tangent_ne_zero
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L)
    (hf : IsCentral f) (v : Fin n → k) (hv : inputTangent k L G f v ≠ 0) :
    ∃ a : L, Additive.ofMul
      (Lie.targetMap (normOfCentralHom k L G f hf a) k (vectorTangent v)) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_galois_smul_sum_ne_zero k L
    (fun σ => lieKernelMapLinear G σ.toAlgHom (inputTangent k L G f v)) 1
    (by simpa only [lieKernelMapLinear_galois_one] using hv)
  refine ⟨a, ?_⟩
  intro h
  rw [← normOfCentralHom_tangent_sum k L G f hf v a, h, map_zero] at ha
  exact ha rfl

/-- A monomorphic central positive-dimensional vector input has a scalar norm
whose actual differential is nonzero on a base-field coordinate direction. -/
theorem exists_normOfCentralHom_coordinate_tangent_ne_zero
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) [Mono f.hom.hom]
    (hf : IsCentral f) (hn : 0 < n) :
    ∃ (a : L) (v : Fin n → k), Additive.ofMul
      (Lie.targetMap (normOfCentralHom k L G f hf a) k (vectorTangent v)) ≠ 0 := by
  classical
  let j : Fin n := ⟨0, hn⟩
  let v : Fin n → k := Pi.single j 1
  obtain ⟨a, ha⟩ := exists_normOfCentralHom_tangent_ne_zero k L G f hf v
    (inputTangent_ne_zero k L G f v j (by simp [v]))
  exact ⟨a, v, ha⟩

local instance standardVectorIsAffineHom :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom := by
  change IsAffineHom (Spec.map
    (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
  infer_instance

/-- Choose an actual central norm with nonzero base-field differential. -/
def nonzeroNormOfCentralHom
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) [Mono f.hom.hom]
    (hf : IsCentral f) (hn : 0 < n) :
    {q : VectorGroup.groupScheme (CommRingCat.of k) n ⟶ G //
      IsCentral q ∧ Lie.targetMapLinear q k ≠ 0} := by
  classical
  let h := exists_normOfCentralHom_coordinate_tangent_ne_zero k L G f hf hn
  let a := Classical.choose h
  refine ⟨normOfCentralHom k L G f hf a, normOfCentralHom_isCentral k L G f hf a, ?_⟩
  obtain ⟨v, hv⟩ := Classical.choose_spec h
  intro hzero
  exact hv (LinearMap.congr_fun hzero (Additive.ofMul (vectorTangent v)))

end Langlands.GroupScheme.PolynomialPoint
