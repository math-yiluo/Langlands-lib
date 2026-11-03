import Langlands.GroupScheme.UnitriangularUnipotentStatement
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.UnitriangularUnipotent.Coordinates

/-! # Unipotence of the upper unitriangular group scheme

Milne 2017, Theorem 14.5 (b) ⇒ (c) ⇒ (a), for the upper unitriangular group `U_N`. Its
coordinate ring is a polynomial ring in the entries `x_ij` (`i < j`). Give `x_ij` the weight
`j - i`. For a nonzero `b` in a nonzero right-translation stable subspace `V`, pick a monomial
`m` of maximal weight in `b` and let `φ` be the coefficient of `m`. Right translation by `φ`
sends `b` to the nonzero constant `b.coeff m`, so `1 ∈ V`. The Library criterion
`Unipotent.isUnipotent_of_oneMemStable` then gives unipotence.
-/

noncomputable section

universe u

open CategoryTheory MvPolynomial
open scoped TensorProduct

namespace Langlands.GroupScheme.UnitriangularUnipotent

open AffineLinearEmbedding Unipotent

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- If the points of a corepresented group functor map multiplicatively to matrices, and the
matrix of the point classified by `f` is `M` with `f` applied to its entries, then the entries
of `M` are matrix coefficients: their comultiplication is matrix multiplication. -/
theorem comul_entry_of_pt {n : Type} [Fintype n] [DecidableEq n]
    (ι : ∀ A : CommAlgCat.{u} (CommRingCat.of k), F.obj A → Matrix n n A)
    (hι : ∀ A x y, ι A (x * y) = ι A x * ι A y) (M : Matrix n n B)
    (hM : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (f : B →ₐ[k] A) i j,
      ι A (pt e f) i j = f (M i j))
    (i j : n) : comul e (M i j) = ∑ l, M i l ⊗ₜ[k] M l j := by
  have h := congrArg (fun x => ι (CommAlgCat.of (CommRingCat.of k) (B ⊗[k] B)) x i j)
    (pt_comul e)
  simp only [hι, Matrix.mul_apply, hM] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {N : ℕ}

/-- Polynomial coordinates on a corepresented group functor in which the entries above the
diagonal of the upper unitriangular matrix are matrix coefficients make its coordinate
bialgebra unipotent: every nonzero finite-dimensional right-translation stable subspace
contains `1`. -/
theorem oneMemStable_of_coordinates (θ : MvPolynomial (Pos N) k →ₐ[k] B)
    (χ : B →ₐ[k] MvPolynomial (Pos N) k) (hχθ : ∀ f, χ (θ f) = f) (hθχ : ∀ b, θ (χ b) = b)
    (hU : ∀ i j, comul e (upperTri (fun q => θ (X q)) i j) =
      ∑ l, upperTri (fun q => θ (X q)) i l ⊗ₜ[k] upperTri (fun q => θ (X q)) l j) :
    letI := bialgebra e
    OneMemStable k B := by
  let := bialgebra e
  intro V _ hV hV0
  obtain ⟨b, hbV, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  have hf0 : χ b ≠ 0 := fun h => hb0 (by rw [← hθχ b, h, map_zero])
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (χ b).support (Finsupp.weight posWeight)
    (support_nonempty.2 hf0)
  -- The comultiplication in the polynomial coordinates.
  let κ : MvPolynomial (Pos N) (MvPolynomial (Pos N) k) →+* B ⊗[k] B :=
    eval₂Hom ((Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom.comp θ.toRingHom)
      (fun q => (1 : B) ⊗ₜ[k] θ (X q))
  have hκ : (comul e).toRingHom.comp θ.toRingHom = κ.comp (comulPoly k).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [κ, comulPoly, MvPolynomial.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    · intro p
      have hp : θ (X p) = upperTri (fun q => θ (X q)) p.1.1 p.1.2 :=
        (upperTri_apply_of_lt' (fun q => θ (X q)) p.2).symm
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comulPoly_X]
      rw [hp, hU, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, map_upperTri, map_upperTri]
      simp only [κ, eval₂Hom_C, eval₂Hom_X', RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      have hL : ∀ i l, upperTri (fun q => (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B)
          (θ (X q))) i l = upperTri (fun q => θ (X q)) i l ⊗ₜ[k] (1 : B) := fun i l =>
        (map_upperTri (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom _ i l).symm
      have hR : ∀ l j, upperTri (fun q => (1 : B) ⊗ₜ[k] θ (X q)) l j =
          (1 : B) ⊗ₜ[k] upperTri (fun q => θ (X q)) l j := fun l j =>
        (map_upperTri (Algebra.TensorProduct.includeRight : B →ₐ[k] B ⊗[k] B).toRingHom _ l j).symm
      rw [hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- The coefficient of `m`, as a functional on `B`.
  let φ : Module.Dual k B := (lcoeff k m).comp χ.toLinearMap
  have hφ : ∀ d, φ (θ (monomial d 1)) = if d = m then 1 else 0 := by
    intro d
    simp [φ, hχθ, coeff_monomial]
  have key : rightAct φ b = (χ b).coeff m • (1 : B) := by
    have hb : comul e b = κ (comulPoly k (χ b)) := by
      conv_lhs => rw [← hθχ b]
      exact RingHom.congr_fun hκ (χ b)
    rw [rightAct_apply]
    change TensorProduct.rid k B (LinearMap.lTensor B φ (comul e b)) = _
    rw [hb, rid_lTensor_eval₂Hom k θ φ m hφ,
      coeff_comulPoly_of_weight_le k (χ b) m fun a ha => hmax a ha, algHom_C,
      Algebra.algebraMap_eq_smul_one]
  have hc : (χ b).coeff m ≠ 0 := mem_support_iff.1 hm
  have h1 : (1 : B) = ((χ b).coeff m)⁻¹ • rightAct φ b := by
    rw [key, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h1]
  exact V.smul_mem _ (hV φ b hbV)

/-- Polynomial coordinates as in `oneMemStable_of_coordinates` make a corepresented group
scheme unipotent. -/
theorem isUnipotent_of_coordinates (θ : MvPolynomial (Pos N) k →ₐ[k] B)
    (χ : B →ₐ[k] MvPolynomial (Pos N) k) (hχθ : ∀ f, χ (θ f) = f) (hθχ : ∀ b, θ (χ b) = b)
    (hU : ∀ i j, comul e (upperTri (fun q => θ (X q)) i j) =
      ∑ l, upperTri (fun q => θ (X q)) i l ⊗ₜ[k] upperTri (fun q => θ (X q)) l j) :
    IsUnipotent (Corepresented.groupScheme F e) :=
  isUnipotent_of_oneMemStable e (oneMemStable_of_coordinates e θ χ hχθ hθχ hU)

end Langlands.GroupScheme.UnitriangularUnipotent

namespace Langlands.GroupScheme

open UnitriangularUnipotent

/-- The concrete upper unitriangular group scheme is unipotent over every field, in every
dimension including zero (Milne 2017, Theorem 14.5 (b) ⇒ (a)). -/
theorem unitriangularUnipotent : UnitriangularUnipotentStatement.{u} := by
  intro k _ N
  refine isUnipotent_of_coordinates (corep k N) (theta k N) (chi k N) chi_theta theta_chi
    (comul_entry_of_pt (corep k N) (fun A x => ((show GL (Fin N) A from x.1) : Matrix (Fin N) (Fin N) A))
      (fun A x y => rfl) _ fun A f i j => (pt_apply f i j).trans (congrArg f ?_))
  calc u i j = upperTri (fun q : Pos N => u q.1.1 q.1.2) i j := (upperTri_u i j).symm
    _ = _ := congrArg (fun v => upperTri v i j) (funext fun q => (theta_X q).symm)

end Langlands.GroupScheme
