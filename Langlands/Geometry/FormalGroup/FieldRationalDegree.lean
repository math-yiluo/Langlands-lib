import Langlands.Geometry.FormalGroup.FieldScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Langlands.Geometry.FormalGroup.ScalarIsogenyTensorInverse

/-! # Rational degrees from finite kernel ranks over a field -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] {π : O}
variable {k F : Type v} [Field k] [Field F] [Algebra O k] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ} {L : ModuleLaw O k υ}

namespace Hom.IsIsogeny

variable {f : Hom M N} {g : Hom N L}

/-- The degree of an integral field-valued isogeny is the dimension of its kernel algebra. -/
def fieldDegree (hf : f.IsIsogeny) : ℕ :=
  Module.finrank k (Classical.choice hf.2).coordinateAlgebra

/-- The kernel rank on the field spectrum is the dimension of the represented algebra. -/
theorem hasKernelRank_fieldDegree (hf : f.IsIsogeny) : f.HasKernelRank hf.fieldDegree := by
  refine ⟨Classical.choice hf.2, fun p => ?_⟩
  simp only [FiniteKernelModel.rank, fieldDegree, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem fieldDegree_eq_of_rank (hf : f.IsIsogeny) {n : ℕ} (h : f.HasKernelRank n) :
    hf.fieldDegree = n := hf.hasKernelRank_fieldDegree.unique h

/-- The zero point of the kernel makes its field rank positive. -/
theorem fieldDegree_pos (hf : f.IsIsogeny) : 0 < hf.fieldDegree := by
  let K := Classical.choice hf.2
  let j : K.coordinateAlgebra ⟶ CommAlgCat.of k k :=
    K.represents.homEquiv.symm ⟨0, map_zero _⟩
  let : Nontrivial K.coordinateAlgebra := j.hom.toRingHom.domain_nontrivial
  exact Module.finrank_pos

theorem fieldDegree_congr {f' : Hom M N} (h : f = f')
    (hf : f.IsIsogeny) (hf' : f'.IsIsogeny) : hf.fieldDegree = hf'.fieldDegree := by
  subst f'
  rfl

theorem fieldDegree_comp (hg : g.IsIsogeny) (hf : f.IsIsogeny) :
    (hg.comp_of_finiteKernelComposition (finiteKernelCompositionStatement M N L) hf).fieldDegree =
      hf.fieldDegree * hg.fieldDegree :=
  fieldDegree_eq_of_rank _ (hf.hasKernelRank_fieldDegree.comp_of_finiteKernelComposition
    (finiteKernelCompositionStatement M N L) hf.1 hg.hasKernelRank_fieldDegree)

/-- Scalar power kernel ranks agree across an actual isogeny. -/
theorem scalarPower_fieldDegree_eq (hf : f.IsIsogeny)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (n : ℕ) :
    (hM.scalarPower_isIsogeny n).fieldDegree = (hN.scalarPower_isIsogeny n).fieldDegree := by
  have h := fieldDegree_congr (f.comp_scalarHom (π ^ n))
    (hf.comp_of_finiteKernelComposition (finiteKernelCompositionStatement M M N)
      (hM.scalarPower_isIsogeny n))
    ((hN.scalarPower_isIsogeny n).comp_of_finiteKernelComposition
      (finiteKernelCompositionStatement M N N) hf)
  rw [fieldDegree_comp hf (hM.scalarPower_isIsogeny n),
    fieldDegree_comp (hN.scalarPower_isIsogeny n) hf, mul_comm hf.fieldDegree] at h
  exact Nat.eq_of_mul_eq_mul_right hf.fieldDegree_pos h

end Hom.IsIsogeny

namespace IsPiDivisible

theorem scalarPower_fieldDegree_add (hM : M.IsPiDivisible π) (m n : ℕ) :
    (hM.scalarPower_isIsogeny (m + n)).fieldDegree =
      (hM.scalarPower_isIsogeny n).fieldDegree * (hM.scalarPower_isIsogeny m).fieldDegree := by
  rw [← Hom.IsIsogeny.fieldDegree_comp]
  apply Hom.IsIsogeny.fieldDegree_congr
  rw [pow_add, scalarHom_mul]

end IsPiDivisible

namespace RationalHom.ScalarIsogenyPresentation

variable {z : RationalHom F M N} {w : RationalHom F N L}

/-- Divide the actual numerator kernel rank by the actual scalar kernel rank. -/
def degree (P : ScalarIsogenyPresentation π z) (hM : M.IsPiDivisible π) : ℚ :=
  (P.isIsogeny.fieldDegree : ℚ) / (hM.scalarPower_isIsogeny P.exponent).fieldDegree

theorem degree_pos (P : ScalarIsogenyPresentation π z) (hM : M.IsPiDivisible π) :
    0 < P.degree hM :=
  div_pos (by exact_mod_cast P.isIsogeny.fieldDegree_pos)
    (by exact_mod_cast (hM.scalarPower_isIsogeny P.exponent).fieldDegree_pos)

/-- Actual scalar-denominator presentations compose by adding their exponents. -/
def comp (Q : ScalarIsogenyPresentation π w) (P : ScalarIsogenyPresentation π z) :
    ScalarIsogenyPresentation π (RationalHom.comp w z) where
  exponent := Q.exponent + P.exponent
  representative := Q.representative.comp P.representative
  isIsogeny := Q.isIsogeny.comp_of_finiteKernelComposition
    (Hom.finiteKernelCompositionStatement M N L) P.isIsogeny
  represents := by
    rw [pow_add, mul_smul, ← comp_smul, ← smul_comp, Q.represents, P.represents, ← ofHom_comp]

theorem degree_comp (Q : ScalarIsogenyPresentation π w) (P : ScalarIsogenyPresentation π z)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    (Q.comp P).degree hM = P.degree hM * Q.degree hN := by
  simp only [degree, comp]
  rw [Hom.IsIsogeny.fieldDegree_comp Q.isIsogeny P.isIsogeny,
    hM.scalarPower_fieldDegree_add Q.exponent P.exponent,
    P.isIsogeny.scalarPower_fieldDegree_eq hM hN Q.exponent, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_comm]

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The ratio is independent of which uniformizer power clears the denominator. -/
theorem degree_eq (P Q : ScalarIsogenyPresentation π z) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) : P.degree hM = Q.degree hM := by
  have hP := hM.scalarPower_isIsogeny P.exponent
  have hQ := hM.scalarPower_isIsogeny Q.exponent
  have he : P.representative.comp (M.scalarHom (π ^ Q.exponent)) =
      Q.representative.comp (M.scalarHom (π ^ P.exponent)) := by
    apply ofHom_injective_of_piDivisible (F := F) hπ hM
    simp only [ofHom_comp, ofHom_scalarHom, comp_smul, comp_id, map_pow,
      ← P.represents, ← Q.represents, smul_smul, mul_comm]
  have h := Hom.IsIsogeny.fieldDegree_congr he
    (P.isIsogeny.comp_of_finiteKernelComposition (Hom.finiteKernelCompositionStatement M M N) hQ)
    (Q.isIsogeny.comp_of_finiteKernelComposition (Hom.finiteKernelCompositionStatement M M N) hP)
  rw [Hom.IsIsogeny.fieldDegree_comp P.isIsogeny hQ,
    Hom.IsIsogeny.fieldDegree_comp Q.isIsogeny hP] at h
  have hp : (hP.fieldDegree : ℚ) ≠ 0 := by exact_mod_cast hP.fieldDegree_pos.ne'
  have hq : (hQ.fieldDegree : ℚ) ≠ 0 := by exact_mod_cast hQ.fieldDegree_pos.ne'
  change (P.isIsogeny.fieldDegree : ℚ) / hP.fieldDegree = (Q.isIsogeny.fieldDegree : ℚ) / hQ.fieldDegree
  apply (div_eq_div_iff hp hq).2
  exact_mod_cast (mul_comm P.isIsogeny.fieldDegree _).trans (h.trans (mul_comm _ _))

end RationalHom.ScalarIsogenyPresentation

namespace QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The positive rational degree of an actual field-valued tensor quasi-isogeny. -/
def fieldDegree (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) : ℚ :=
  (e.scalarIsogenyPresentation hπ hM hN).degree hM

theorem fieldDegree_eq (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    (P : RationalHom.ScalarIsogenyPresentation π e.hom) :
    e.fieldDegree hπ hM hN = P.degree hM :=
  (e.scalarIsogenyPresentation hπ hM hN).degree_eq P hπ hM

theorem fieldDegree_pos (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) : 0 < e.fieldDegree hπ hM hN :=
  (e.scalarIsogenyPresentation hπ hM hN).degree_pos hM

theorem fieldDegree_trans (e : QuasiIsogeny F M N) (f : QuasiIsogeny F N L)
    (hπ : Irreducible π) (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    (hL : L.IsPiDivisible π) :
    (e.trans f).fieldDegree hπ hM hL = e.fieldDegree hπ hM hN * f.fieldDegree hπ hN hL :=
  ((e.trans f).fieldDegree_eq hπ hM hL ((f.scalarIsogenyPresentation hπ hN hL).comp
    (e.scalarIsogenyPresentation hπ hM hN))).trans
    ((f.scalarIsogenyPresentation hπ hN hL).degree_comp
      (e.scalarIsogenyPresentation hπ hM hN) hM hN)

/-- When its forward tensor is integral, a quasi-isogeny has the degree of that numerator. -/
theorem fieldDegree_ofHom (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {f : Hom M N} (hf : f.IsIsogeny) (he : e.hom = RationalHom.ofHom f) :
    e.fieldDegree hπ hM hN = (hf.fieldDegree : ℚ) := by
  let P : RationalHom.ScalarIsogenyPresentation π e.hom :=
    ⟨0, f, hf, by simpa only [pow_zero, one_smul] using he⟩
  have hd : P.degree hM = (hf.fieldDegree : ℚ) := by
    change (hf.fieldDegree : ℚ) / (hM.scalarPower_isIsogeny 0).fieldDegree = _
    have hs : (M.scalarHom (π ^ 0)).HasKernelRank 1 := by
      rw [pow_zero, scalarHom_one]
      exact (Iso.refl M).hasKernelRank_one
    rw [Hom.IsIsogeny.fieldDegree_eq_of_rank _ hs, Nat.cast_one, div_one]
  exact (e.fieldDegree_eq hπ hM hN P).trans hd

@[simp]
theorem fieldDegree_refl (hπ : Irreducible π) (hM : M.IsPiDivisible π) :
    (QuasiIsogeny.refl M : QuasiIsogeny F M M).fieldDegree hπ hM hM = 1 := by
  rw [fieldDegree_ofHom _ hπ hM hM (Iso.refl M).isIsogeny rfl,
    Hom.IsIsogeny.fieldDegree_eq_of_rank _ (Iso.refl M).hasKernelRank_one, Nat.cast_one]

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
