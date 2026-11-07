import Langlands.GroupScheme.Examples.SU3GroupScheme

/-! # Actual rational points and elementary generation of the special unitary model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root

section Coefficients

variable {A B : Type u} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

/-- An involution-compatible coefficient equivalence identifies the actual fixed SL3 subgroups. -/
def twistFixedRingEquiv (e : A ≃+* B) (he : ∀ a, e (c.bar a) = d.bar (e a)) :
    twistFixedSubgroup c ≃* twistFixedSubgroup d where
  toEquiv := Equiv.subtypeEquiv (SpecialLinear.Root.matrixRingEquiv e).toEquiv (fun g => by
    change unitaryTwist c g = g ↔
      unitaryTwist d (Matrix.SpecialLinearGroup.map e.toRingHom g) =
        Matrix.SpecialLinearGroup.map e.toRingHom g
    rw [unitaryTwist_map e.toRingHom he]
    exact (SpecialLinear.Root.matrixRingEquiv e).injective.eq_iff.symm)
  map_mul' x y := Subtype.ext ((SpecialLinear.Root.matrixRingEquiv e).map_mul x.1 y.1)

/-- Coefficient equivalence on the actual determinant-one Hermitian matrix subgroups. -/
def specialUnitaryRingEquiv (e : A ≃+* B) (he : ∀ a, e (c.bar a) = d.bar (e a)) :
    specialUnitarySubgroup c ≃* specialUnitarySubgroup d :=
  ((fixedSpecialUnitaryEquiv c).symm.trans (twistFixedRingEquiv e he)).trans
    (fixedSpecialUnitaryEquiv d)

/-- The coefficient equivalence acts entry by entry on the actual underlying matrices. -/
theorem specialUnitaryRingEquiv_val (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a)) (g : specialUnitarySubgroup c) :
    ((specialUnitaryRingEquiv e he g).1 : Matrix (Fin 3) (Fin 3) B) =
      (g.1 : Matrix (Fin 3) (Fin 3) A).map e := rfl

end Coefficients

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- The actual test scheme associated to the base coefficient algebra. -/
abbrev baseAffineTest : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))

/-- Recover L from the actual tensor coefficient algebra of the base affine test. -/
def rationalCoefficientEquiv :
    SpecialLinear.WeilRoot.tensorAlgebra k L (baseAffineTest k) ≃ₐ[L] L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of k) k))).trans
      (Algebra.TensorProduct.rid k L L)

/-- Actual base-section evaluation commutes with the original quadratic conjugation. -/
theorem rationalCoefficientEquiv_bar
    (x : SpecialLinear.WeilRoot.tensorAlgebra k L (baseAffineTest k)) :
    rationalCoefficientEquiv k L ((coefficientInvolution k L (baseAffineTest k)).bar x) =
      (fieldInvolution k L).bar (rationalCoefficientEquiv k L x) := by
  let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of k) k))).trans
      (Algebra.TensorProduct.rid k L L)
  change e (QuasiSplitUnitary.scalarConjugation _ (conjugation k L) x) =
    conjugation k L (e x)
  induction x using TensorProduct.inductionOn with
  | tmul a r =>
    change (Corepresented.affineSectionsAlgEquiv
      (CommAlgCat.of (CommRingCat.of k) k) r) • conjugation k L a =
        conjugation k L ((Corepresented.affineSectionsAlgEquiv
          (CommAlgCat.of (CommRingCat.of k) k) r) • a)
    exact (map_smul (conjugation k L) _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Actual rational points of the constructed group scheme are the original SU3 matrices over L. -/
def rationalMatrixEquiv :
    rationalPoints (groupScheme k L) ≃* specialUnitarySubgroup (fieldInvolution k L) :=
  ((GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L)).trans
    (pointsEquiv k L (baseAffineTest k))).trans
      (specialUnitaryRingEquiv (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L))

/-- Rational matrix coordinates are evaluation of the actual ambient tensor matrix. -/
theorem rationalMatrixEquiv_val (x : rationalPoints (groupScheme k L)) :
    ((rationalMatrixEquiv k L x).1 : Matrix (Fin 3) (Fin 3) L) =
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L (baseAffineTest k)
        (GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L) x ≫
          (inclusion k L).hom.hom) : Matrix (Fin 3) (Fin 3)
            (SpecialLinear.WeilRoot.tensorAlgebra k L (baseAffineTest k))).map
              (rationalCoefficientEquiv k L) := by
  unfold rationalMatrixEquiv
  simp only [MulEquiv.trans_apply]
  rw [specialUnitaryRingEquiv_val, pointsEquiv_val]
  rfl

/-- The original upper root matrix, regarded as an actual rational point of the scheme model. -/
def rationalUpper : Parameters (fieldInvolution k L) →* rationalPoints (groupScheme k L) :=
  (rationalMatrixEquiv k L).symm.toMonoidHom.comp
    ((Parameters.embedding (fieldInvolution k L)).codRestrict
      (specialUnitarySubgroup (fieldInvolution k L))
      (embedding_mem_specialUnitarySubgroup (fieldInvolution k L)))

/-- The original opposite root matrix, regarded as an actual rational point of the scheme model. -/
def rationalLower : Parameters (fieldInvolution k L) →* rationalPoints (groupScheme k L) :=
  (rationalMatrixEquiv k L).symm.toMonoidHom.comp
    ((oppositeEmbedding (fieldInvolution k L)).codRestrict
      (specialUnitarySubgroup (fieldInvolution k L))
      (oppositeEmbedding_mem_specialUnitarySubgroup (fieldInvolution k L)))

@[simp] theorem rationalMatrixEquiv_upper (x : Parameters (fieldInvolution k L)) :
    (rationalMatrixEquiv k L (rationalUpper k L x)).1 =
      Parameters.embedding (fieldInvolution k L) x := by
  exact congrArg Subtype.val ((rationalMatrixEquiv k L).apply_symm_apply _)

@[simp] theorem rationalMatrixEquiv_lower (x : Parameters (fieldInvolution k L)) :
    (rationalMatrixEquiv k L (rationalLower k L x)).1 =
      oppositeEmbedding (fieldInvolution k L) x := by
  exact congrArg Subtype.val ((rationalMatrixEquiv k L).apply_symm_apply _)

/-- A subgroup containing all original upper and opposite rational matrices is the whole group. -/
theorem eq_top_of_rational_roots (N : Subgroup (rationalPoints (groupScheme k L)))
    (hupper : (rationalUpper k L).range ≤ N) (hlower : (rationalLower k L).range ≤ N) :
    N = ⊤ := by
  let f := (specialUnitarySubgroup (fieldInvolution k L)).subtype.comp
    (rationalMatrixEquiv k L).toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp
    (rationalMatrixEquiv k L).injective
  have hroot : elementarySubgroup (fieldInvolution k L) ≤ N.map f := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact ⟨rationalUpper k L x, hupper ⟨x, rfl⟩, rationalMatrixEquiv_upper k L x⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨rationalLower k L x, hlower ⟨x, rfl⟩, rationalMatrixEquiv_lower k L x⟩
  apply top_unique
  intro x _
  have hx : f x ∈ elementarySubgroup (fieldInvolution k L) := by
    rw [← specialUnitarySubgroup_eq_elementarySubgroup_quadratic k L]
    exact (rationalMatrixEquiv k L x).2
  obtain ⟨y, hy, hyx⟩ := hroot hx
  exact hf hyx ▸ hy

/-- The upper and opposite root matrices generate the actual rational-point carrier. -/
theorem rational_root_ranges_eq_top :
    (rationalUpper k L).range ⊔ (rationalLower k L).range = ⊤ :=
  eq_top_of_rational_roots k L _ le_sup_left le_sup_right

end SchemeModel
end Langlands.GroupScheme.SU3Root
