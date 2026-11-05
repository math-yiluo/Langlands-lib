import Langlands.GroupScheme.SplitExistence.TorusWeights

/-! # The roots of the Chevalley group

The roots of the torus `D(X)` in the Chevalley group (Library `roots`: nonzero characters with a
nonzero weight space in the Lie algebra) are exactly the characters `charOf (P.root j)`.

* Each root group `u_j : 𝔾ₐ → G` gives the Lie element `u_j(ε)`, whose matrix is `e_j`, a nonzero
  weight matrix of weight `root j`.
* Conversely a nonzero weight vector of weight `ξ ≠ 0` has a weight matrix of weight `ξ`, so `ξ`
  is a root (module `RootBound`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {k : Type u} [Field k]

/-- The affine points of the additive group. -/
def gaAffineEquiv (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints (Gak k) A ≃* Multiplicative (Fin 1 → A) :=
  Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of k) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of k) 1) (CommAlgCat.of k A)

theorem gaCoord_eq_affine (A : Type u) [CommRing A] [Algebra k A]
    (p : Lie.AffinePoints (Gak k) A) :
    Multiplicative.toAdd (gaCoord k _ p) =
      affSecEquiv k (CommAlgCat.of k A) ((gaAffineEquiv A p).toAdd 0) := by
  have h := Corepresented.pointsEquiv_eq_affinePointsEquiv
    (VectorGroup.functor (CommRingCat.of k) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of k) 1) (CommAlgCat.of k A) p
  exact congrArg (fun z : Multiplicative (Fin 1 → _) => z.toAdd 0) h

/-- Affine points of `𝔾ₐ` map to the root exponentials `x_j(s)`. -/
theorem affinePointsEquiv_rootToGL (A : Type u) [CommRing A] [Algebra k A] (j : J)
    (p : Lie.AffinePoints (Gak k) A) :
    GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (CommAlgCat.of k A)
        (p ≫ (D.rootToGL k j).hom.hom) = D.x j ((gaAffineEquiv A p).toAdd 0) := by
  apply (glMapEquiv (affSecEquiv k (CommAlgCat.of k A))).injective
  rw [← D.pointsEquiv_eq_glMap k (CommAlgCat.of k A), pointsEquiv_rootToGL, gaCoord_eq_affine]
  exact (D.x_map (affSecEquiv k (CommAlgCat.of k A)).toRingHom j _).symm

/-- The dual-number point `ε` of `𝔾ₐ`. -/
def epsPoint : Lie.AffinePoints (Gak k) (DualNumber k) :=
  (gaAffineEquiv (DualNumber k)).symm (Multiplicative.ofAdd fun _ => TrivSqZeroExt.inr 1)

theorem epsPoint_mem : epsPoint (k := k) ∈ lieKernel (Gak k) k := by
  change Lie.reduction (Gak k) (epsPoint (k := k)) = 1
  apply (gaAffineEquiv k).injective
  have h := Corepresented.affinePointsEquiv_naturality (VectorGroup.functor (CommRingCat.of k) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of k) 1)
    (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k) :
      CommAlgCat.of k (DualNumber k) ⟶ CommAlgCat.of k k) (epsPoint (k := k))
  change gaAffineEquiv k ((algSpec (CommRingCat.of k)).map _ ≫ epsPoint) = _
  rw [map_one]
  refine h.trans ?_
  apply Multiplicative.toAdd.injective
  funext i
  change TrivSqZeroExt.fst ((gaAffineEquiv (DualNumber k) (epsPoint (k := k))).toAdd i) = 0
  rw [epsPoint, MulEquiv.apply_symm_apply]
  rfl

namespace ChevGroup

variable {D} (G : D.ChevGroup k) [IsAffineHom G.H.X.hom]

/-- The Lie element `u_j(ε)` of the root group `j`. -/
def rootLie (j : J) : Additive (lieKernel G.H k) :=
  Additive.ofMul ⟨epsPoint ≫ (G.u j).hom.hom, by
    change Lie.reduction G.H (epsPoint ≫ (G.u j).hom.hom) = 1
    change (_ ≫ epsPoint) ≫ (G.u j).hom.hom = 1
    have h := epsPoint_mem (k := k)
    change (_ ≫ epsPoint) = 1 at h
    rw [h, MonObj.one_comp]⟩

theorem lieMat_rootLie (j : J) : G.lieMat k (G.rootLie j) = D.eF (F := k) j := by
  rw [lieMat_apply]
  change GeneralLinear.DualNumber.coefficients (GeneralLinear.affinePointsEquiv _ _ _
    (epsPoint ≫ (G.u j).hom.hom ≫ G.i.hom.hom)) = _
  rw [← Grp.comp_hom_hom, G.u_comp, D.affinePointsEquiv_rootToGL, epsPoint,
    MulEquiv.apply_symm_apply]
  ext c d
  change TrivSqZeroExt.snd (((D.x j (TrivSqZeroExt.inr 1) : GL (Fin D.n) (DualNumber k)) :
    Matrix (Fin D.n) (Fin D.n) (DualNumber k)) c d) = _
  rw [coe_x, ← xm, D.xm_inr, one_smul]
  by_cases hcd : c = d
  · subst hcd
    simp
  · simp [Matrix.one_apply_ne hcd]

theorem isWeightMatrix_eF (j : J) : D.IsWeightMatrix (P.root j) (D.eF (F := k) j) := by
  intro c d h
  have hne : D.e j 1 c d ≠ 0 := by
    intro h0
    apply h
    simp [eF, h0]
  have hwt := D.e_weight j 1 c d hne
  rw [one_smul] at hwt
  rw [hwt]
  abel

/-- **The roots of the Chevalley group are the characters of the roots of `P`.** -/
theorem roots_t [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]
    [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] :
    roots G.t = Set.range fun j => charOf k (P.root j) := by
  ext χ
  constructor
  · rintro ⟨hχ0, hχ⟩
    obtain ⟨ξ, rfl⟩ := (charEquiv k (X := X)).surjective χ
    rw [charEquiv_apply] at hχ hχ0 ⊢
    have hξ : ξ ≠ 0 := by
      rintro rfl
      apply hχ0
      rw [← charEquiv_apply, map_zero]
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    have hw := G.isWeightMatrix_of_mem_weightSpace x hx
    obtain ⟨j, hj⟩ := G.exists_root_of_isWeightMatrix x hx0 hξ hw
    exact ⟨j, congrArg (charOf k) hj⟩
  · rintro ⟨j, rfl⟩
    refine ⟨?_, ?_⟩
    · intro h0
      apply P.ne_zero j
      apply (charEquiv k (X := X)).injective
      rw [charEquiv_apply, map_zero]
      exact h0
    · rw [Submodule.ne_bot_iff]
      refine ⟨G.rootLie j, G.mem_weightSpace_t _ ?_, ?_⟩
      · rw [G.lieMat_rootLie]
        exact isWeightMatrix_eF j
      · intro h0
        apply D.e_one_map_ne_zero_field (K := k) j
        have := G.lieMat_rootLie j
        rw [h0, map_zero] at this
        exact this.symm

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
