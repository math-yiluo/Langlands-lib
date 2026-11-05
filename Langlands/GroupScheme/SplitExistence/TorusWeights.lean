import Langlands.GroupScheme.SplitExistence.Characters
import Langlands.GroupScheme.SplitExistence.RootBound

/-! # Torus weight spaces of the Lie algebra

The Library weight space `weightSpace t (charOf ξ)` of the Lie algebra of the Chevalley group
consists exactly of the elements whose matrix is a weight matrix of weight `ξ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {k : Type u} [Field k]

/-- Global-section points of the torus on an affine test scheme come from affine points. -/
theorem torusPointsEquiv_apply_eq_affine (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (Tk (X := X) k).toGrp A) (m : Multiplicative X) :
    ((torusPointsEquiv k ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) t m :
        Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)ˣ) :
        Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))).left, ⊤)) =
      affSecEquiv k (CommAlgCat.of k A) ((torusAffineEquiv A t m : Aˣ) : A) := by
  have h := Corepresented.pointsEquiv_eq_affinePointsEquiv
    (Diagonalizable.functor (CommRingCat.of k) X)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) X) (CommAlgCat.of k A) t
  have h2 := congrArg (fun χ : Multiplicative X →* _ => χ m) h
  exact congrArg Units.val h2

/-- Affine points of the torus map to the diagonal matrices `diag(χ(wt c))`. -/
theorem affinePointsEquiv_torusToGL (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (Tk (X := X) k).toGrp A) :
    GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (CommAlgCat.of k A)
        (t ≫ (D.torusToGL k).hom.hom) = D.torusHom (torusAffineEquiv A t) := by
  apply (glMapEquiv (affSecEquiv k (CommAlgCat.of k A))).injective
  rw [← D.pointsEquiv_eq_glMap k (CommAlgCat.of k A), pointsEquiv_torusToGL]
  ext c d
  rw [coe_torusHom, Matrix.diagonal_apply]
  change _ = affSecEquiv k (CommAlgCat.of k A) (((D.torusHom (torusAffineEquiv A t) :
    GL (Fin D.n) A) : Matrix (Fin D.n) (Fin D.n) A) c d)
  rw [coe_torusHom, Matrix.diagonal_apply]
  split_ifs
  · exact torusPointsEquiv_apply_eq_affine A t _
  · exact (map_zero _).symm

/-- The value of the character `charOf ξ` at an affine point of the torus. -/
theorem characterValue_charOf (A : Type u) [CommRing A] [Algebra k A] (ξ : X)
    (t : Lie.AffinePoints (Tk (X := X) k).toGrp A) :
    Lie.characterValue (charOf k ξ) t = torusAffineEquiv A t (Multiplicative.ofAdd ξ) := by
  apply Units.ext
  simp only [Lie.characterValue, Gm.affinePointsEquiv, MulEquiv.trans_apply]
  erw [gmPoints_charOf]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (Units.val (torusPointsEquiv k _ t (Multiplicative.ofAdd ξ))) = _
  rw [torusPointsEquiv_apply_eq_affine]
  have key : ∀ a : A, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (affSecEquiv k (CommAlgCat.of k A) a) = a := by
    intro a
    have h := congrArg (fun f : _ →+* _ => f a)
      (Corepresented.affineSectionsIso_inv_ringHom (R := CommRingCat.of k) (CommAlgCat.of k A))
    change (Scheme.ΓSpecIso _).hom ((Corepresented.affineSectionsIso (R := CommRingCat.of k)
      (CommAlgCat.of k A)).inv.hom a) = a
    erw [h]
    exact Iso.inv_hom_id_apply _ _
  exact key _

namespace ChevGroup

variable {D} (G : D.ChevGroup k) [IsAffineHom G.H.X.hom]

theorem lieMat_adjoint_torus (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (Tk (X := X) k).toGrp A) (x : Additive (lieKernel G.H A)) :
    G.lieMat A (adjoint G.H A (t ≫ G.t.hom.hom) x) =
      (D.torusHom (torusAffineEquiv A t) : Matrix (Fin D.n) (Fin D.n) A) * G.lieMat A x *
        (((D.torusHom (torusAffineEquiv A t))⁻¹ : GL (Fin D.n) A) :
          Matrix (Fin D.n) (Fin D.n) A) := by
  rw [G.lieMat_adjoint]
  have h : t ≫ G.t.hom.hom ≫ G.i.hom.hom = t ≫ (D.torusToGL k).hom.hom := by
    rw [← Grp.comp_hom_hom, G.t_comp]
  rw [Category.assoc, h, D.affinePointsEquiv_torusToGL]

/-- A weight matrix of weight `ξ` lies in the Library weight space of `charOf ξ`. -/
theorem mem_weightSpace_t {ξ : X} (x : Additive (lieKernel G.H k))
    (hw : D.IsWeightMatrix ξ (G.lieMat k x)) :
    x ∈ weightSpace G.t (charOf k ξ) := by
  intro A _ _ t
  apply G.lieMat_injective A
  rw [G.lieMat_adjoint_torus, LinearMap.map_smul, G.lieMat_map, characterValue_charOf]
  have hA := hw.map (algebraMap k A) (map_zero _)
  convert hA.torusHom_conj (torusAffineEquiv A t) using 2
  all_goals rfl

/-- The universal affine point of the torus has the monomial characters. -/
theorem torusAffineEquiv_id (m : Multiplicative X) :
    ((torusAffineEquiv (AddMonoidAlgebra k X) (𝟙 (Tk (X := X) k).toGrp.X) m :
      (AddMonoidAlgebra k X)ˣ) : AddMonoidAlgebra k X) =
      AddMonoidAlgebra.single (Multiplicative.toAdd m) 1 := by
  have h : torusAffineEquiv (AddMonoidAlgebra k X) (𝟙 (Tk (X := X) k).toGrp.X) =
      (Diagonalizable.corepresentation (CommRingCat.of k) X).homEquiv (𝟙 _) := by
    change (Diagonalizable.corepresentation (CommRingCat.of k) X).homEquiv
      ((algSpec.fullyFaithful.preimage (𝟙 _)).unop) = _
    rw [Functor.FullyFaithful.preimage_id]
    rfl
  rw [h]
  rfl

/-- The weight equation at a single test point, in matrix coordinates. -/
theorem lieMat_weight_eq {ξ : X} (x : Additive (lieKernel G.H k))
    (hx : x ∈ weightSpace G.t (charOf k ξ)) (A : Type u) [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (Tk (X := X) k).toGrp A) :
    (D.torusHom (torusAffineEquiv A t) : Matrix (Fin D.n) (Fin D.n) A) *
        (G.lieMat k x).map (algebraMap k A) *
        (((D.torusHom (torusAffineEquiv A t))⁻¹ : GL (Fin D.n) A) :
          Matrix (Fin D.n) (Fin D.n) A) =
      ((torusAffineEquiv A t (Multiplicative.ofAdd ξ) : Aˣ) : A) •
        (G.lieMat k x).map (algebraMap k A) := by
  have h := congrArg (G.lieMat A) (hx A t)
  rw [G.lieMat_adjoint_torus, LinearMap.map_smul, G.lieMat_map, characterValue_charOf] at h
  exact h

/-- Entries of a matrix conjugated by `diag(χ(wt c))`. -/
theorem torusHom_conj_apply {A : Type u} [CommRing A] (χ : Multiplicative X →* Aˣ)
    (M : Matrix (Fin D.n) (Fin D.n) A) (c d : Fin D.n) :
    ((D.torusHom χ : Matrix (Fin D.n) (Fin D.n) A) * M *
        (((D.torusHom χ)⁻¹ : GL (Fin D.n) A) : Matrix (Fin D.n) (Fin D.n) A)) c d =
      (χ (Multiplicative.ofAdd (D.wt c)) : A) * M c d *
        (χ (Multiplicative.ofAdd (-D.wt d)) : A) := by
  rw [← map_inv, coe_torusHom, coe_torusHom, Matrix.mul_diagonal, Matrix.diagonal_mul,
    MonoidHom.inv_apply, ofAdd_neg, map_inv]

/-- **Elements of the Library weight space of `charOf ξ` have weight matrices of weight `ξ`.** -/
theorem isWeightMatrix_of_mem_weightSpace {ξ : X} (x : Additive (lieKernel G.H k))
    (hx : x ∈ weightSpace G.t (charOf k ξ)) :
    D.IsWeightMatrix ξ (G.lieMat k x) := by
  intro c d hcd
  have h := G.lieMat_weight_eq x hx (AddMonoidAlgebra k X) (𝟙 (Tk (X := X) k).toGrp.X)
  have he := congrFun (congrFun h c) d
  rw [torusHom_conj_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, torusAffineEquiv_id,
    torusAffineEquiv_id, torusAffineEquiv_id] at he
  simp only [toAdd_ofAdd, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
    AddMonoidAlgebra.single_mul_single, one_mul, mul_one, add_zero] at he
  have he' : AddMonoidAlgebra.single (D.wt c - D.wt d) (G.lieMat k x c d) =
      AddMonoidAlgebra.single ξ (G.lieMat k x c d) := by
    rw [sub_eq_add_neg]
    exact he
  exact (AddMonoidAlgebra.single_left_inj hcd).1 he'
end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
