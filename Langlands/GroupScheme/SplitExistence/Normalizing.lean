import Langlands.GroupScheme.SplitExistence.TorusAut
import Langlands.GroupScheme.SplitExistence.Centralizer
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Points of the Chevalley group normalizing the torus

For a simple root `i`, the `k`-point `n_i = u_i(1) u_{-i}(-1) u_i(1)` of the Chevalley group maps
to the matrix `φ_i([[0, 1], [-1, 0]])` over every test scheme. Conjugation by this matrix sends
`diag(χ(wt c))` to `diag(χ(s_i(wt c)))`, so `n_i` normalizes the torus through the automorphism
of `D(X)` induced by the reflection `s_i`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section Ring

variable {R : Type u} [CommRing R]

/-- The Weyl element over any ring is `x_i(1) x_{-i}(-1) x_i(1)`. -/
theorem φ_sl2Weyl_eq (i : b.support) :
    D.φ i R sl2Weyl = D.x i 1 * D.x (P.reflectionPerm i i) (-1) * D.x i (1 : R) := by
  rw [sl2Weyl_eq, map_mul, map_mul]
  rw [show D.φ i R (sl2Upper 1) = D.x i 1 from Units.ext (D.φ_upper i R 1),
    show D.φ i R (sl2Lower (-1)) = D.x (P.reflectionPerm i i) (-1) from
      Units.ext (D.φ_lower i R (-1))]

/-- Over any ring, the Weyl element conjugates `diag(χ(wt c))` to `diag(χ(s_i(wt c)))`. -/
theorem φ_sl2Weyl_mul_torusHom (i : b.support) (χ : Multiplicative X →* Rˣ) :
    D.φ i R sl2Weyl * D.torusHom χ =
      D.torusHom (χ.comp (AddMonoidHom.toMultiplicative
        (P.reflection i).toAddEquiv.toAddMonoidHom)) * D.φ i R sl2Weyl := by
  apply Units.ext
  ext c d
  simp only [Units.val_mul, coe_torusHom, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ((D.φ i R sl2Weyl : GL (Fin D.n) R) : Matrix (Fin D.n) (Fin D.n) R) c d = 0
  · simp [h]
  · have hw := D.weyl_weight i R c d h
    have hχ : χ.comp (AddMonoidHom.toMultiplicative (P.reflection i).toAddEquiv.toAddMonoidHom)
        (Multiplicative.ofAdd (D.wt c)) = χ (Multiplicative.ofAdd (D.wt d)) := by
      change χ (Multiplicative.ofAdd (P.reflection i (D.wt c))) = _
      rw [hw, RootPairing.reflection_same]
    rw [hχ, mul_comm]

end Ring

variable {k : Type u} [Field k]

/-- The base point of `𝔾ₐ` with coordinate `s`. -/
def gaBase (s : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Gak k).X :=
  (VectorGroup.coordinates (CommRingCat.of k) 1 _).symm (Multiplicative.ofAdd fun _ => s)

theorem gaCoord_gaBase (s : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    gaCoord k _ (gaBase s) = Multiplicative.ofAdd s := by
  simp only [gaCoord, gaBase, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  rfl

namespace ChevGroup

variable {D} (G : D.ChevGroup k)

/-- The `k`-point `n_i = u_i(1) u_{-i}(-1) u_i(1)` of the Chevalley group. -/
def weylPoint (i : b.support) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.H.X :=
  (gaBase 1 ≫ (G.u i).hom.hom) * (gaBase (-1) ≫ (G.u (P.reflectionPerm i i)).hom.hom) *
    (gaBase 1 ≫ (G.u i).hom.hom)

theorem pointsEquiv_weylPoint (i : b.support) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _ (G.weylPoint i ≫ G.i.hom.hom) =
      D.φ i _ sl2Weyl := by
  rw [weylPoint, MonObj.mul_comp, MonObj.mul_comp, map_mul, map_mul, Category.assoc,
    Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, G.u_comp, G.u_comp,
    pointsEquiv_rootToGL, pointsEquiv_rootToGL, gaCoord_gaBase, gaCoord_gaBase, D.φ_sl2Weyl_eq]
  rfl

theorem pointsEquiv_constantPoint_weylPoint (i : b.support) (T : Over (Spec (CommRingCat.of k))) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T
        (G.H.constantPoint (G.weylPoint i) T ≫ G.i.hom.hom) =
      D.φ i Γ(T.left, ⊤) sl2Weyl := by
  rw [constantPoint, Category.assoc, GeneralLinear.pointsEquiv_naturality, pointsEquiv_weylPoint,
    D.φ_sl2Weyl_eq, D.φ_sl2Weyl_eq, map_mul, map_mul, D.x_map, D.x_map, map_one,
    map_neg, map_one]

theorem comp_t_innerIso_comp_i (i : b.support) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    (x ≫ (G.t ≫ (G.H.innerIso (G.weylPoint i)).hom).hom.hom) ≫ G.i.hom.hom =
      (G.H.constantPoint (G.weylPoint i) T ≫ G.i.hom.hom) * (x ≫ (D.torusToGL k).hom.hom) *
        (G.H.constantPoint (G.weylPoint i) T ≫ G.i.hom.hom)⁻¹ := by
  rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc, innerIso_hom_comp, ← Category.assoc,
    G.t_comp, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_comp]

theorem comp_torusEnd_t_comp_i (w : X →+ X) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    (x ≫ (torusEnd k w ≫ G.t).hom.hom) ≫ G.i.hom.hom =
      (x ≫ (torusEnd k w).hom.hom) ≫ (D.torusToGL k).hom.hom := by
  rw [Category.assoc, ← Grp.comp_hom_hom, Category.assoc, G.t_comp, Grp.comp_hom_hom,
    Category.assoc]

/-- **`n_i` normalizes the torus through the reflection `s_i`.** -/
theorem isNormalizingPoint_weylPoint (i : b.support) :
    IsNormalizingPoint G.t (G.weylPoint i) (torusAut k (P.reflection i).toAddEquiv) := by
  have hmono := G.mono_i
  rw [IsNormalizingPoint, groupHom_torusAut_hom]
  apply hom_ext_points
  intro T x
  rw [← cancel_mono G.i.hom.hom, comp_t_innerIso_comp_i, comp_torusEnd_t_comp_i]
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T).injective
  rw [map_mul, map_mul, map_inv, pointsEquiv_constantPoint_weylPoint,
    pointsEquiv_torusToGL, pointsEquiv_torusToGL, torusPointsEquiv_torusEnd,
    D.φ_sl2Weyl_mul_torusHom, mul_inv_cancel_right]

end ChevGroup

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
