import Langlands.GroupScheme.Absolute.NormalSolvableTriangularRepresentation
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # Diagonal invariance under ambient conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}

namespace SolvableSubgroupTriangularRepresentation

/-- The actual diagonal homomorphism associated to the triangular embedding. -/
def diagonalHom (Q : SolvableSubgroupTriangularRepresentation i) :
    H ⟶ GeneralLinear.blockLeviScheme (Fin Q.dimension) (CommRingCat.of k)
      (fun j => -(j.val : ℤ)) :=
  Q.triangular ≫ GeneralLinear.blockLimitHom
    (Fin Q.dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ))

/-- The subgroup matrices are upper triangular on every test scheme. -/
theorem isUpperTriangular (Q : SolvableSubgroupTriangularRepresentation i)
    {V : Over (Spec (CommRingCat.of k))} (h : V ⟶ H.X) :
    (Q.ambient.pointMatrix V (h ≫ i.hom.hom) :
      Matrix (Fin Q.dimension) (Fin Q.dimension) Γ(V.left, ⊤)).IsUpperTriangular := by
  let e : Fin Q.dimension → ℤ := fun j => -(j.val : ℤ)
  have hm := ((GeneralLinear.isRepresentedBy_blockParabolic
    (Fin Q.dimension) (CommRingCat.of k) e).pointsEquiv V (h ≫ Q.triangular.hom.hom)).2
  have hfac : Q.triangular.hom.hom ≫
      (GeneralLinear.blockParabolicHom (Fin Q.dimension) (CommRingCat.of k) e).hom.hom =
      i.hom.hom ≫ Q.ambient.hom.hom :=
    congrArg (fun f => f.hom.hom) Q.factorization
  intro l m hlm
  have he : e l < e m := by
    dsimp only [e]
    change m.val < l.val at hlm
    omega
  have hz := (GeneralLinear.mem_blockParabolic e).mp hm l m he
  simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
    Category.assoc, hfac, MatrixRepresentation.pointMatrix_apply] using hz

/-- A smooth connected ambient group acting on its triangularly represented
smooth connected subgroup by ambient conjugation preserves every diagonal
coefficient, on every test scheme. -/
theorem diagonal_conjugation (Q : SolvableSubgroupTriangularRepresentation i)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (a : AutomorphicAction G H)
    (ha : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X),
      a.act g h ≫ i.hom.hom = g * (h ≫ i.hom.hom) * g⁻¹)
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X) (h : V ⟶ H.X)
    (l : Fin Q.dimension) :
    Q.ambient.pointMatrix V (a.act g h ≫ i.hom.hom) l l =
      Q.ambient.pointMatrix V (h ≫ i.hom.hom) l l := by
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨_, _, _, hInt⟩ := smoothConnectedAffineGeometry.2 k G H
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
  let : GeometricallyIntegral (G.X ⊗ H.X).hom := hInt
  let : IsIntegral (G.X ⊗ H.X).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (G.X ⊗ H.X).hom
  let W := G.X ⊗ H.X
  let x : W ⟶ G.X := fst G.X H.X
  let y : W ⟶ H.X := snd G.X H.X
  let τ := Q.ambient.restrict i
  let B : Matrix (Fin Q.dimension) (Fin Q.dimension) Γ(W.left, ⊤) :=
    τ.pointMatrix W y
  let C : Matrix (Fin Q.dimension) (Fin Q.dimension) Γ(W.left, ⊤) :=
    τ.pointMatrix W (a.act x y)
  have hB : B.IsUpperTriangular := Q.isUpperTriangular y
  have hC : C.IsUpperTriangular := Q.isUpperTriangular (a.act x y)
  have hmat : τ.pointMatrix W (a.act x y) =
      Q.ambient.pointMatrix W x * τ.pointMatrix W y *
        (Q.ambient.pointMatrix W x)⁻¹ := by
    simp only [τ, MatrixRepresentation.pointMatrix_restrict, ha, map_mul, map_inv]
  have hchar : C.charpoly = B.charpoly := by
    dsimp only [C, B]
    rw [hmat]
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.charpoly_units_conj (Q.ambient.pointMatrix W x)
      (τ.pointMatrix W y : Matrix (Fin Q.dimension) (Fin Q.dimension) Γ(W.left, ⊤))
  let e : W ⟶ W := lift (1 : W ⟶ G.X) y
  let p : Γ(W.left, ⊤) →+* Γ(W.left, ⊤) := e.left.appTop.hom
  have hpB (j : Fin Q.dimension) : p (B j j) = B j j := by
    have hn := τ.pointMatrix_naturality e y
    have hey : e ≫ y = y := by simp only [e, y, lift_snd]
    rw [hey] at hn
    exact (congrArg (fun M => M j j) hn).symm
  have hpC (j : Fin Q.dimension) : p (C j j) = B j j := by
    have hn := τ.pointMatrix_naturality e (a.act x y)
    have hez : e ≫ a.act x y = y := by
      rw [a.naturality]
      simp only [e, x, y, lift_fst, lift_snd, a.act_one_left]
    rw [hez] at hn
    exact (congrArg (fun M => M j j) hn).symm
  have hdiag := MatrixRepresentation.diagonal_eq_of_charpoly_of_retraction
    B C hB hC hchar p hpB hpC l
  have hpull := congrArg (fun s => (lift g h).left.appTop s) hdiag
  have hnatC := τ.pointMatrix_naturality (lift g h) (a.act x y)
  have hnatB := τ.pointMatrix_naturality (lift g h) y
  have hez : lift g h ≫ a.act x y = a.act g h := by
    rw [a.naturality]
    simp only [x, y, lift_fst, lift_snd]
  have hey : lift g h ≫ y = h := by simp only [y, lift_snd]
  rw [hez] at hnatC
  rw [hey] at hnatB
  calc
    Q.ambient.pointMatrix V (a.act g h ≫ i.hom.hom) l l =
        (lift g h).left.appTop (C l l) := congrArg (fun M => M l l) hnatC
    _ = (lift g h).left.appTop (B l l) := hpull
    _ = Q.ambient.pointMatrix V (h ≫ i.hom.hom) l l :=
      (congrArg (fun M => M l l) hnatB).symm

variable (Q : SolvableSubgroupTriangularRepresentation i)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (a : AutomorphicAction G H)
    (ha : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X),
      a.act g h ≫ i.hom.hom = g * (h ≫ i.hom.hom) * g⁻¹)

include ha

/-- Ambient conjugation fixes the actual diagonal projection on every test scheme. -/
theorem diagonalHom_conjugation
    {V : Over (Spec (CommRingCat.of k))} (g : V ⟶ G.X) (h : V ⟶ H.X) :
    a.act g h ≫ Q.diagonalHom.hom.hom = h ≫ Q.diagonalHom.hom.hom := by
  let e : Fin Q.dimension → ℤ := fun j => -(j.val : ℤ)
  let m := GeneralLinear.blockLeviHom (Fin Q.dimension) (CommRingCat.of k) e
  have : Mono m.hom.hom :=
    (GeneralLinear.isRepresentedBy_blockLevi
      (Fin Q.dimension) (CommRingCat.of k) e).1
  apply (cancel_mono m.hom.hom).mp
  apply (GeneralLinear.pointsEquiv
    (Fin Q.dimension) (CommRingCat.of k) V).injective
  change GeneralLinear.pointsEquiv _ _ V
      (((a.act g h ≫ Q.triangular.hom.hom) ≫
        (GeneralLinear.blockLimitHom _ _ e).hom.hom) ≫ m.hom.hom) =
    GeneralLinear.pointsEquiv _ _ V
      (((h ≫ Q.triangular.hom.hom) ≫
        (GeneralLinear.blockLimitHom _ _ e).hom.hom) ≫ m.hom.hom)
  rw [GeneralLinear.pointsEquiv_blockLimitHom,
    GeneralLinear.pointsEquiv_blockLimitHom]
  apply Matrix.GeneralLinearGroup.ext
  intro l j
  simp only [GeneralLinear.coe_blockLeviProjection,
    GeneralLinear.blockDiagonalPart_apply]
  by_cases he : e l = e j
  · have hlj : l = j := Fin.ext (Int.ofNat_inj.mp (neg_injective he))
    subst j
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hfac : Q.triangular.hom.hom ≫
        (GeneralLinear.blockParabolicHom (Fin Q.dimension)
          (CommRingCat.of k) e).hom.hom = i.hom.hom ≫ Q.ambient.hom.hom :=
      congrArg (fun f => f.hom.hom) Q.factorization
    simpa only [Category.assoc, hfac, MatrixRepresentation.pointMatrix_apply] using
      Q.diagonal_conjugation a ha g h l
  · rw [ite_eq_right he, ite_eq_right he]

/-- The actual universal commutator in the subgroup has trivial diagonal. -/
theorem commutator_diagonalHom :
    (a.act (fst G.X H.X) (snd G.X H.X) * (snd G.X H.X)⁻¹) ≫
      Q.diagonalHom.hom.hom = 1 := by
  rw [MonObj.mul_comp, GrpObj.inv_comp, Q.diagonalHom_conjugation a ha,
    mul_inv_cancel]

/-- The universal ambient commutator factors through the scheme-theoretic
diagonal kernel in the subgroup. -/
def commutatorKernelFactor :
    G.X ⊗ H.X ⟶ (kernel Q.diagonalHom).X :=
  (kernelPointsEquiv Q.diagonalHom (G.X ⊗ H.X)).symm
    ⟨a.act (fst G.X H.X) (snd G.X H.X) * (snd G.X H.X)⁻¹,
      Q.commutator_diagonalHom a ha⟩

theorem commutatorKernelFactor_comp :
    Q.commutatorKernelFactor a ha ≫ (kernelι Q.diagonalHom).hom.hom =
      a.act (fst G.X H.X) (snd G.X H.X) * (snd G.X H.X)⁻¹ :=
  congrArg Subtype.val ((kernelPointsEquiv Q.diagonalHom (G.X ⊗ H.X)).apply_symm_apply
    ⟨_, Q.commutator_diagonalHom a ha⟩)

end SolvableSubgroupTriangularRepresentation

end Langlands.GroupScheme
