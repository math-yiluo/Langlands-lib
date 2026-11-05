import Langlands.GroupScheme.Reductive.CovariantProductInjective
import Langlands.GroupScheme.Reductive.NondegenerateTensorConjugation
import Langlands.GroupScheme.HomogeneousCharacterCoordinates
import Langlands.GroupScheme.Reductive.AffineReynoldsRegular

/-! # Tensor embeddings of coordinates lying in a product of covariant spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineLinearEmbedding MatrixRepresentation

namespace AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance covariantTensorEmbeddingInst1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance covariantTensorEmbeddingInst2 : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

/-- The actual covariant subspace, expressed with the coalgebra of the coordinate Hopf
algebra. -/
theorem leftCovariantSubspace_eq_hopf (i : H ⟶ G) (χ : algebra H) :
    leftCovariantSubspace i χ =
      Chevalley.leftCovariantSubspace (B := hopfAlgebra G)
        (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom.toLinearMap χ := by
  unfold leftCovariantSubspace
  rw [corepresentation_coalgebra_eq G]
  rfl

end AffineCoordinates

namespace Chevalley

section Algebra

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

/-- When multiplication is injective on `X ⊗ Y`, the products of basis vectors form a
basis of the product subspace, indexed by `Fin (a * b)` through `finProdFinEquiv`. -/
theorem exists_basis_mul_of_injective (X Y : Submodule k B) {a b : ℕ}
    (bX : Basis (Fin a) k X) (bY : Basis (Fin b) k Y)
    (hinj : Function.Injective (coordinateProduct X Y)) :
    ∃ bP : Basis (Fin (a * b)) k (X * Y),
      ∀ l : Fin a × Fin b, (bP (finProdFinEquiv l) : B) = (bX l.1 : B) * (bY l.2 : B) := by
  let bT : Basis (Fin a × Fin b) k (X ⊗[k] Y) := bX.tensorProduct bY
  let eP : (X ⊗[k] Y) ≃ₗ[k] ↥(X * Y) :=
    (LinearEquiv.ofInjective (coordinateProduct X Y) hinj).trans
      (LinearEquiv.ofEq _ _ (range_coordinateProduct X Y))
  refine ⟨(bT.map eP).reindex finProdFinEquiv, ?_⟩
  intro l
  rw [Basis.reindex_apply, Equiv.symm_apply_apply, Basis.map_apply]
  change coordinateProduct X Y (bT l) = _
  simp only [bT, Basis.tensorProduct_apply', coordinateProduct_tmul]

/-- The coordinates, in a basis of a larger subspace, of a basis of a smaller subspace form
an injective matrix. -/
theorem coactionCoordinates_mulVecLin_injective [Coalgebra k B] (V P : Submodule k B)
    {d c : ℕ} (bV : Basis (Fin d) k V) (bP : Basis (Fin c) k P) (hVP : V ≤ P) :
    Function.Injective (coactionCoordinates P bP fun j => (bV j : B)).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hmem : ∑ j, x j • (bV j : B) ∈ P :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hVP (bV j).2)
  have hsum : ∑ j, x j • (bV j : B) = 0 := by
    rw [← basis_expand P bP hmem]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hr := congrFun hx r
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, coactionCoordinates,
      Matrix.of_apply, Pi.zero_apply] at hr
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [show ∑ j, x j * extendedCoord P bP r (bV j : B) = 0 by
      rw [← hr]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _, zero_smul]
  have hV0 : ∑ j, x j • bV j = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using hsum
  exact funext (Fintype.linearIndependent_iff.mp bV.linearIndependent x hV0)

end Algebra

section Inclusion

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The coordinates of a regular subspace inside a larger regular subspace give an
actual intertwiner of the two finite regular representations. -/
theorem intertwines_coactionCoordinates (V P : Submodule k B) {d c : ℕ}
    (bV : Basis (Fin d) k V) (bP : Basis (Fin c) k P)
    (hV : letI := (bialgebra e).toCoalgebra
      ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V)
    (hP : letI := (bialgebra e).toCoalgebra
      ∀ (f : Module.Dual k B) (v : B), v ∈ P → rightAct f v ∈ P)
    (hVP : V ≤ P) :
    Intertwines (regularRepresentation e (Field.toIsField k) V bV hV)
      (regularRepresentation e (Field.toIsField k) P bP hP)
      (letI := (bialgebra e).toCoalgebra; coactionCoordinates P bP fun j => (bV j : B)) := by
  let := (bialgebra e).toCoalgebra
  apply intertwines_of_universalMatrix e
  rw [regularRepresentation_universalMatrix, regularRepresentation_universalMatrix]
  exact coactionCoordinates_mul P bP _ _ (fun j => hVP (bV j).2)
    (fun j => comul_basis V bV hV j)

end Inclusion

section Affine

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- On an actual affine group, a regular subspace inside a larger one gives an
actual intertwiner of the finite regular representations. -/
theorem intertwines_affine_coactionCoordinates
    (V P : Submodule k (AffineCoordinates.algebra G)) {d c : ℕ}
    (bV : Basis (Fin d) k V) (bP : Basis (Fin c) k P)
    (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ V → rightAct f v ∈ V)
    (hP : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ P → rightAct f v ∈ P)
    (hVP : V ≤ P) :
    Intertwines (affineRegularRepresentation G V bV hV) (affineRegularRepresentation G P bP hP)
      (letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra;
        coactionCoordinates P bP fun j => (bV j : AffineCoordinates.algebra G)) :=
  Intertwines.restrict (intertwines_coactionCoordinates (AffineCoordinates.corepresentation G)
    V P bV bP hV hP hVP) (AffineCoordinates.groupSchemeIso G).inv

end Affine

section Embedding

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {H H' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] [IsAffineHom H'.X.hom]

local instance covariantTensorEmbeddingInst3 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- If the difference comorphism of two actual subgroup maps is injective, every finite
regular coordinate subspace inside the product of a left `i`-covariant and a left
`i'`-covariant finite regular subspace embeds, by an actual injective intertwiner, into the
tensor product of their finite regular representations. -/
theorem exists_intertwines_tensor_of_le_mul (i : H ⟶ G) (i' : H' ⟶ G)
    (χ : AffineCoordinates.algebra H) (ψ : AffineCoordinates.algebra H')
    (hdense : Function.Injective (differenceComorphism
      (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
      (AffineHomImageHopfAdapter.pullback i').hom.toAlgHom))
    (X Y : Submodule k (AffineCoordinates.algebra G))
    (hXc : X ≤ AffineCoordinates.leftCovariantSubspace i χ)
    (hYc : Y ≤ AffineCoordinates.leftCovariantSubspace i' ψ)
    {a b : ℕ} (bX : Basis (Fin a) k X) (bY : Basis (Fin b) k Y)
    (hX : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ X → rightAct f v ∈ X)
    (hY : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ Y → rightAct f v ∈ Y)
    (V : Submodule k (AffineCoordinates.algebra G)) {d : ℕ} (bV : Basis (Fin d) k V)
    (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ V → rightAct f v ∈ V)
    (hVP : V ≤ X * Y) :
    ∃ C : Matrix (Fin a × Fin b) (Fin d) k,
      Intertwines (affineRegularRepresentation G V bV hV)
        ((affineRegularRepresentation G X bX hX).tensor
          (affineRegularRepresentation G Y bY hY)) C ∧
        Function.Injective C.mulVecLin := by
  classical
  have hinj : Function.Injective (coordinateProduct X Y) :=
    coordinateProduct_injective (A := AffineCoordinates.hopfAlgebra G)
      (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
      (AffineHomImageHopfAdapter.pullback i').hom.toAlgHom χ ψ
      (hXc.trans (AffineCoordinates.leftCovariantSubspace_eq_hopf i χ).le)
      (hYc.trans (AffineCoordinates.leftCovariantSubspace_eq_hopf i' ψ).le) hdense
  obtain ⟨bP, hbP⟩ := exists_basis_mul_of_injective X Y bX bY hinj
  have hP := affine_rightAct_mem_mul G X Y bX bY hX hY
  have hM := intertwines_affine_productMatrix G X Y bX bY bP hX hY hP
  have hMval : productMatrix X Y bX bY bP =
      (1 : Matrix (Fin (a * b)) (Fin (a * b)) k).submatrix id finProdFinEquiv := by
    ext r l
    change extendedCoord (X * Y) bP r ((bX l.1 : AffineCoordinates.algebra G) *
      (bY l.2 : AffineCoordinates.algebra G)) = _
    rw [← hbP l, extendedCoord_basis]
    rfl
  let N : Matrix (Fin a × Fin b) (Fin (a * b)) k :=
    (1 : Matrix (Fin (a * b)) (Fin (a * b)) k).submatrix finProdFinEquiv id
  have hNM : N * productMatrix X Y bX bY bP = 1 := by
    rw [hMval, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one_equiv]
  have hMN : productMatrix X Y bX bY bP * N = 1 := by
    rw [hMval, ← Matrix.submatrix_mul _ _ _ _ _ finProdFinEquiv.bijective, Matrix.mul_one,
      Matrix.submatrix_id_id]
  have hNint := Intertwines.of_mul_eq_one hM hNM hMN
  have hJ := intertwines_affine_coactionCoordinates G V (X * Y) bV bP hV hP hVP
  refine ⟨_, Intertwines.comp hJ hNint, ?_⟩
  have hJinj := (letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra;
    coactionCoordinates_mulVecLin_injective V (X * Y) bV bP hVP)
  have hNinj : Function.Injective N.mulVecLin := by
    intro x y hxy
    have hx := congrArg (productMatrix X Y bX bY bP).mulVecLin hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec] at hx
    exact hx
  rw [Matrix.mulVecLin_mul]
  exact hNinj.comp hJinj

/-- Under `1 ∈ X₁ Y₁`, the products `Xₑ Yₑ` of covariant powers increase with `e`. -/
theorem mul_pow_le_mul_pow_succ (i : H ⟶ G) (i' : H' ⟶ G)
    (χ : AffineCoordinates.algebra H) (ψ : AffineCoordinates.algebra H')
    (hone : (1 : AffineCoordinates.algebra G) ∈ AffineCoordinates.leftCovariantSubspace i χ *
      AffineCoordinates.leftCovariantSubspace i' ψ) (e : ℕ) :
    AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ e) ≤
      AffineCoordinates.leftCovariantSubspace i (χ ^ (e + 1)) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ (e + 1)) := by
  calc AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ e)
      = AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
          AffineCoordinates.leftCovariantSubspace i' (ψ ^ e) * 1 := (mul_one _).symm
    _ ≤ AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
          AffineCoordinates.leftCovariantSubspace i' (ψ ^ e) *
          (AffineCoordinates.leftCovariantSubspace i χ *
            AffineCoordinates.leftCovariantSubspace i' ψ) :=
        mul_le_mul' le_rfl (Submodule.one_le.mpr hone)
    _ = AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
          AffineCoordinates.leftCovariantSubspace i χ *
          (AffineCoordinates.leftCovariantSubspace i' (ψ ^ e) *
            AffineCoordinates.leftCovariantSubspace i' ψ) := mul_mul_mul_comm _ _ _ _
    _ ≤ AffineCoordinates.leftCovariantSubspace i (χ ^ e * χ) *
          AffineCoordinates.leftCovariantSubspace i' (ψ ^ e * ψ) :=
        mul_le_mul'
          (AffineCoordinates.mul_le_leftCovariantSubspace i _ _ le_rfl le_rfl)
          (AffineCoordinates.mul_le_leftCovariantSubspace i' _ _ le_rfl le_rfl)
    _ = _ := by rw [pow_succ, pow_succ]

/-- Under `1 ∈ X₁ Y₁`, the products of covariant powers are monotone in the exponent. -/
theorem mul_pow_le_mul_pow (i : H ⟶ G) (i' : H' ⟶ G)
    (χ : AffineCoordinates.algebra H) (ψ : AffineCoordinates.algebra H')
    (hone : (1 : AffineCoordinates.algebra G) ∈ AffineCoordinates.leftCovariantSubspace i χ *
      AffineCoordinates.leftCovariantSubspace i' ψ) {e e' : ℕ} (h : e ≤ e') :
    AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ e) ≤
      AffineCoordinates.leftCovariantSubspace i (χ ^ e') *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ e') := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (Nat.le_add_right e n)).trans
      (mul_pow_le_mul_pow_succ G i i' χ ψ hone (e + n))

/-- Covariant exhaustion data give tensor embeddings. Suppose the difference comorphism of
`i` and `i'` is injective, `1` lies in `X₁ Y₁`, every left `j`-invariant coordinate lies in
some `Xₑ Yₑ`, and for cofinally many `e` the spaces `Xₑ` and `Yₑ` have equal finite
dimension with `Xₑ` rationally irreducible; here `Xₑ` is the left `i`-covariant subspace of
weight `χ ^ e` and `Yₑ` the left `i'`-covariant subspace of weight `ψ ^ e`. Then every
finite right-stable left `j`-invariant coordinate subspace embeds, by an actual injective
intertwiner, into `σ ⊗ π` with `σ` rationally irreducible and both factors on one
coordinate type. -/
theorem exists_tensor_embedding_of_covariant_exhaustion {Λ : Type u} [AddCommGroup Λ]
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G)
    (i : H ⟶ G) (i' : H' ⟶ G)
    (χ : AffineCoordinates.algebra H) (ψ : AffineCoordinates.algebra H')
    (hdense : Function.Injective (differenceComorphism
      (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
      (AffineHomImageHopfAdapter.pullback i').hom.toAlgHom))
    (hone : (1 : AffineCoordinates.algebra G) ∈ AffineCoordinates.leftCovariantSubspace i χ *
      AffineCoordinates.leftCovariantSubspace i' ψ)
    (hexh : ∀ w : AffineCoordinates.algebra G,
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
        (g : T ⟶ G.X),
        AffineCoordinates.pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w =
          AffineCoordinates.pointAlgebraHom G T g w) →
      ∃ e : ℕ, w ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ e))
    (hst : ∀ e : ℕ, ∃ e' : ℕ, e ≤ e' ∧ ∃ (m : ℕ)
      (bX : Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i (χ ^ e')))
      (_ : Basis (Fin m) k (AffineCoordinates.leftCovariantSubspace i' (ψ ^ e')))
      (hX : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
        ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
          v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e') →
            rightAct f v ∈ AffineCoordinates.leftCovariantSubspace i (χ ^ e')),
      (affineRegularRepresentation G _ bX hX).rationalRepresentation.IsIrreducible)
    (V : Submodule k (AffineCoordinates.algebra G)) {d : ℕ} (bV : Basis (Fin d) k V)
    (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (v : AffineCoordinates.algebra G),
        v ∈ V → rightAct f v ∈ V)
    (hinv : ∀ w ∈ V, ∀ (T : Over (Spec (CommRingCat.of k)))
      (h : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp.X)
      (g : T ⟶ G.X),
      AffineCoordinates.pointAlgebraHom G T ((h ≫ j.hom.hom) * g) w =
        AffineCoordinates.pointAlgebraHom G T g w) :
    ∃ (m : ℕ) (σ π : MatrixRepresentation G (Fin m))
      (C : Matrix (Fin m × Fin m) (Fin d) k),
      σ.rationalRepresentation.IsIrreducible ∧
        Intertwines (affineRegularRepresentation G V bV hV) (σ.tensor π) C ∧
        Function.Injective C.mulVecLin := by
  classical
  choose f hf using fun l : Fin d =>
    hexh (bV l : AffineCoordinates.algebra G) (hinv _ (bV l).2)
  let E := Finset.univ.sup f
  have hbasis : ∀ l, (bV l : AffineCoordinates.algebra G) ∈
      AffineCoordinates.leftCovariantSubspace i (χ ^ E) *
        AffineCoordinates.leftCovariantSubspace i' (ψ ^ E) := fun l =>
    mul_pow_le_mul_pow G i i' χ ψ hone (Finset.le_sup (Finset.mem_univ l)) (hf l)
  have hVE : V ≤ AffineCoordinates.leftCovariantSubspace i (χ ^ E) *
      AffineCoordinates.leftCovariantSubspace i' (ψ ^ E) := by
    intro v hv
    have hsum := congrArg Subtype.val (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hsum]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hbasis l)
  obtain ⟨e', hEe', m, bX, bY, hX, hirr⟩ := hst E
  have hY := AffineCoordinates.rightAct_mem_leftCovariantSubspace (G := G) i' (ψ ^ e')
  obtain ⟨C, hC, hCinj⟩ := exists_intertwines_tensor_of_le_mul G i i' (χ ^ e') (ψ ^ e')
    hdense _ _ le_rfl le_rfl bX bY hX (fun f v hv => hY f hv) V bV hV
    (hVE.trans (mul_pow_le_mul_pow G i i' χ ψ hone hEe'))
  exact ⟨m, _, _, C, hirr, hC, hCinj⟩

end Embedding

end Chevalley

end Langlands.GroupScheme
