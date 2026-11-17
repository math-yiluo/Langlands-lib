import Langlands.GroupScheme.Reductive.FiniteCovariantFamily

/-! # Finite covariant families in translation-stable section spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.InvariantPowerLift

variable {k : Type u} [Field k]
  {J H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The linear combination map of a finite family of actual sections. -/
def familyLinearMap (f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop) :
    (n → k) →ₗ[k] ((algΓ (CommRingCat.of k)).obj J.X).unop where
  toFun v := ∑ j, v j • f j
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

omit [DecidableEq n] in
theorem familyLinearMap_apply (f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (v : n → k) : familyLinearMap f v = ∑ j, v j • f j := rfl

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem coordinateFamily_apply (B : Matrix n m k)
    (f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop) (j : m) :
    coordinateFamily B f j = familyLinearMap f (fun r => B r j) := by
  simp only [coordinateFamily, familyLinearMap_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.map_apply, Algebra.smul_def]
  rfl

omit [DecidableEq n] [DecidableEq m] in
theorem familyLinearMap_coordinateFamily (B : Matrix n m k)
    (f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop) (v : m → k) :
    familyLinearMap (coordinateFamily B f) v = familyLinearMap f (B *ᵥ v) := by
  change (∑ j, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop (v j) *
      (∑ r, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop (B r j) * f r)) =
    ∑ r, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop
      ((B *ᵥ v) r) * f r
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pullback along actual right translation by a rational subgroup point. -/
def rightTranslation (i : H ⟶ J)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    ((algΓ (CommRingCat.of k)).obj J.X).unop →ₐ[k]
      ((algΓ (CommRingCat.of k)).obj J.X).unop :=
  ((algΓ (CommRingCat.of k)).map
    (𝟙 J.X * (CartesianMonoidalCategory.toUnit J.X ≫ h ≫ i.hom.hom))).unop.hom

/-- A covariant family's linear combination transforms by its rational matrix. -/
theorem IsRightCovariantFamily.rightTranslation_familyLinearMap
    {i : H ⟶ J} {ρ : MatrixRepresentation H n}
    {f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop}
    (hf : IsRightCovariantFamily i ρ f)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (v : n → k) :
    rightTranslation i h (familyLinearMap f v) =
      familyLinearMap f ((ρ.rationalMatrix h : Matrix n n k) *ᵥ v) := by
  have he := hf J.X (𝟙 _) (CartesianMonoidalCategory.toUnit J.X ≫ h)
  rw [MatrixRepresentation.pointMatrix_constant] at he
  change (fun j => rightTranslation i h (f j)) =
    ((ρ.rationalMatrix h : Matrix n n k).map (scalarMap J.X))ᵀ *ᵥ f at he
  rw [familyLinearMap_apply, map_sum]
  simp only [map_smul, congrFun he, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply]
  change (∑ j, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop (v j) *
      (∑ r, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop
        (ρ.rationalMatrix h r j) * f r)) =
    ∑ r, algebraMap k ((algΓ (CommRingCat.of k)).obj J.X).unop
      (((ρ.rationalMatrix h : Matrix n n k) *ᵥ v) r) * f r
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  change algebraMap k _ (v j) * (algebraMap k _ (ρ.rationalMatrix h r j) * f r) =
    (algebraMap k _ (ρ.rationalMatrix h r j) * algebraMap k _ (v j)) * f r
  ring

section Stable

variable [IsAlgClosed k] [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]

omit [DecidableEq m] in
/-- Rational translation stability of sections gives all-test stability in
the split inverse-image coordinates of a finite covariant family. -/
theorem IsRightCovariantFamily.isStableCoordinates_comap
    {i : H ⟶ J} {ρ : MatrixRepresentation H n}
    {f : n → ((algΓ (CommRingCat.of k)).obj J.X).unop}
    (hf : IsRightCovariantFamily i ρ f)
    (W : Submodule k ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hW : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ W → rightTranslation i h s ∈ W)
    (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ j, familyLinearMap f (fun r => B r j) ∈ W)
    (hproj : ∀ v, familyLinearMap f v ∈ W → (B * C) *ᵥ v = v) :
    ρ.IsStableCoordinates B C := by
  apply MatrixRepresentation.isStableCoordinates_of_rationalMatrix
  intro h
  have hp (j : m) :
      (B * C) *ᵥ ((ρ.rationalMatrix h : Matrix n n k) *ᵥ (fun r => B r j)) =
        (ρ.rationalMatrix h : Matrix n n k) *ᵥ (fun r => B r j) := by
    apply hproj
    rw [← hf.rightTranslation_familyLinearMap]
    exact hW h _ (hcols j)
  have he : (B * C) * ((ρ.rationalMatrix h : Matrix n n k) * B) =
      (ρ.rationalMatrix h : Matrix n n k) * B := by
    ext r j
    exact congrFun (hp j) r
  simpa only [Matrix.mul_assoc] using he.symm

open AffineCoordinates AffineLinearEmbedding Chevalley MatrixRepresentation

/-- Every section in a rationally translation-stable subspace belongs to a
finite covariant family contained in that subspace, with covariance on all tests. -/
theorem exists_covariantFamily_in_submodule [IsAffine J.X.left]
    (i : H ⟶ J)
    (W : Submodule k ((algΓ (CommRingCat.of k)).obj J.X).unop)
    (hW : ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (s : ((algΓ (CommRingCat.of k)).obj J.X).unop),
      s ∈ W → rightTranslation i h s ∈ W)
    (s : ((algΓ (CommRingCat.of k)).obj J.X).unop) (hs : s ∈ W) :
    ∃ (d : ℕ) (ρ : MatrixRepresentation H (Fin d))
      (f : Fin d → ((algΓ (CommRingCat.of k)).obj J.X).unop) (v : Fin d → k),
      IsRightCovariantFamily i ρ f ∧ (∀ j, f j ∈ W) ∧
        familyLinearMap f v = s := by
  classical
  let := (bialgebra (corepresentation J)).toCoalgebra
  let a := (globalAlgEquiv J).symm s
  let V := regularSpan (K := k) ({a} : Finset (algebra J))
  have ha : a ∈ V := subset_regularSpan _ (Finset.mem_singleton_self a)
  let b := Module.finBasis k V
  have hV : ∀ (ψ : Module.Dual k (algebra J)) (w : algebra J),
      w ∈ V → rightAct ψ w ∈ V := fun ψ _ hw => rightAct_mem_regularSpan _ ψ hw
  let ρ := (affineRegularRepresentation J V b hV).restrict i
  let f := fun j => globalAlgHom J (b j : algebra J)
  have hf : IsRightCovariantFamily i ρ f :=
    isRightCovariantFamily_regularBasis i V b hV
  let v := fun j => b.repr (⟨a, ha⟩ : V) j
  have hv : familyLinearMap f v = s := by
    have hb := congrArg (fun w : V => globalAlgHom J (w : algebra J))
      (b.sum_repr (⟨a, ha⟩ : V))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hb
    change (globalAlgHom J) (∑ j, v j • (b j : algebra J)) =
      globalAlgHom J a at hb
    rw [map_sum] at hb
    simp only [map_smul] at hb
    change familyLinearMap f v = globalAlgHom J a at hb
    exact hb.trans ((globalAlgEquiv J).apply_symm_apply s)
  let U := W.comap (familyLinearMap f)
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates U
  have hstable : ρ.IsStableCoordinates B C :=
    hf.isStableCoordinates_comap W hW B C hcols hproj
  refine ⟨d, ρ.restrictCoordinates B C hCB hstable, coordinateFamily B f,
    C *ᵥ v, hf.restrictCoordinates B C hCB hstable, ?_, ?_⟩
  · intro j
    rw [coordinateFamily_apply]
    exact hcols j
  · rw [familyLinearMap_coordinateFamily, Matrix.mulVec_mulVec,
      hproj v (show v ∈ U by change familyLinearMap f v ∈ W; rwa [hv]), hv]

end Stable

end Langlands.GroupScheme.InvariantPowerLift
