import Langlands.GroupScheme.Examples.HermitianMatrixGroupScheme
import Langlands.GroupScheme.Examples.HermitianMatrixSplitting
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleAlgebra
import Langlands.GroupScheme.Descent.LocalGaloisInvariant
import Langlands.GroupScheme.Torus.Split

/-!
# Descending a Hermitian Galois cocycle to a special unitary group

Let `M/K` be a Galois extension containing a separable quadratic extension `L/K`, and let
`E` be a local isomorphism from `SL_(n+1)` to an affine group `G` over the cover
`Spec M → Spec K`. Suppose that the Galois discrepancies of `E` are trivial for
automorphisms fixing `L` and are `g ↦ X (g⁻¹)ᵀ X⁻¹` for the others, with `X` the image of
`H⁻¹` for a nonsingular Hermitian matrix `H` over `L`. Then `G` is isomorphic to the
special unitary group scheme of `H`, and the isomorphism is the composite of `E` with the
splitting of the special unitary group over every cover point.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.OuterTypeAHermitian

open SpecialLinearTitsCocycle SU3Root HermitianMatrix

section Coefficients

variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- The coefficient map of a cover point is a `K`-algebra map into the relative global
sections. -/
theorem coefficients_algebraMap {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (k : K) :
    coefficients a (algebraMap K M k) =
      algebraMap K (SpecialLinear.WeilRoot.sectionAlgebra K Z) k := by
  change ((Scheme.ΓSpecIso _).inv ≫ a.left.appTop) (algebraMap K M k) =
    ((Scheme.ΓSpecIso _).inv ≫ Z.hom.appTop) k
  rw [← Over.w a, Scheme.Hom.comp_appTop, ← Category.assoc]
  change _ = ((((Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap K M))).appTop) ≫ a.left.appTop) k)
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable (L : Type u) [Field L] [Algebra K L] [Algebra L M] [IsScalarTower K L M]

/-- The `K`-algebra map `L → Γ(Z)` attached to a cover point `a : Z ⟶ Spec M`. -/
def fieldPoint {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    L →ₐ[K] SpecialLinear.WeilRoot.sectionAlgebra K Z where
  toRingHom := (coefficients a).comp (algebraMap L M)
  commutes' k := by
    change coefficients a (algebraMap L M (algebraMap K L k)) = _
    rw [← IsScalarTower.algebraMap_apply, coefficients_algebraMap]

@[simp] theorem fieldPoint_apply {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (l : L) : fieldPoint L a l = coefficients a (algebraMap L M l) := rfl

theorem fieldPoint_naturality {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z)
    (a : Z ⟶ cover K M) (l : L) :
    fieldPoint L (t ≫ a) l = t.left.appTop.hom (fieldPoint L a l) := by
  rw [fieldPoint_apply, coefficients_naturality]
  rfl

theorem fieldPoint_coverAut {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (σ : M ≃ₐ[K] M) (l : L) :
    fieldPoint L (a ≫ coverAut K M σ) l = coefficients a (σ (algebraMap L M l)) := by
  rw [fieldPoint_apply, coefficients_coverAut]
  rfl

end Coefficients

section Coordinates

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- The coordinate `ℓ ⊗ r ↦ φ_a(ℓ) r` of the tensor coefficients at a cover point. -/
def firstCoord {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    SpecialLinear.WeilRoot.tensorAlgebra K L Z →+* Γ(Z.left, ⊤) :=
  (tensorProj K L (fieldPoint L a)).toRingHom

/-- The conjugate coordinate `ℓ ⊗ r ↦ φ_a(c ℓ) r` at a cover point. -/
def secondCoord {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    SpecialLinear.WeilRoot.tensorAlgebra K L Z →+* Γ(Z.left, ⊤) :=
  (tensorProj K L ((fieldPoint L a).comp (conjugation K L).toAlgHom)).toRingHom

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
theorem firstCoord_tmul {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (l : L)
    (r : SpecialLinear.WeilRoot.sectionAlgebra K Z) :
    firstCoord L a (l ⊗ₜ[K] r) = fieldPoint L a l * r :=
  tensorProj_tmul K L _ l r

theorem secondCoord_eq {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (x : SpecialLinear.WeilRoot.tensorAlgebra K L Z) :
    secondCoord L a x =
      firstCoord L a ((SU3Root.SchemeModel.coefficientInvolution K L Z).bar x) :=
  tensorProj_scalarConjugation K L (fieldPoint L a) x

theorem coord_injective {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (x y : SpecialLinear.WeilRoot.tensorAlgebra K L Z)
    (h₁ : firstCoord L a x = firstCoord L a y) (h₂ : secondCoord L a x = secondCoord L a y) :
    x = y :=
  tensorProj_injective₂ K L (fieldPoint L a) x y h₁ h₂

theorem coord_surjective {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (r s : Γ(Z.left, ⊤)) :
    ∃ x : SpecialLinear.WeilRoot.tensorAlgebra K L Z,
      firstCoord L a x = r ∧ secondCoord L a x = s :=
  tensorProj_surjective₂ K L (fieldPoint L a) r s

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- The first coordinate of a scalar from `L` is its coefficient. -/
theorem firstCoord_algebraMap {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (l : L) :
    firstCoord L a (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L Z) l) =
      coefficients a (algebraMap L M l) := by
  have h := tensorProj_tmul K L (fieldPoint L a) l 1
  rw [mul_one] at h
  exact h

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- The coordinates are natural in the test scheme. -/
theorem firstCoord_tensorMap {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z)
    (a : Z ⟶ cover K M) (x : SpecialLinear.WeilRoot.tensorAlgebra K L Z) :
    firstCoord L (t ≫ a) (SpecialLinear.WeilRoot.tensorMap K L t x) =
      t.left.appTop.hom (firstCoord L a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l r =>
    have h1 := tensorProj_tmul K L (fieldPoint L (t ≫ a)) l (t.left.appTop.hom r)
    have h2 := tensorProj_tmul K L (fieldPoint L a) l r
    rw [fieldPoint_naturality] at h1
    exact h1.trans ((map_mul t.left.appTop.hom _ _).symm.trans
      (congrArg t.left.appTop.hom h2.symm))
  | add x y hx hy =>
    erw [map_add (SpecialLinear.WeilRoot.tensorMap K L t), map_add (firstCoord L (t ≫ a)),
      map_add (firstCoord L a), map_add t.left.appTop.hom, hx, hy]

omit [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] in
/-- At a Galois translate of a cover point fixing `L`, the coordinates are unchanged. -/
theorem firstCoord_coverAut_of_fixes {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K M) (σ : M ≃ₐ[K] M) (hσ : ∀ y : L, σ (algebraMap L M y) = algebraMap L M y)
    (x : SpecialLinear.WeilRoot.tensorAlgebra K L Z) :
    firstCoord L (a ≫ coverAut K M σ) x = firstCoord L a x := by
  have h : fieldPoint L (a ≫ coverAut K M σ) = fieldPoint L a := by
    ext l
    rw [fieldPoint_coverAut, hσ, fieldPoint_apply]
  simp only [firstCoord, h]

/-- An automorphism of `M` moving `L` restricts to the conjugation of `L`. -/
theorem restrict_conjugation (σ : M ≃ₐ[K] M)
    (hσ : ∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y) (l : L) :
    σ (algebraMap L M l) = algebraMap L M (conjugation K L l) := by
  have hne : σ.restrictNormal L ≠ 1 := by
    intro h
    obtain ⟨y, hy⟩ := hσ
    apply hy
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h]
    rfl
  rw [← AlgEquiv.restrictNormal_commutes σ L l, conjugation_unique K L _ hne]

/-- At a Galois translate of a cover point moving `L`, the two coordinates are exchanged. -/
theorem firstCoord_coverAut_of_moves {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K M) (σ : M ≃ₐ[K] M) (hσ : ∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y)
    (x : SpecialLinear.WeilRoot.tensorAlgebra K L Z) :
    firstCoord L (a ≫ coverAut K M σ) x = secondCoord L a x := by
  have h : fieldPoint L (a ≫ coverAut K M σ) =
      (fieldPoint L a).comp (conjugation K L).toAlgHom := by
    ext l
    rw [fieldPoint_coverAut, restrict_conjugation L σ hσ, AlgHom.comp_apply, fieldPoint_apply]
    rfl
  simp only [firstCoord, secondCoord, h]

end Coordinates

section Local

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {n : ℕ} (H : Form (fieldInvolution K L) (Fin (n + 1)))

/-- The splitting of the determinant-one isometries of `H` at a cover point. -/
def splitAt {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    SchemeModel.tensorPoints K L H Z ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) :=
  splitEquiv (SchemeModel.tensorForm K L H Z) (firstCoord L a) (secondCoord L a)
    (secondCoord_eq L a) (coord_injective L a) (coord_surjective L a)

theorem coe_splitAt {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (x : SchemeModel.tensorPoints K L H Z) :
    ((splitAt L H a x : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      (x.1 : Matrix (Fin (n + 1)) (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L Z)).map (firstCoord L a) := rfl

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- The local isomorphism from `SU(H)` to `G` at a cover point: split, then apply `E`. -/
def localEquiv {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    (Z ⟶ (GroupModel.groupScheme K L H).X) ≃* (Z ⟶ G.X) :=
  (GroupModel.pointsEquiv K L H Z).trans ((splitAt L H a).trans
    ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm.trans (E.toFun a)))

theorem localEquiv_apply {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (y : Z ⟶ (GroupModel.groupScheme K L H).X) :
    localEquiv L H E a y = E.toFun a
      ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm
        (splitAt L H a (GroupModel.pointsEquiv K L H Z y))) := rfl

/-- The local isomorphisms are natural in the test scheme. -/
theorem localEquiv_naturality {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z)
    (a : Z ⟶ cover K M) (y : Z ⟶ (GroupModel.groupScheme K L H).X) :
    localEquiv L H E (t ≫ a) (t ≫ y) = t ≫ localEquiv L H E a y := by
  rw [localEquiv_apply, localEquiv_apply, ← E.naturality]
  congr 1
  apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).injective
  rw [MulEquiv.apply_symm_apply, SpecialLinear.pointsEquiv_naturality,
    MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_splitAt, GroupModel.pointsEquiv_naturality, Matrix.map_map]
  change _ = ((splitAt L H a (GroupModel.pointsEquiv K L H Z y) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).map t.left.appTop.hom
  rw [coe_splitAt, Matrix.map_map]
  congr 1
  funext x
  exact firstCoord_tensorMap L t a x

/-- A discrepancy identity converts the local isomorphism at a Galois translate into the
local isomorphism at the original cover point. -/
theorem toFun_coverAut_of_discrepancy (σ : M ≃ₐ[K] M) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K M) (g h : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤))
    (hd : discrepancy E σ a g = h) :
    E.toFun (a ≫ coverAut K M σ)
        ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g) =
      E.toFun a ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm h) := by
  rw [← hd, discrepancy, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

/-- Automorphisms of `M` fixing `L` pointwise have trivial discrepancy on every test. -/
def InnerTrivial : Prop :=
  ∀ σ : M ≃ₐ[K] M, (∀ y : L, σ (algebraMap L M y) = algebraMap L M y) →
    ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
      (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)), discrepancy E σ a g = g

/-- Automorphisms of `M` moving `L` have discrepancy `g ↦ X (g⁻¹)ᵀ X⁻¹`, where `X` is the
coefficient image of `H⁻¹`. -/
def OuterHermitian : Prop :=
  ∀ σ : M ≃ₐ[K] M, (∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y) →
    ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K M)
      (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
      (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
        (Matrix.GeneralLinearGroup.map (coefficients a)
            (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
          (Matrix.GeneralLinearGroup.map (coefficients a)
            (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹)⁻¹ :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))

/-- The coefficient image of `H⁻¹` is the first coordinate of the inverse extended Gram
matrix. -/
theorem coefficients_gram_inv {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    (Matrix.GeneralLinearGroup.map (coefficients a)
        (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      (((SchemeModel.tensorForm K L H Z).gram⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1))
        (SpecialLinear.WeilRoot.tensorAlgebra K L Z)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L Z)).map
        (firstCoord L a) := by
  ext i j
  change coefficients a (algebraMap L M ((H.gram⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) L)
    i j)) = firstCoord L a (((Matrix.GeneralLinearGroup.map
      (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L Z)) H.gram)⁻¹ :
        Matrix.GeneralLinearGroup (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L Z))
      i j)
  rw [← map_inv, Matrix.GeneralLinearGroup.map_apply, firstCoord_algebraMap]

/-- The coefficient image of `H` is the first coordinate of the extended Gram matrix. -/
theorem coefficients_gram {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) :
    (Matrix.GeneralLinearGroup.map (coefficients a)
        (Matrix.GeneralLinearGroup.map (algebraMap L M) H.gram⁻¹)⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      ((SchemeModel.tensorForm K L H Z).gram :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L Z)).map
        (firstCoord L a) := by
  ext i j
  change coefficients a (algebraMap L M (((H.gram⁻¹)⁻¹ :
      Matrix.GeneralLinearGroup (Fin (n + 1)) L) i j)) =
    firstCoord L a ((Matrix.GeneralLinearGroup.map
      (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L Z)) H.gram :
        Matrix.GeneralLinearGroup (Fin (n + 1)) (SpecialLinear.WeilRoot.tensorAlgebra K L Z))
      i j)
  rw [inv_inv, Matrix.GeneralLinearGroup.map_apply, firstCoord_algebraMap]

/-- Under the inner and outer discrepancy hypotheses, the local isomorphisms are invariant
under every Galois translation of the cover point. -/
theorem localEquiv_coverAut (hin : InnerTrivial L E) (hout : OuterHermitian L H E)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M) (σ : M ≃ₐ[K] M)
    (y : Z ⟶ (GroupModel.groupScheme K L H).X) :
    localEquiv L H E (a ≫ coverAut K M σ) y = localEquiv L H E a y := by
  rw [localEquiv_apply, localEquiv_apply]
  by_cases hσ : ∀ l : L, σ (algebraMap L M l) = algebraMap L M l
  · have hs : splitAt L H (a ≫ coverAut K M σ) (GroupModel.pointsEquiv K L H Z y) =
        splitAt L H a (GroupModel.pointsEquiv K L H Z y) := by
      apply Subtype.ext
      rw [coe_splitAt, coe_splitAt]
      congr 1
      funext x
      exact firstCoord_coverAut_of_fixes L a σ hσ x
    rw [hs]
    exact toFun_coverAut_of_discrepancy E σ a _ _ (hin σ hσ Z a _)
  · have hmv : ∃ y : L, σ (algebraMap L M y) ≠ algebraMap L M y := not_forall.mp hσ
    have hs : splitAt L H (a ≫ coverAut K M σ) (GroupModel.pointsEquiv K L H Z y) =
        splitSL (SchemeModel.tensorForm K L H Z) (secondCoord L a)
          (GroupModel.pointsEquiv K L H Z y) := by
      apply Subtype.ext
      rw [coe_splitAt, coe_splitSL]
      congr 1
      funext x
      exact firstCoord_coverAut_of_moves L a σ hmv x
    rw [hs]
    apply toFun_coverAut_of_discrepancy E σ a
    apply Subtype.ext
    rw [hout σ hmv Z a, coefficients_gram_inv, coefficients_gram]
    exact splitSL_conj (SchemeModel.tensorForm K L H Z) (firstCoord L a) (secondCoord L a)
      (secondCoord_eq L a) (GroupModel.pointsEquiv K L H Z y)

end Local

section Descent

variable {K : Type u} (L : Type u) {M : Type u} [Field K] [Field L] [Field M] [Algebra K L]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {n : ℕ} (H : Form (fieldInvolution K L) (Fin (n + 1)))
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K M))

/-- The local isomorphisms from `SU(H)` to `G`, as a local group isomorphism over the
cover. -/
def localIso : LocalGroupIso (GroupModel.groupScheme K L H) G (cover K M) where
  toFun a := localEquiv L H E a
  naturality t a y := localEquiv_naturality L H E t a y

theorem localIso_isInvariant (hin : InnerTrivial L E) (hout : OuterHermitian L H E)
    (σ : M ≃ₐ[K] M) :
    (localIso L H E).IsInvariant (algebraBaseMap K M) (galoisBaseMap K M σ)
      (galoisBaseMap_over K M σ) :=
  fun a y => localEquiv_coverAut L H E hin hout a σ y

variable [IsGalois K M] [IsAffineHom G.X.hom]

/-- The isomorphism `SU(H) ≅ G` descended from the local isomorphisms. -/
def descendedIso (hin : InnerTrivial L E) (hout : OuterHermitian L H E) :
    GroupModel.groupScheme K L H ≅ G :=
  LocalGroupIso.galoisDescendIso (localIso L H E) (localIso_isInvariant L H E hin hout)

/-- On every test scheme with a cover point `a`, the descended isomorphism is the local
isomorphism at `a`. -/
theorem comp_descendedIso_hom (hin : InnerTrivial L E) (hout : OuterHermitian L H E)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K M)
    (y : Z ⟶ (GroupModel.groupScheme K L H).X) :
    y ≫ (descendedIso L H E hin hout).hom.hom.hom = localEquiv L H E a y :=
  LocalGroupIso.comp_galoisDescendIso_hom (localIso L H E)
    (localIso_isInvariant L H E hin hout) a y

end Descent

section Presentation

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {Idx : Type} [Fintype Idx] [DecidableEq Idx] (H : Form (fieldInvolution K L) Idx)
  {G : GroupScheme (Spec (CommRingCat.of K))} (φ : GroupModel.groupScheme K L H ≅ G)

/-- The tensor matrices of the points of `G`, through an isomorphism with `SU(H)`. -/
def matrixPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ G.X) →* Matrix.GeneralLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra K L T) :=
  (SchemeModel.tensorPoints K L H T).subtype.comp
    ((GroupModel.pointsEquiv K L H T).toMonoidHom.comp (isoPointsEquiv φ.symm T).toMonoidHom)

theorem matrixPoints_apply (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X) :
    matrixPoints K L H φ T x = (GroupModel.pointsEquiv K L H T (x ≫ φ.inv.hom.hom)).1 := rfl

theorem matrixPoints_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (matrixPoints K L H φ T) :=
  Subtype.val_injective.comp ((GroupModel.pointsEquiv K L H T).injective.comp
    (isoPointsEquiv φ.symm T).injective)

theorem matrixPoints_comp_hom (T : Over (Spec (CommRingCat.of K)))
    (y : T ⟶ (GroupModel.groupScheme K L H).X) :
    matrixPoints K L H φ T (y ≫ φ.hom.hom.hom) = (GroupModel.pointsEquiv K L H T y).1 := by
  have h : φ.hom.hom.hom ≫ φ.inv.hom.hom = 𝟙 _ := congrArg (fun f => f.hom.hom) φ.hom_inv_id
  rw [matrixPoints_apply, Category.assoc, h, Category.comp_id]

/-- The image of the matrix points is exactly the determinant-one isometries of `H`. -/
theorem mem_range_matrixPoints (T : Over (Spec (CommRingCat.of K)))
    (g : Matrix.GeneralLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra K L T)) :
    g ∈ (matrixPoints K L H φ T).range ↔
      (((g : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
          (H.gram : Matrix Idx Idx L).map
            (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
          (g : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
        (H.gram : Matrix Idx Idx L).map
          (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) ∧
      Matrix.GeneralLinearGroup.det g = 1) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (GroupModel.pointsEquiv K L H T (x ≫ φ.inv.hom.hom)).2
  · intro hg
    obtain ⟨y, hy⟩ := (GroupModel.pointsEquiv K L H T).surjective ⟨g, hg⟩
    exact ⟨y ≫ φ.hom.hom.hom, by rw [matrixPoints_comp_hom, hy]⟩

/-- The matrix points are natural in the test scheme. -/
theorem matrixPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    (matrixPoints K L H φ T' (a ≫ x) :
        Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
      (matrixPoints K L H φ T x : Matrix Idx Idx
        (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SpecialLinear.WeilRoot.tensorMap K L a) := by
  rw [matrixPoints_apply, matrixPoints_apply, Category.assoc]
  exact GroupModel.pointsEquiv_naturality K L H a _

end Presentation

end Langlands.GroupScheme.OuterTypeAHermitian
