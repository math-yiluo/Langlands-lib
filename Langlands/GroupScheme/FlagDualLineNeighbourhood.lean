import Langlands.GroupScheme.ProjectiveQuotientEmbedding
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Invariant affine neighbourhoods from semi-invariant dual lines -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

open GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (n : ℕ) (X : Scheme.{u}) [Algebra R Γ(X, ⊤)]

local notation "𝒜" => projectiveSpaceGrading R n

/-- A translated coordinate basis point lies in the chart `D₊(X j₀)` exactly where the
`j₀`-th coordinate of the translated basis vector is invertible. -/
theorem basisPoint_linearAction_preimage_coordinateOpen (j j₀ : Fin (n + 1))
    (e : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    (basisPoint (R := R) n X j ≫ linearAction R n e) ⁻¹ᵁ
        projectiveSpaceCoordinateOpen R n j₀ =
      X.basicOpen (algebraMap R Γ(X, ⊤) (e (Pi.single j 1) j₀)) := by
  let g := gradedLinearSubstitution R n e.toLinearMap
  let f := basisEval (R := R) n X j
  have hg := irrelevant_le_map_gradedLinearSubstitution R n e
  have hf := basisEval_primitive (R := R) n X j
  have hfg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤ := by
    apply top_unique
    calc
      ⊤ = (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f := hf.symm
      _ ≤ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g.toRingHom).map f :=
        Ideal.map_mono hg
      _ = (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) := Ideal.map_map _ _
  have hX : (f.comp g.toRingHom) (MvPolynomial.X j₀) =
      algebraMap R Γ(X, ⊤) (e (Pi.single j 1) j₀) := by
    change basisEval (R := R) n X j (linearSubstitution R n e.toLinearMap (MvPolynomial.X j₀)) = _
    rw [basisEval_eq_eval, linearSubstitution_X, eval_linearFormPolynomialEquiv]
    rfl
  change (Proj.fromOfGlobalSections 𝒜 f hf ≫ Proj.map g hg) ⁻¹ᵁ
    Proj.basicOpen 𝒜 (MvPolynomial.X j₀) = _
  rw [← fromOfGlobalSections_comp_gradedMap n g hg f hf hfg,
    Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 _ _ Nat.one_pos
      (projectiveSpace_X_mem R n j₀), hX]

end Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateLines

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A translated basis section lies in the relative chart `D₊(X j₀)` exactly where the
`j₀`-th coordinate of the translated basis vector is invertible. -/
theorem basisSection_globalLinearAction_preimage_coordinateOpen (n : ℕ) (X : Scheme.{u})
    (j j₀ : Fin (n + 1))
    (e : (Fin (n + 1) → Γ(X, ⊤)) ≃ₗ[Γ(X, ⊤)] (Fin (n + 1) → Γ(X, ⊤))) :
    (basisSection n X j ≫ globalLinearAction n e) ⁻¹ᵁ coordinateOpen X n j₀ =
      X.basicOpen (e (Pi.single j 1) j₀) := by
  rw [← toPolynomial_preimage_coordinateOpen n X.toSpecΓ j₀, ← Scheme.Hom.comp_preimage]
  have h : (basisSection n X j ≫ globalLinearAction n e) ≫ toPolynomial n X.toSpecΓ =
      ProjectiveSpace.CoordinateLines.basisPoint (R := Γ(X, ⊤)) n X j ≫
        ProjectiveSpace.linearAction Γ(X, ⊤) n e := by
    simp only [globalLinearAction, Category.assoc, linearAction_toPolynomial,
      basisSection_toPolynomial_assoc]
  rw [h, ProjectiveSpace.CoordinateLines.basisPoint_linearAction_preimage_coordinateOpen]
  rfl

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RationalPoints

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- On a reduced scheme locally of finite type over an algebraically closed field, global
functions with equal values at all rational points are equal. -/
theorem eq_of_rationalPoints {Z : Over (Spec (CommRingCat.of k))}
    [IsReduced Z.left] [LocallyOfFiniteType Z.hom] {f g : Γ(Z.left, ⊤)}
    (h : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z,
      z.left.appTop f = z.left.appTop g) :
    f = g := by
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  rw [← sub_eq_zero, ← AlgebraicGeometry.basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hxU, hx⟩ := nonempty_inter_closedPoints
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
    (Z.left.basicOpen (f - g)).isOpen.isLocallyClosed
  let z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z :=
    Over.homMk (pointOfClosedPoint Z.hom x hx) (pointOfClosedPoint_comp Z.hom x hx)
  have hmem : IsLocalRing.closedPoint k ∈ z.left ⁻¹ᵁ Z.left.basicOpen (f - g) := by
    change pointOfClosedPoint Z.hom x hx (IsLocalRing.closedPoint k) ∈ Z.left.basicOpen (f - g)
    rw [pointOfClosedPoint_apply]
    exact hxU
  rw [Scheme.preimage_basicOpen_top, map_sub, h z, sub_self, Scheme.basicOpen_zero] at hmem
  exact hmem

/-- Evaluation of global functions at a rational point, with values in the field. -/
def rationalEval {Z : Over (Spec (CommRingCat.of k))}
    (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z) : Γ(Z.left, ⊤) →+* k :=
  (z.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom

omit [IsAlgClosed k] in
/-- Rational-point evaluation of a scalar is the scalar itself. -/
@[simp] theorem rationalEval_scalarMap {Z : Over (Spec (CommRingCat.of k))}
    (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z) (c : k) :
    rationalEval z (scalarMap Z c) = c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Z.hom.appTop ≫ z.left.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom) c = c
  rw [← Scheme.Hom.comp_appTop_assoc, Over.w z]
  simp

/-- Global functions agreeing under every rational-point evaluation are equal. -/
theorem eq_of_rationalEval {Z : Over (Spec (CommRingCat.of k))}
    [IsReduced Z.left] [LocallyOfFiniteType Z.hom] {f g : Γ(Z.left, ⊤)}
    (h : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z,
      rationalEval z f = rationalEval z g) :
    f = g := by
  apply eq_of_rationalPoints
  intro z
  have hz := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (h z)
  simpa [rationalEval] using hz

omit [IsAlgClosed k] in
/-- The rational matrix of a point is the evaluation of the universal matrix. -/
theorem map_rationalEval_pointMatrix {H : GroupScheme (Spec (CommRingCat.of k))}
    {m : Type} [Fintype m] [DecidableEq m] (σ : MatrixRepresentation H m)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    Matrix.GeneralLinearGroup.map (rationalEval z) (σ.pointMatrix H.X (𝟙 H.X)) =
      σ.rationalMatrix z := by
  have hz := σ.pointMatrix_naturality z (𝟙 H.X)
  rw [Category.comp_id] at hz
  rw [MatrixRepresentation.rationalMatrix, MonoidHom.comp_apply]
  erw [hz]
  ext i j
  rfl

end RationalPoints

section RowSemiInvariance

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A row vector whose line is stable under all rational points of a reduced group locally of
finite type is semi-invariant on every test: its translate is a unit multiple of it. -/
theorem exists_unit_vecMul_of_rationalPoints {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    {m : Type} [Fintype m] [DecidableEq m] (σ : MatrixRepresentation H m)
    (w : m → k) (j₀ : m) (hw : w j₀ ≠ 0)
    (hσ : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, ∃ c : kˣ,
      w ᵥ* (σ.rationalMatrix x : Matrix m m k) = (c : k) • w)
    (Z : Over (Spec (CommRingCat.of k))) (h : Z ⟶ H.X) :
    ∃ c : Γ(Z.left, ⊤)ˣ,
      (fun l => scalarMap Z (w l)) ᵥ* (σ.pointMatrix Z h : Matrix m m Γ(Z.left, ⊤)) =
        (c : Γ(Z.left, ⊤)) • fun l => scalarMap Z (w l) := by
  let A := Γ(H.X.left, ⊤)
  let W : m → A := fun l => scalarMap H.X (w l)
  let g₀ := σ.pointMatrix H.X (𝟙 H.X)
  -- semi-invariance of `w` under the inverse rational matrices
  have hσinv : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, ∃ c : kˣ,
      w ᵥ* ((σ.rationalMatrix x)⁻¹ : GL m k) = (c : k) • w := by
    intro x
    obtain ⟨c, hc⟩ := hσ x
    refine ⟨c⁻¹, ?_⟩
    have hone : ((σ.rationalMatrix x : GL m k) : Matrix m m k) *
        (((σ.rationalMatrix x)⁻¹ : GL m k) : Matrix m m k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc
      w ᵥ* (((σ.rationalMatrix x)⁻¹ : GL m k) : Matrix m m k) =
          (((c⁻¹ : kˣ) : k) • ((c : k) • w)) ᵥ* (((σ.rationalMatrix x)⁻¹ : GL m k) :
            Matrix m m k) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = ((c⁻¹ : kˣ) : k) • ((w ᵥ* ((σ.rationalMatrix x : GL m k) : Matrix m m k)) ᵥ*
            (((σ.rationalMatrix x)⁻¹ : GL m k) : Matrix m m k)) := by
        rw [Matrix.smul_vecMul, hc]
      _ = ((c⁻¹ : kˣ) : k) • w := by
        rw [Matrix.vecMul_vecMul, hone, Matrix.vecMul_one]
  -- the universal proportionality identities, checked at rational points
  have hprop : ∀ g : GL m A,
      (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, ∃ c : kˣ,
        w ᵥ* (Matrix.GeneralLinearGroup.map (rationalEval x) g : Matrix m m k) = (c : k) • w) →
      ∀ l, (W ᵥ* (g : Matrix m m A)) l * W j₀ = (W ᵥ* (g : Matrix m m A)) j₀ * W l := by
    intro g hg l
    apply eq_of_rationalEval
    intro x
    obtain ⟨c, hc⟩ := hg x
    have hW' : ∀ l, rationalEval x (W l) = w l := fun l => rationalEval_scalarMap x (w l)
    have hW : rationalEval x ∘ W = w := funext hW'
    simp only [map_mul, RingHom.map_vecMul, hW, hW']
    have hmap : (g : Matrix m m A).map (rationalEval x) =
        (Matrix.GeneralLinearGroup.map (rationalEval x) g : Matrix m m k) := rfl
    rw [hmap, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h₁ := hprop g₀ (fun x => by
    rw [map_rationalEval_pointMatrix]
    exact hσ x)
  have h₂ := hprop g₀⁻¹ (fun x => by
    rw [map_inv, map_rationalEval_pointMatrix]
    exact hσinv x)
  -- the unit `W j₀`
  have ha : IsUnit (W j₀) := (Ne.isUnit hw).map (scalarMap H.X)
  obtain ⟨a, ha'⟩ := ha
  let c₀ := (W ᵥ* (g₀ : Matrix m m A)) j₀ * ((a⁻¹ : Aˣ) : A)
  let d₀ := (W ᵥ* ((g₀⁻¹ : GL m A) : Matrix m m A)) j₀ * ((a⁻¹ : Aˣ) : A)
  have hscale : ∀ (v : m → A),
      (∀ l, v l * W j₀ = v j₀ * W l) → v = (v j₀ * ((a⁻¹ : Aˣ) : A)) • W := by
    intro v hv
    funext l
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      v l = v l * W j₀ * ((a⁻¹ : Aˣ) : A) := by
        rw [← ha', mul_assoc, Units.mul_inv, mul_one]
      _ = v j₀ * ((a⁻¹ : Aˣ) : A) * W l := by
        rw [hv l]
        ring
  have hc₀ : W ᵥ* (g₀ : Matrix m m A) = c₀ • W := hscale _ h₁
  have hd₀ : W ᵥ* ((g₀⁻¹ : GL m A) : Matrix m m A) = d₀ • W := hscale _ h₂
  have hcd : c₀ * d₀ = 1 := by
    have hone : (g₀ : Matrix m m A) * ((g₀⁻¹ : GL m A) : Matrix m m A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hW : W = (c₀ * d₀) • W := by
      calc
        W = W ᵥ* ((g₀ : Matrix m m A) * ((g₀⁻¹ : GL m A) : Matrix m m A)) := by
          rw [hone, Matrix.vecMul_one]
        _ = (c₀ * d₀) • W := by
          rw [← Matrix.vecMul_vecMul, hc₀, Matrix.smul_vecMul, hd₀, smul_smul]
    have hj := congrFun hW j₀
    simp only [Pi.smul_apply, smul_eq_mul] at hj
    rw [← ha'] at hj
    have := congrArg (· * ((a⁻¹ : Aˣ) : A)) hj
    simpa [mul_assoc] using this.symm
  -- transport along the test point `h`
  let φ := h.left.appTop.hom
  refine ⟨Units.map φ.toMonoidHom ⟨c₀, d₀, hcd, by rw [mul_comm]; exact hcd⟩, ?_⟩
  have hφW' : ∀ l, φ (W l) = scalarMap Z (w l) := by
    intro l
    change h.left.appTop (H.X.hom.appTop ((Scheme.ΓSpecIso _).inv (w l))) =
      Z.hom.appTop ((Scheme.ΓSpecIso _).inv (w l))
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w h]
  have hφW : φ ∘ W = fun l => scalarMap Z (w l) := funext hφW'
  have hφg : (g₀ : Matrix m m A).map φ = (σ.pointMatrix Z h : Matrix m m Γ(Z.left, ⊤)) := by
    have hh := σ.pointMatrix_naturality h (𝟙 H.X)
    rw [Category.comp_id] at hh
    rw [hh]
    rfl
  funext l
  have hl := congrArg (fun v => φ (v l)) hc₀
  simp only [RingHom.map_vecMul, Pi.smul_apply, smul_eq_mul, map_mul, hφW, hφW', hφg] at hl
  simpa only [Pi.smul_apply, smul_eq_mul, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, hφW] using hl

end RowSemiInvariance

namespace ProjectiveOrbit

/-- A translated basis section lies in the chart `D₊(X j₀)` exactly where the `(j₀, j)` entry
of the translating matrix is invertible. -/
theorem basisSection_matrixAction_preimage_coordinateOpen (n : ℕ) (T : Scheme.{u})
    (j j₀ : Fin (n + 1)) (N : GL (Fin (n + 1)) Γ(T, ⊤)) :
    (RelativeProjectiveSpace.basisSection n T j ≫ matrixAction n N) ⁻¹ᵁ
        RelativeProjectiveSpace.coordinateOpen T n j₀ =
      T.basicOpen ((N : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) j₀ j) := by
  rw [matrixAction,
    RelativeProjectiveSpace.basisSection_globalLinearAction_preimage_coordinateOpen,
    coordinateEquiv_apply, Matrix.mulVec_single_one]
  rfl

/-- A test point of the orbit map of the `j`-th coordinate line lies in the chart translated
by `P` exactly where the `(j₀, j)` entry of `P ρ(g)` is invertible. -/
theorem comp_orbitMap_basisSection_preimage_translatedChart {n : ℕ} {R : CommRingCat.{u}}
    {G : GroupScheme (Spec R)} (ρ : MatrixRepresentation G (Fin (n + 1))) (j : Fin (n + 1))
    {Z : Over (Spec R)} (g : Z ⟶ G.X) (P : GL (Fin (n + 1)) Γ(Spec R, ⊤))
    (j₀ : Fin (n + 1)) :
    (g ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n (Spec R) j)).left ⁻¹ᵁ
        translatedChart P j₀ =
      Z.left.basicOpen (((Matrix.GeneralLinearGroup.map Z.hom.appTop.hom P *
        ρ.pointMatrix Z g : GL (Fin (n + 1)) Γ(Z.left, ⊤)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j₀ j) := by
  rw [comp_orbitMap, Scheme.Hom.comp_preimage, map_preimage_translatedChart, orbitSection,
    pullbackPoint_basisSection, ← Scheme.Hom.comp_preimage, Category.assoc,
    ← matrixAction_mul, basisSection_matrixAction_preimage_coordinateOpen]

end ProjectiveOrbit

section BasisChange

variable {k : Type u} [Field k] {n : ℕ}

/-- Replacing the `j₀`-th row of the identity matrix by `w` gives determinant `w j₀`. -/
theorem det_one_updateRow (w : Fin (n + 1) → k) (j₀ : Fin (n + 1)) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow j₀ w).det = w j₀ := by
  have hw : w = ∑ l, w l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) l := by
    ext i
    simp [Matrix.one_apply]
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j₀ w
  rw [← hw, Matrix.det_one, smul_eq_mul, mul_one] at h
  exact h

/-- The coordinate change over `Γ(Spec k, 𝒪)` whose `j₀`-th row is the linear form `w`
and whose other rows are standard. -/
def dualLineChange (w : Fin (n + 1) → k) (j₀ : Fin (n + 1)) (hw : w j₀ ≠ 0) :
    GL (Fin (n + 1)) Γ(Spec (CommRingCat.of k), ⊤) :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow j₀ w)
      (by rw [det_one_updateRow]; exact hw))

/-- On every test the `j₀`-th row of the coordinate change is the linear form `w`. -/
theorem dualLineChange_row (w : Fin (n + 1) → k) (j₀ : Fin (n + 1)) (hw : w j₀ ≠ 0)
    (Z : Over (Spec (CommRingCat.of k))) :
    (Matrix.GeneralLinearGroup.map Z.hom.appTop.hom (dualLineChange w j₀ hw) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j₀ =
      fun l => scalarMap Z (w l) := by
  funext l
  change Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow j₀ w) j₀ l)) = _
  rw [Matrix.updateRow_self]
  rfl

/-- The `(j₀, l)` entry of `P M`, for the coordinate change `P`, is the `l`-th entry of `w M`. -/
theorem dualLineChange_mul_apply (w : Fin (n + 1) → k) (j₀ : Fin (n + 1)) (hw : w j₀ ≠ 0)
    (Z : Over (Spec (CommRingCat.of k))) (M : GL (Fin (n + 1)) Γ(Z.left, ⊤))
    (l : Fin (n + 1)) :
    ((Matrix.GeneralLinearGroup.map Z.hom.appTop.hom (dualLineChange w j₀ hw) * M :
        GL (Fin (n + 1)) Γ(Z.left, ⊤)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) j₀ l =
      ((fun l => scalarMap Z (w l)) ᵥ* (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) l := by
  rw [Units.val_mul, ← dualLineChange_row w j₀ hw Z]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

omit [Field k] in
/-- Evaluation at the identity rational point is the canonical identification `Γ(Spec k) ≅ k`. -/
theorem rationalEval_id [Field k] :
    rationalEval (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k))))) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom := by
  simp [rationalEval]

end BasisChange

section Assembly

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Local assembly of the invariant affine neighbourhood. Let `q : G → Q` be a quotient of a smooth
affine group by a smooth closed subgroup `B`, with `Q` proper, such that `B` is the all-test
stabilizer of the `j`-th coordinate line of a representation `ρ`. If for every rational point
`g` there is a linear form not vanishing on `ρ(g) e_j` whose line is stable under the rational
points of a smooth subgroup `U`, then every rational point of `Q` has an affine open
neighbourhood invariant under `U`. -/
theorem exists_invariantAffineOpen_of_dualLines
    {G B U : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (b : B ⟶ G) (hb : IsClosedSubgroup b) (hB : Smooth B.X.hom)
    (i : U ⟶ G) (hU : Smooth U.X.hom)
    (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1)))
    (hρ : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *ᵥ
              Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) :
              Fin (n + 1) → Γ(Z.left, ⊤)))
    {Q : Over (Spec (CommRingCat.of k))} [IsProper Q.hom] (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Z)
    (a : SchemeAction G Q)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (hw : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ∃ w : Fin (n + 1) → k,
        w ⬝ᵥ ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
            (Pi.single j 1 : Fin (n + 1) → k)) ≠ 0 ∧
        ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
          ∃ c : kˣ,
            w ᵥ* (ρ.rationalMatrix (x ≫ i.hom.hom) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (c : k) • w)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    ∃ V : Q.left.Opens,
      IsAffineOpen V ∧ Set.range x.left ⊆ V ∧
        (a.restrict i).hom.left ⁻¹ᵁ V = (snd U.X Q).left ⁻¹ᵁ V := by
  -- lift the rational point to the group
  have : LocallyOfFiniteType q.left := by
    have : LocallyOfFiniteType (q.left ≫ Q.hom) := (Over.w q).symm ▸ inferInstance
    exact locallyOfFiniteType_of_comp q.left Q.hom
  obtain ⟨g', hg'⟩ :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective (K := k) q.left x.left
  have hgS : g' ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q, ← Category.assoc, hg']
    exact Over.w x
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk g' hgS
  have hgx : g ≫ q = x := Over.OverMorphism.ext hg'
  -- the semi-invariant linear form and a coordinate where it does not vanish
  obtain ⟨w, hwg, hwU⟩ := hw g
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, w j₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hwg
    rw [show w = 0 from funext h, zero_dotProduct]
  -- the projective embedding of the quotient
  have : IsClosedImmersion (ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib).left :=
    ProjectiveOrbit.isClosedImmersion_quotientOrbitMap n b j ρ hρ q hfib hb hB
  have hφ := ProjectiveOrbit.isMatrixEquivariant_quotientOrbitMap n b j ρ hρ q hfib a hact
  have hfac : q ≫ ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib =
      ProjectiveOrbit.orbitMap n ρ
        (RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j) :=
    ProjectiveOrbit.fac_quotientOrbitMap n b j ρ hρ q hfib
  have : Smooth U.X.hom := hU
  have : IsReduced U.X.left :=
    SmoothReducedProof.isReduced_of_smooth_over_field k _ U.X.hom
  -- affineness and invariance of the pulled-back translated chart
  obtain ⟨hV, hinv⟩ := ProjectiveOrbit.isAffineOpen_isInvariantOpen_preimage_translatedChart
    a ρ (ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib) hφ i
    (dualLineChange w j₀ hj₀) j₀ (fun Z h => by
      rw [dualLineChange_row]
      obtain ⟨c, hc⟩ := exists_unit_vecMul_of_rationalPoints (ρ.restrict i) w j₀ hj₀
        (fun y => by rw [MatrixRepresentation.rationalMatrix_restrict]; exact hwU y) Z h
      exact ⟨c, by simpa only [MatrixRepresentation.pointMatrix_restrict] using hc⟩)
  refine ⟨_, hV, ?_, hinv⟩
  -- the rational point lies in the chart
  have hx : x.left ⁻¹ᵁ ((ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib).left ⁻¹ᵁ
      ProjectiveOrbit.translatedChart (dualLineChange w j₀ hj₀) j₀) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, ← hgx, Category.assoc, hfac,
      ProjectiveOrbit.comp_orbitMap_basisSection_preimage_translatedChart]
    apply Scheme.basicOpen_of_isUnit
    rw [dualLineChange_mul_apply]
    have hev : rationalEval (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
        (((fun l => scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (w l)) ᵥ*
          (ρ.pointMatrix _ g : Matrix (Fin (n + 1)) (Fin (n + 1)) _)) j) =
        w ⬝ᵥ ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
          (Pi.single j 1 : Fin (n + 1) → k)) := by
      rw [RingHom.map_vecMul, Matrix.dotProduct_mulVec, dotProduct_single, mul_one]
      congr 2
      · funext l
        exact rationalEval_scalarMap _ (w l)
    rw [rationalEval_id] at hev
    have hinvhom : ∀ y : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤),
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y) = y := by
      intro y
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    have hu := (Ne.isUnit (hev ▸ hwg)).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    exact (congrArg IsUnit (hinvhom _)).mp hu
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ x.left ⁻¹ᵁ ((ProjectiveOrbit.quotientOrbitMap n b j ρ hρ q hfib).left ⁻¹ᵁ
      ProjectiveOrbit.translatedChart (dualLineChange w j₀ hj₀) j₀) := by
    rw [hx]
    trivial
  exact hp

end Assembly

end Langlands.GroupScheme
