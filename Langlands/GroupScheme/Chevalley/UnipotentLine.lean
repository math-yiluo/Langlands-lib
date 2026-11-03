import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Coordinate lines in representations of unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {n : Type} [Fintype n] [DecidableEq n]

/-- Preservation of a coordinate line on every scheme test, with a global unit
as the scalar. -/
def PreservesCoordinateLine (ρ : MatrixRepresentation G n) (j : n) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
    ∃ a : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
        (a : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤))

variable (ρ : MatrixRepresentation G n) (j : n)
    (hline : ρ.PreservesCoordinateLine j)

/-- The unique scalar on the chosen coordinate line. -/
def coordinateLineScalar (T : Over (Spec R)) (x : T ⟶ G.X) : Γ(T.left, ⊤)ˣ :=
  Classical.choose (hline T x)

theorem coordinateLineScalar_spec (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      (coordinateLineScalar ρ j hline T x : Γ(T.left, ⊤)) •
        (Pi.single j 1 : n → Γ(T.left, ⊤)) :=
  Classical.choose_spec (hline T x)

@[simp] theorem coordinateLineScalar_val (T : Over (Spec R)) (x : T ⟶ G.X) :
    (coordinateLineScalar ρ j hline T x : Γ(T.left, ⊤)) = ρ.pointMatrix T x j j := by
  have h := congrFun (coordinateLineScalar_spec ρ j hline T x) j
  simpa using h.symm

/-- The line scalar is a homomorphism on the full group of test points. -/
def coordinateLineScalarHom (T : Over (Spec R)) :
    (T ⟶ G.X) →* Γ(T.left, ⊤)ˣ where
  toFun := coordinateLineScalar ρ j hline T
  map_one' := by
    apply Units.ext
    rw [coordinateLineScalar_val, map_one]
    simp
  map_mul' x y := by
    apply Units.ext
    have h := coordinateLineScalar_spec ρ j hline T (x * y)
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      coordinateLineScalar_spec ρ j hline T y, Matrix.mulVec_smul,
      coordinateLineScalar_spec ρ j hline T x, smul_smul] at h
    have hj := congrFun h j
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hj
    rw [Units.val_mul]
    exact hj.symm.trans (mul_comm _ _)

theorem coordinateLineScalar_naturality {T W : Over (Spec R)}
    (b : W ⟶ T) (x : T ⟶ G.X) :
    coordinateLineScalar ρ j hline W (b ≫ x) =
      Units.map b.left.appTop.hom.toMonoidHom (coordinateLineScalar ρ j hline T x) := by
  apply Units.ext
  simp only [coordinateLineScalar_val, Units.coe_map,
    pointMatrix_naturality]
  rfl

/-- The actual character defined by a preserved coordinate line, on all test points. -/
def coordinateLineCharacterPoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    (coordinateLineScalarHom ρ j hline T)

theorem coordinateLineCharacterPoints_naturality {T W : Over (Spec R)}
    (b : W ⟶ T) (x : T ⟶ G.X) :
    coordinateLineCharacterPoints ρ j hline W (b ≫ x) =
      b ≫ coordinateLineCharacterPoints ρ j hline T x := by
  apply (Gm.pointsEquiv (Spec R) W).injective
  change (Gm.pointsEquiv (Spec R) W) ((Gm.pointsEquiv (Spec R) W).symm _) =
    (Gm.pointsEquiv (Spec R) W) (b ≫ (Gm.pointsEquiv (Spec R) T).symm _)
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  exact coordinateLineScalar_naturality ρ j hline b x

/-- The scheme-theoretic character on the preserved coordinate line. -/
def coordinateLineCharacter : G ⟶ (Gm (Spec R)).toGrp :=
  homOfPoints (coordinateLineCharacterPoints ρ j hline)
    (coordinateLineCharacterPoints_naturality ρ j hline)

theorem coordinateLineCharacter_scalar (T : Over (Spec R)) (x : T ⟶ G.X) :
    Gm.pointsEquiv (Spec R) T (x ≫ (coordinateLineCharacter ρ j hline).hom.hom) =
      coordinateLineScalar ρ j hline T x := by
  rw [coordinateLineCharacter, comp_homOfPoints]
  exact (Gm.pointsEquiv (Spec R) T).apply_symm_apply _

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}

/-- A unipotent group fixes every coordinate line that it preserves. -/
theorem fixed_coordinateLine_of_isUnipotent (σ : MatrixRepresentation H n)
    (j : n) (hline : σ.PreservesCoordinateLine j) (hH : IsUnipotent H)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) :
    (σ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      Pi.single j 1 := by
  have hgm : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp :=
    IsSplitTorus.of_iso (splitTorus.gmIso _) (isSplitTorus_splitTorus PUnit)
  have h := hH.comp_eq_one_of_isSplitTorus hgm
    (coordinateLineCharacter σ j hline) T x
  have hscalar : coordinateLineScalar σ j hline T x = 1 := by
    rw [← coordinateLineCharacter_scalar, h, map_one]
  rw [coordinateLineScalar_spec σ j hline T x, hscalar, Units.val_one, one_smul]

/-- A line-stabilizer description of the range of a unipotent group is already
an exact vector-stabilizer description on every scheme test. -/
theorem range_iff_fixes_coordinateLine_of_isUnipotent
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : H ⟶ G)
    (ρ : MatrixRepresentation G n) (j : n) (hH : IsUnipotent H)
    (hstab : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range z).carrier T ↔
        ∃ a : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
            (a : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)))
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range z).carrier T ↔
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
        Pi.single j 1 := by
  have hline : (ρ.restrict z).PreservesCoordinateLine j := by
    intro W y
    simpa only [pointMatrix_restrict] using (hstab W (y ≫ z.hom.hom)).1 ⟨y, rfl⟩
  constructor
  · rintro ⟨y, rfl⟩
    change (ρ.pointMatrix T (y ≫ z.hom.hom) : Matrix n n Γ(T.left, ⊤)) *ᵥ
      Pi.single j 1 = Pi.single j 1
    have hf := fixed_coordinateLine_of_isUnipotent (ρ.restrict z) j hline hH T y
    rw [pointMatrix_restrict ρ z T y] at hf
    exact hf
  · intro hx
    exact (hstab T x).2 ⟨1, by simpa only [Units.val_one, one_smul] using hx⟩

end Langlands.GroupScheme.MatrixRepresentation
