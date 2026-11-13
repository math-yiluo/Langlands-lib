import Langlands.GroupScheme.Examples.HermitianMatrixPresentation

/-! # Comparison with the hyperbolic-plus-diagonal Hermitian model -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

section Rings

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B]
  {Middle : Type v} [Fintype Middle] [DecidableEq Middle]
  {c : RingInvolution A} {d : RingInvolution B}

/-- The existing nonsingular hyperbolic-plus-diagonal Gram matrix as a general form. -/
def ofRoot (H : HermitianRoot.DiagonalForm c Middle) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) : Form c (HermitianRoot.Index Middle) where
  gram := HermitianRoot.gramElement H w hw
  hermitian := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [adjoint, HermitianRoot.gram, Matrix.fromBlocks, Matrix.diagonal_apply,
        eq_comm]
    by_cases h : i = j
    · subst j
      simp [H.bar_weight]
    · simp [h]

@[simp] theorem ofRoot_gram (H : HermitianRoot.DiagonalForm c Middle)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i) :
    ((ofRoot H w hw).gram : Matrix (HermitianRoot.Index Middle)
      (HermitianRoot.Index Middle) A) = HermitianRoot.gram H := rfl

@[simp] theorem preserves_ofRoot_iff (H : HermitianRoot.DiagonalForm c Middle)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (M : Matrix (HermitianRoot.Index Middle) (HermitianRoot.Index Middle) A) :
    Preserves (ofRoot H w hw) M ↔ HermitianRoot.PreservesForm H M := Iff.rfl

/-- These are equal subgroups of the same actual general-linear group. -/
theorem specialUnitarySubgroup_ofRoot (H : HermitianRoot.DiagonalForm c Middle)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i) :
    specialUnitarySubgroup (ofRoot H w hw) = HermitianRoot.specialUnitarySubgroup H := by
  ext g
  rfl

/-- The comparison preserves the actual matrix, in both directions. -/
def rootEquiv (H : HermitianRoot.DiagonalForm c Middle) (w : Middle → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    specialUnitarySubgroup (ofRoot H w hw) ≃* HermitianRoot.specialUnitarySubgroup H :=
  MulEquiv.subgroupCongr (specialUnitarySubgroup_ofRoot H w hw)

@[simp] theorem rootEquiv_val (H : HermitianRoot.DiagonalForm c Middle)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (g : specialUnitarySubgroup (ofRoot H w hw)) : (rootEquiv H w hw g).1 = g.1 := rfl

@[simp] theorem rootEquiv_symm_val (H : HermitianRoot.DiagonalForm c Middle)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (g : HermitianRoot.specialUnitarySubgroup H) :
    ((rootEquiv H w hw).symm g).1 = g.1 := rfl

variable {H : HermitianRoot.DiagonalForm c Middle}
  {J : HermitianRoot.DiagonalForm d Middle}

/-- The general form comparison respects every compatible coefficient change. -/
theorem ofRoot_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = J.weight i)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (z : Middle → Bˣ) (hz : ∀ i, (z i : B) = J.weight i) :
    (ofRoot H w hw).map f hf = ofRoot J z hz := by
  apply Form.ext
  exact HermitianRoot.map_gramElement f hH w hw z hz

/-- Coefficient maps agree on the actual subgroup comparison. -/
theorem rootEquiv_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = J.weight i)
    (w : Middle → Aˣ) (hw : ∀ i, (w i : A) = H.weight i)
    (z : Middle → Bˣ) (hz : ∀ i, (z i : B) = J.weight i)
    (g : specialUnitarySubgroup (ofRoot H w hw)) :
    rootEquiv J z hz
      (coefficientMap f hf (HermitianRoot.gram_map f hH).symm g) =
      HermitianRoot.specialUnitaryMap f hf hH (rootEquiv H w hw g) := by
  apply Subtype.ext
  rfl

end Rings

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : HermitianRoot.DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- Extending the general form is the same as extending the specialized weights. -/
theorem tensorForm_ofRoot (T : Over (Spec (CommRingCat.of k))) :
    tensorForm k L (ofRoot H w hw) T =
      ofRoot (HermitianRoot.SchemeModel.tensorForm k L H T)
        (HermitianRoot.SchemeModel.tensorUnits k L w T)
        (HermitianRoot.SchemeModel.tensorUnits_val k L hw T) :=
  ofRoot_map _ (HermitianRoot.SchemeModel.tensorInclusion_bar k L T)
    (fun _ => rfl) w hw _ _

/-- Equality of the actual subgroups after tensor extension. -/
theorem specialUnitarySubgroup_tensorRoot (T : Over (Spec (CommRingCat.of k))) :
    tensorPoints k L (ofRoot H w hw) T =
      HermitianRoot.specialUnitarySubgroup (HermitianRoot.SchemeModel.tensorForm k L H T) := by
  unfold tensorPoints
  rw [tensorForm_ofRoot, specialUnitarySubgroup_ofRoot]

/-- Identity on actual matrices identifies the two tensor point interfaces. -/
def tensorRootEquiv (T : Over (Spec (CommRingCat.of k))) :
    tensorPoints k L (ofRoot H w hw) T ≃*
      HermitianRoot.specialUnitarySubgroup (HermitianRoot.SchemeModel.tensorForm k L H T) :=
  MulEquiv.subgroupCongr (specialUnitarySubgroup_tensorRoot k L H w hw T)

@[simp] theorem tensorRootEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (g : tensorPoints k L (ofRoot H w hw) T) :
    (tensorRootEquiv k L H w hw T g).1 = g.1 := rfl

@[simp] theorem tensorRootEquiv_symm_val (T : Over (Spec (CommRingCat.of k)))
    (g : HermitianRoot.specialUnitarySubgroup (HermitianRoot.SchemeModel.tensorForm k L H T)) :
    ((tensorRootEquiv k L H w hw T).symm g).1 = g.1 := rfl

/-- The tensor comparison retains every test-scheme restriction. -/
theorem tensorRootEquiv_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (g : tensorPoints k L (ofRoot H w hw) T) :
    tensorRootEquiv k L H w hw T' (tensorPointsMap k L (ofRoot H w hw) a g) =
      HermitianRoot.specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a)
        (SU3Root.SchemeModel.tensorMap_bar k L a)
        (HermitianRoot.SchemeModel.tensorMap_weight k L H a)
        (tensorRootEquiv k L H w hw T g) := by
  apply Subtype.ext
  rfl

/-- The existing represented model supplies an all-test general matrix presentation. -/
def rootPresentation : Presentation k L (ofRoot H w hw)
    (HermitianRoot.SchemeModel.groupScheme k L H w hw) where
  pointsEquiv T := (HermitianRoot.SchemeModel.pointsEquiv k L H w hw T).trans
    (tensorRootEquiv k L H w hw T).symm
  matrix_naturality a x := HermitianRoot.SchemeModel.pointsEquiv_naturality k L H w hw a x

namespace Presentation

variable {k L} {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Supplied general presentation data gives the original specialized matrix points. -/
def rootPointsEquiv (e : Presentation k L (ofRoot H w hw) G)
    (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ G.X) ≃*
      HermitianRoot.specialUnitarySubgroup (HermitianRoot.SchemeModel.tensorForm k L H T) :=
  (e.pointsEquiv T).trans (tensorRootEquiv k L H w hw T)

/-- This conversion keeps the entrywise matrix naturality needed by the existing model. -/
theorem rootPointsEquiv_naturality (e : Presentation k L (ofRoot H w hw) G)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ G.X) :
    ((e.rootPointsEquiv H w hw T' (a ≫ x)).1 : Matrix (HermitianRoot.Index Middle)
      (HermitianRoot.Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      ((e.rootPointsEquiv H w hw T x).1 : Matrix (HermitianRoot.Index Middle)
        (HermitianRoot.Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
          (SpecialLinear.WeilRoot.tensorMap k L a) := e.matrix_naturality a x

/-- The general all-test presentation feeds the existing actual scheme identification. -/
def rootIso (e : Presentation k L (ofRoot H w hw) G) :
    G ≅ HermitianRoot.SchemeModel.groupScheme k L H w hw :=
  HermitianRoot.SchemeModel.isoOfMatrixPoints k L H w hw
    (e.rootPointsEquiv H w hw) (e.rootPointsEquiv_naturality H w hw)

/-- The identification realizes the originally supplied matrix values. -/
theorem rootIso_hom (e : Presentation k L (ofRoot H w hw) G)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    HermitianRoot.SchemeModel.pointsEquiv k L H w hw T
      (x ≫ (e.rootIso H w hw).hom.hom.hom) =
      tensorRootEquiv k L H w hw T (e.pointsEquiv T x) :=
  HermitianRoot.SchemeModel.isoOfMatrixPoints_hom k L H w hw
    (e.rootPointsEquiv H w hw) (e.rootPointsEquiv_naturality H w hw) T x

/-- A congruence from a general presentation identifies the group with the root model. -/
def rootIsometryIso {J : Form (fieldInvolution k L) (HermitianRoot.Index Middle)}
    (e : Presentation k L J G)
    (P : Matrix.GeneralLinearGroup (HermitianRoot.Index Middle) L)
    (hP : adjoint (fieldInvolution k L)
        (P : Matrix (HermitianRoot.Index Middle) (HermitianRoot.Index Middle) L) *
      HermitianRoot.gram H *
        (P : Matrix (HermitianRoot.Index Middle) (HermitianRoot.Index Middle) L) = J.gram) :
    G ≅ HermitianRoot.SchemeModel.groupScheme k L H w hw :=
  (e.isometry (J := ofRoot H w hw) P hP).rootIso H w hw

/-- On every test scheme the congruence bridge realizes actual conjugated matrices. -/
theorem rootIsometryIso_hom {J : Form (fieldInvolution k L) (HermitianRoot.Index Middle)}
    (e : Presentation k L J G)
    (P : Matrix.GeneralLinearGroup (HermitianRoot.Index Middle) L)
    (hP : adjoint (fieldInvolution k L)
        (P : Matrix (HermitianRoot.Index Middle) (HermitianRoot.Index Middle) L) *
      HermitianRoot.gram H *
        (P : Matrix (HermitianRoot.Index Middle) (HermitianRoot.Index Middle) L) = J.gram)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (HermitianRoot.SchemeModel.pointsEquiv k L H w hw T
      (x ≫ (e.rootIsometryIso H w hw P hP).hom.hom.hom)).1 =
      tensorMatrix k L P T * (e.pointsEquiv T x).1 * (tensorMatrix k L P T)⁻¹ :=
  congrArg Subtype.val ((e.isometry (J := ofRoot H w hw) P hP).rootIso_hom H w hw T x)

end Presentation
end SchemeModel
end Langlands.GroupScheme.HermitianMatrix
