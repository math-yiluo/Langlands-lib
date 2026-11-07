import Langlands.GroupScheme.Examples.SU3RationalPoints
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.SpecialLinearWeilDynamicRoots

/-! # The actual split diagonal cocharacter of the special unitary scheme -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root

section Coefficients

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

/-- Coefficient change on the actual fixed subgroup of SL3. -/
def twistFixedMap (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    twistFixedSubgroup c →* twistFixedSubgroup d where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.1, by
    change unitaryTwist d (Matrix.SpecialLinearGroup.map f g.1) =
      Matrix.SpecialLinearGroup.map f g.1
    rw [unitaryTwist_map f hf]
    exact congrArg (Matrix.SpecialLinearGroup.map f) g.2⟩
  map_one' := Subtype.ext ((Matrix.SpecialLinearGroup.map f).map_one)
  map_mul' g h := Subtype.ext ((Matrix.SpecialLinearGroup.map f).map_mul g.1 h.1)

/-- Coefficient change on the actual determinant-one Hermitian GL3 subgroup. -/
def specialUnitaryMap (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    specialUnitarySubgroup c →* specialUnitarySubgroup d :=
  (fixedSpecialUnitaryEquiv d).toMonoidHom.comp
    ((twistFixedMap f hf).comp (fixedSpecialUnitaryEquiv c).symm.toMonoidHom)

@[simp] theorem specialUnitaryMap_val (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) (g : specialUnitarySubgroup c) :
    ((specialUnitaryMap f hf g).1 : Matrix (Fin 3) (Fin 3) B) =
      (g.1 : Matrix (Fin 3) (Fin 3) A).map f := rfl

/-- The unitary diagonal is compatible with any involution-compatible coefficient map. -/
theorem map_diagonal (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagonal c t) =
      diagonal d (Units.map f.toMonoidHom t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal_apply, diagonalEntries, barUnit, hf]

/-- All diagonal parameters give actual determinant-one Hermitian matrices. -/
def diagonalSpecialUnitaryHom (c : RingInvolution A) :
    Aˣ →* specialUnitarySubgroup c :=
  (diagonalHom c).codRestrict (specialUnitarySubgroup c)
    (fun t => ⟨diagonal_preservesForm c t, diagonal_det c t⟩)

/-- Coefficient change preserves the specified diagonal parameter. -/
theorem specialUnitaryMap_diagonal (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) (t : Aˣ) :
    specialUnitaryMap f hf (diagonalSpecialUnitaryHom c t) =
      diagonalSpecialUnitaryHom d (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  apply Units.ext
  rw [specialUnitaryMap_val]
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) B =>
    (g : Matrix (Fin 3) (Fin 3) B)) (map_diagonal f hf t)

end Coefficients

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Quadratic conjugation fixes every actual ground-base function in tensor coefficients. -/
theorem sectionToTensor_bar (T : Over (Spec (CommRingCat.of k))) (r : Γ(T.left, ⊤)) :
    (coefficientInvolution k L T).bar (SpecialLinear.WeilRoot.includeSections k L T r) =
      SpecialLinear.WeilRoot.includeSections k L T r := by
  change QuasiSplitUnitary.scalarConjugation (SpecialLinear.WeilRoot.sectionAlgebra k T)
    (conjugation k L)
      ((Algebra.TensorProduct.includeRight :
        SpecialLinear.WeilRoot.sectionAlgebra k T →ₐ[k]
          L ⊗[k] SpecialLinear.WeilRoot.sectionAlgebra k T) r) = _
  erw [Algebra.TensorProduct.includeRight_apply,
    QuasiSplitUnitary.scalarConjugation_tmul, map_one]

/-- The matrix-valued point equivalence is natural as a homomorphism of actual subgroups. -/
theorem pointsEquiv_map {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme k L).X) :
    pointsEquiv k L T' (a ≫ x) =
      specialUnitaryMap (SpecialLinear.WeilRoot.tensorMap k L a) (tensorMap_bar k L a)
        (pointsEquiv k L T x) := by
  apply Subtype.ext
  apply Units.ext
  exact pointsEquiv_naturality k L a x

/-- The scalar unit in the actual tensor coefficients determined by a multiplicative point. -/
def scalarUnit (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Gm (Spec (CommRingCat.of k))).X) →*
      (SpecialLinear.WeilRoot.tensorAlgebra k L T)ˣ :=
  (Units.map (SpecialLinear.WeilRoot.includeSections k L T).toMonoidHom).comp
    (Gm.pointsEquiv (Spec (CommRingCat.of k)) T).toMonoidHom

@[simp] theorem scalarUnit_bar (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    barUnit (coefficientInvolution k L T) (scalarUnit k L T x) = scalarUnit k L T x := by
  apply Units.ext
  exact sectionToTensor_bar k L T _

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Included scalar units commute with all actual test restrictions. -/
theorem scalarUnit_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    scalarUnit k L T' (a ≫ x) =
      Units.map (SpecialLinear.WeilRoot.tensorMap k L a).toMonoidHom (scalarUnit k L T x) := by
  apply Units.ext
  simp only [scalarUnit, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Gm.pointsEquiv_naturality, Units.coe_map]
  exact (SpecialLinear.WeilRoot.tensorMap_includeSections k L a _).symm

/-- Diagonal special-unitary matrices on every actual test scheme. -/
def cocharacterPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Gm (Spec (CommRingCat.of k))).X) →* (T ⟶ (groupScheme k L).X) :=
  (pointsEquiv k L T).symm.toMonoidHom.comp
    ((diagonalSpecialUnitaryHom (coefficientInvolution k L T)).comp (scalarUnit k L T))

@[simp] theorem pointsEquiv_cocharacterPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    pointsEquiv k L T (cocharacterPoints k L T x) =
      diagonalSpecialUnitaryHom (coefficientInvolution k L T) (scalarUnit k L T x) :=
  (pointsEquiv k L T).apply_symm_apply _

/-- The diagonal parameterization respects every actual change of relative test scheme. -/
theorem cocharacterPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    cocharacterPoints k L T' (a ≫ x) = a ≫ cocharacterPoints k L T x := by
  apply (pointsEquiv k L T').injective
  rw [pointsEquiv_cocharacterPoints, pointsEquiv_map, pointsEquiv_cocharacterPoints,
    specialUnitaryMap_diagonal, scalarUnit_naturality]

/-- The actual ground-field split diagonal cocharacter of the special unitary scheme. -/
def cocharacter : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme k L :=
  homOfPoints (cocharacterPoints k L) (cocharacterPoints_naturality k L)

/-- The constructed cocharacter has the prescribed actual diagonal matrix on every test. -/
theorem pointsEquiv_cocharacter {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    pointsEquiv k L T (x ≫ (cocharacter k L).hom.hom) =
      diagonalSpecialUnitaryHom (coefficientInvolution k L T) (scalarUnit k L T x) := by
  rw [cocharacter, comp_homOfPoints, pointsEquiv_cocharacterPoints]

/-- Ground scalars give exactly the diagonal entries `(t,1,t^-1)`. -/
theorem pointsEquiv_cocharacter_val {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ((pointsEquiv k L T (x ≫ (cocharacter k L).hom.hom)).1 :
      Matrix (Fin 3) (Fin 3) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
        !![(scalarUnit k L T x : SpecialLinear.WeilRoot.tensorAlgebra k L T), 0, 0;
          0, 1, 0; 0, 0, ((scalarUnit k L T x)⁻¹ :
            (SpecialLinear.WeilRoot.tensorAlgebra k L T)ˣ)] := by
  rw [pointsEquiv_cocharacter]
  change (diagonal (coefficientInvolution k L T) (scalarUnit k L T x) :
    Matrix (Fin 3) (Fin 3) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) = _
  rw [diagonal_val, scalarUnit_bar, mul_inv_cancel]
  rfl

end SchemeModel
end Langlands.GroupScheme.SU3Root
