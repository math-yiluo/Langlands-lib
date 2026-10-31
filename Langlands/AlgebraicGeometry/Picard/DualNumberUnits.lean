import Langlands.GroupScheme.GeneralLinearDualNumber
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.Forget

/-! # Units reducing to one in split dual-number section rings -/

universe u v

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.DualNumberUnits

namespace MatrixCoordinates

open Langlands.GroupScheme.GeneralLinear

variable {R : Type u} [CommRing R]

/-- The existing matrix-unit construction in rank one, evaluated as a scalar unit. -/
def unit (a : R) : (DualNumber R)ˣ :=
  Units.mapEquiv (Matrix.uniqueRingEquiv (m := PUnit.{1})
    (A := DualNumber R)).toMulEquiv
      (DualNumber.matrixUnit (fun _ _ : PUnit.{1} ↦ a))

@[simp]
lemma unit_val (a : R) : (unit a : DualNumber R) = 1 + TrivSqZeroExt.inr a := by
  change (1 : Matrix PUnit.{1} PUnit.{1} (DualNumber R)) default default +
    TrivSqZeroExt.inr a = _
  simp

lemma unit_add (a b : R) : unit (a + b) = unit a * unit b := by
  let X : Matrix PUnit.{1} PUnit.{1} R := fun _ _ ↦ a
  let Y : Matrix PUnit.{1} PUnit.{1} R := fun _ _ ↦ b
  let e := Units.mapEquiv
    (Matrix.uniqueRingEquiv (m := PUnit.{1}) (A := DualNumber R)).toMulEquiv
  change e (DualNumber.matrixUnit (X + Y)) =
    e (DualNumber.matrixUnit X) * e (DualNumber.matrixUnit Y)
  rw [DualNumber.matrixUnit_add, map_mul]

end MatrixCoordinates

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Reduction of actual scalar units modulo epsilon. -/
def reduction (R : Type u) [CommRing R] : (DualNumber R)ˣ →* Rˣ :=
  Units.map (TrivSqZeroExt.fstHom R R R).toMonoidHom

/-- The actual multiplicative kernel of reduction, rather than chosen coefficients. -/
abbrev Kernel (R : Type u) [CommRing R] := (reduction R).ker

lemma fst_eq_one (g : Kernel R) : (g.val : DualNumber R).fst = 1 :=
  congrArg (fun h : Rˣ ↦ (h : R)) g.property

@[simp]
lemma reduction_unit (a : R) : reduction R (MatrixCoordinates.unit a) = 1 := by
  apply Units.ext
  change (MatrixCoordinates.unit a : DualNumber R).fst = 1
  simp

lemma unit_snd (g : Kernel R) :
    MatrixCoordinates.unit (g.val : DualNumber R).snd = g.val := by
  apply Units.ext
  apply TrivSqZeroExt.ext
  · simpa using (fst_eq_one g).symm
  · simp

/-- The additive coefficient group is the multiplicative reduction kernel. -/
def kernelEquiv : Multiplicative R ≃* Kernel R where
  toFun a := ⟨MatrixCoordinates.unit a.toAdd, reduction_unit a.toAdd⟩
  invFun g := Multiplicative.ofAdd (g.val : DualNumber R).snd
  left_inv a := by
    change Multiplicative.ofAdd
      (MatrixCoordinates.unit a.toAdd : DualNumber R).snd = a
    simp
  right_inv g := Subtype.ext (unit_snd g)
  map_mul' a b := Subtype.ext (MatrixCoordinates.unit_add a.toAdd b.toAdd)

@[simp]
lemma kernelEquiv_val (a : Multiplicative R) :
    ((kernelEquiv a).val : DualNumber R) = 1 + TrivSqZeroExt.inr a.toAdd :=
  MatrixCoordinates.unit_val a.toAdd

namespace Coordinates

open Langlands.GroupScheme.GeneralLinear.DualNumber

lemma unit_map (f : R →+* S) (a : R) :
    Units.map (coefficientMap f).toMonoidHom (MatrixCoordinates.unit a) =
      MatrixCoordinates.unit (f a) := by
  apply Units.ext
  change coefficientMap f (MatrixCoordinates.unit a : DualNumber R) = _
  rw [MatrixCoordinates.unit_val, map_add, map_one, coefficientMap_inr,
    MatrixCoordinates.unit_val]

lemma unit_scale (r a : R) :
    Units.map (epsilonScale r).toMonoidHom (MatrixCoordinates.unit a) =
      MatrixCoordinates.unit (r * a) := by
  apply Units.ext
  apply TrivSqZeroExt.ext <;> simp [MatrixCoordinates.unit_val, mul_comm]

/-- Coefficient change on the actual unit kernel. -/
def kernelMap (f : R →+* S) : Kernel R →* Kernel S where
  toFun g := ⟨Units.map (coefficientMap f).toMonoidHom g.val, by
    apply Units.ext
    change f (g.val : DualNumber R).fst = 1
    rw [fst_eq_one, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

@[simp]
lemma kernelMap_equiv (f : R →+* S) (a : R) :
    kernelMap f (kernelEquiv (Multiplicative.ofAdd a)) =
      kernelEquiv (Multiplicative.ofAdd (f a)) :=
  Subtype.ext (unit_map f a)

lemma kernelMap_id (g : Kernel R) : kernelMap (RingHom.id R) g = g := by
  apply Subtype.ext
  apply Units.ext
  apply TrivSqZeroExt.ext <;> rfl

lemma kernelMap_comp {T : Type*} [CommRing T] (f : R →+* S) (h : S →+* T)
    (g : Kernel R) :
    kernelMap (h.comp f) g = kernelMap h (kernelMap f g) := by
  apply Subtype.ext
  apply Units.ext
  apply TrivSqZeroExt.ext <;> rfl

/-- Epsilon scaling on units, for an arbitrary scalar including zero. -/
def kernelScale (r : R) : Kernel R →* Kernel R where
  toFun g := ⟨Units.map (epsilonScale r).toMonoidHom g.val, by
    apply Units.ext
    change (epsilonScale r (g.val : DualNumber R)).fst = 1
    rw [epsilonScale_fst, fst_eq_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

@[simp]
lemma kernelScale_equiv (r a : R) :
    kernelScale r (kernelEquiv (Multiplicative.ofAdd a)) =
      kernelEquiv (Multiplicative.ofAdd (r * a)) :=
  Subtype.ext (unit_scale r a)

end Coordinates

/-- The same equivalence in additive notation, for sheaves of abelian groups. -/
def kernelAddEquiv : R ≃+ Additive (Kernel R) where
  toFun a := Additive.ofMul (kernelEquiv (Multiplicative.ofAdd a))
  invFun g := (kernelEquiv.symm g.toMul).toAdd
  left_inv a := congrArg Multiplicative.toAdd
    (kernelEquiv.left_inv (Multiplicative.ofAdd a))
  right_inv g := congrArg Additive.ofMul (kernelEquiv.right_inv g.toMul)
  map_add' a b := congrArg Additive.ofMul
    (kernelEquiv.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

/-- The reduction kernels form a functor on commutative rings. -/
def kernelFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} where
  obj R := AddCommGrpCat.of (Additive (Kernel R))
  map f := AddCommGrpCat.ofHom (Coordinates.kernelMap f.hom).toAdditive
  map_id R := by
    apply AddCommGrpCat.ext
    intro g
    change Additive.ofMul (Coordinates.kernelMap (RingHom.id R) g.toMul) = g
    exact congrArg Additive.ofMul (Coordinates.kernelMap_id (R := R) g.toMul)
  map_comp {R S T} f h := by
    apply AddCommGrpCat.ext
    intro g
    change Additive.ofMul (Coordinates.kernelMap (h.hom.comp f.hom) g.toMul) =
      Additive.ofMul (Coordinates.kernelMap h.hom (Coordinates.kernelMap f.hom g.toMul))
    exact congrArg Additive.ofMul
      (Coordinates.kernelMap_comp (R := R) (S := S) f.hom h.hom g.toMul)

/-- The additive underlying group, using the existing forgetful functors. -/
abbrev ringAdditiveFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The additive underlying group is naturally the split unit reduction kernel. -/
def kernelFunctorIso :
    ringAdditiveFunctor.{u} ≅ kernelFunctor :=
  NatIso.ofComponents (fun R ↦
    { hom := AddCommGrpCat.ofHom (kernelAddEquiv (R := R)).toAddMonoidHom
      inv := AddCommGrpCat.ofHom (kernelAddEquiv (R := R)).symm.toAddMonoidHom
      hom_inv_id := by
        apply AddCommGrpCat.ext
        intro a
        exact (kernelAddEquiv (R := R)).left_inv a
      inv_hom_id := by
        apply AddCommGrpCat.ext
        intro g
        exact (kernelAddEquiv (R := R)).right_inv g }) (by
    intro R S f
    ext a
    exact congrArg Additive.ofMul (Coordinates.kernelMap_equiv f.hom a).symm)

variable (X : Scheme.{u})

/-- Split dual-number unit kernels on each actual structure-sheaf section ring. -/
def kernelPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X :=
  X.presheaf ⋙ kernelFunctor

/-- Restriction-compatible coefficient description over all opens of a scheme. -/
def kernelPresheafIso :
    X.presheaf ⋙ ringAdditiveFunctor ≅ kernelPresheaf X :=
  Functor.isoWhiskerLeft X.presheaf kernelFunctorIso

/-- The split unit kernels satisfy the sheaf condition. -/
lemma kernelPresheaf_isSheaf : (kernelPresheaf X).IsSheaf := by
  apply TopCat.Presheaf.isSheaf_of_iso (kernelPresheafIso X)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  change TopCat.Presheaf.IsSheaf (X.presheaf ⋙ forget CommRingCat)
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget CommRingCat) X.presheaf).mp X.sheaf.property

/-- The sheaf of split dual-number unit kernels on a scheme. -/
def kernelSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨kernelPresheaf X, kernelPresheaf_isSheaf X⟩

end Langlands.AlgebraicGeometry.Picard.DualNumberUnits
