import Langlands.AlgebraicGeometry.Picard.StalkDerivationTangent
import Langlands.AlgebraicGeometry.Picard.RigidifiedDualNumber
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # Addition of actual tangent maps at the identity of a monoid object -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.GeneralLinear.DualNumber
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace DualNumberDouble

variable (k : Type u) [Field k]

/-- The double dual-number ring is local because its units are detected by the
first projection to the local dual-number ring. -/
instance doubleIsLocalRing : IsLocalRing (DualNumber (DualNumber k)) where
  isUnit_or_isUnit_of_add_one h := by
    have h' := congrArg TrivSqZeroExt.fst h
    change _ + _ = (1 : DualNumber k) at h'
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one h').imp
      TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr

/-- The inclusion of the first infinitesimal parameter. -/
def first : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  TrivSqZeroExt.inlAlgHom k (DualNumber k) (DualNumber k)

/-- The inclusion of the second infinitesimal parameter. -/
def second : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  coefficientAlgMap (R := CommRingCat.of k) (TrivSqZeroExt.inlAlgHom k k k)

/-- Set the second infinitesimal parameter to zero. -/
def leftAxis : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  TrivSqZeroExt.fstHom k (DualNumber k) (DualNumber k)

/-- Set the first infinitesimal parameter to zero. -/
def rightAxis : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  coefficientAlgMap (R := CommRingCat.of k) (TrivSqZeroExt.fstHom k k k)

/-- Set both infinitesimal parameters equal to epsilon. -/
def fold : DualNumber (DualNumber k) →ₐ[k] DualNumber k where
  toFun z := (z.fst.fst, z.fst.snd + z.snd.fst)
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (a.fst.snd + b.fst.snd) + (a.snd.fst + b.snd.fst) =
        (a.fst.snd + a.snd.fst) + (b.fst.snd + b.snd.fst)
      abel
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (a.fst.fst * b.fst.snd + a.fst.snd * b.fst.fst) +
          (a.fst.fst * b.snd.fst + a.snd.fst * b.fst.fst) =
        a.fst.fst * (b.fst.snd + b.snd.fst) +
          (a.fst.snd + a.snd.fst) * b.fst.fst
      ring
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (0 : k) + 0 = 0
      exact add_zero _

@[simp] lemma first_apply (z : DualNumber k) :
    first k z = TrivSqZeroExt.inl z := rfl

@[simp] lemma second_apply (z : DualNumber k) :
    second k z = (TrivSqZeroExt.inl z.fst, TrivSqZeroExt.inl z.snd) := rfl

@[simp] lemma leftAxis_apply (z : DualNumber (DualNumber k)) :
    leftAxis k z = z.fst := rfl

@[simp] lemma rightAxis_apply (z : DualNumber (DualNumber k)) :
    rightAxis k z = (z.fst.fst, z.snd.fst) := rfl

@[simp] lemma fold_apply (z : DualNumber (DualNumber k)) :
    fold k z = (z.fst.fst, z.fst.snd + z.snd.fst) := rfl

variable {k}

/-- An algebra homomorphism induces its actual morphism in the slice over `Spec k`. -/
def specOverMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) :
    Over.mk (Spec.algebraMap k B) ⟶ Over.mk (Spec.algebraMap k A) :=
  Over.homMk (Spec.homEquivAlgHom.symm φ).val (Spec.homEquivAlgHom.symm φ).property

@[simp]
lemma specOverMap_left {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B) :
    (specOverMap φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

variable (k)

/-- The actual double dual-number test, with the independent two parameters and their product. -/
def test : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.algebraMap k (DualNumber (DualNumber k)))

def fst : test k ⟶ dualNumberTest k := specOverMap (first k)

def snd : test k ⟶ dualNumberTest k := specOverMap (second k)

def inl : dualNumberTest k ⟶ test k := specOverMap (leftAxis k)

def inr : dualNumberTest k ⟶ test k := specOverMap (rightAxis k)

def diagonal : dualNumberTest k ⟶ test k := specOverMap (fold k)

@[simp]
lemma inl_fst : inl k ≫ fst k = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  rfl

@[simp]
lemma inr_snd : inr k ≫ snd k = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  rfl

@[simp]
lemma diagonal_fst : diagonal k ≫ fst k = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change fold k (first k z) = z
  apply TrivSqZeroExt.ext <;> simp

@[simp]
lemma diagonal_snd : diagonal k ≫ snd k = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change fold k (second k z) = z
  apply TrivSqZeroExt.ext <;> simp

/-- The structure map of the dual-number test as a morphism in the slice. -/
def toBase : dualNumberTest k ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (dualNumberProjection k) (Category.comp_id _)

@[simp]
lemma inl_snd : inl k ≫ snd k = toBase k ≫ dualNumberClosedPoint k := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

@[simp]
lemma inr_fst : inr k ≫ fst k = toBase k ≫ dualNumberClosedPoint k := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- An axis inclusion carries the closed point to the double test's closed point. -/
lemma inl_closedPoint :
    (inl k).left (IsLocalRing.closedPoint (DualNumber k)) =
      IsLocalRing.closedPoint (DualNumber (DualNumber k)) := by
  let : IsLocalHom (leftAxis k).toRingHom :=
    ⟨fun _ h ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h⟩
  exact Spec_closedPoint (f := (CommRingCat.ofHom (leftAxis k).toRingHom :
    CommRingCat.of (DualNumber (DualNumber k)) ⟶ CommRingCat.of (DualNumber k)))

variable {k} {A : Type u} [CommRing A] [Algebra k A]

/-- The diagonal's epsilon coefficient is the sum of the two axis coefficients. -/
lemma fold_comp_eq_lift (r : A →ₐ[k] k) :
    letI := r.toRingHom.toAlgebra
    ∀ (D E : Derivation k A k) (φ : A →+* DualNumber (DualNumber k)),
      (leftAxis k).toRingHom.comp φ = (derivationDualNumberLift r D).toRingHom →
      (rightAxis k).toRingHom.comp φ = (derivationDualNumberLift r E).toRingHom →
      (fold k).toRingHom.comp φ = (derivationDualNumberLift r (D + E)).toRingHom := by
  let := r.toRingHom.toAlgebra
  intro D E φ hD hE
  apply RingHom.ext
  intro a
  have h₀ := congrArg TrivSqZeroExt.fst (RingHom.congr_fun hD a)
  have h₁ := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hD a)
  have h₂ := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hE a)
  apply TrivSqZeroExt.ext
  · exact h₀
  · change (φ a).fst.snd + (φ a).snd.fst = D a + E a
    exact congrArg₂ (· + ·) h₁ h₂

end DualNumberDouble

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A double infinitesimal map with prescribed axes has the sum derivation on
the diagonal. This concerns actual scheme morphisms and the actual point stalk. -/
lemma tangent_diagonal_eq_add (p : X ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
    ∀ (D E : Derivation k (X.presheaf.stalk (x (IsLocalRing.closedPoint k))) k)
      (F : (DualNumberDouble.test k).left ⟶ X),
      (DualNumberDouble.inl k).left ≫ F =
        (rationalStalkDerivationTangentEquiv p x hx D).val →
      (DualNumberDouble.inr k).left ≫ F =
        (rationalStalkDerivationTangentEquiv p x hx E).val →
      (DualNumberDouble.diagonal k).left ≫ F =
        (rationalStalkDerivationTangentEquiv p x hx (D + E)).val := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation p x hx).toRingHom.toAlgebra
  intro D E F hD hE
  have hpoint : F (IsLocalRing.closedPoint (DualNumber (DualNumber k))) =
      x (IsLocalRing.closedPoint k) := by
    rw [← DualNumberDouble.inl_closedPoint k]
    have h := congrArg (fun t : Spec (CommRingCat.of (DualNumber k)) ⟶ X ↦
      t (IsLocalRing.closedPoint (DualNumber k))) hD
    exact h.trans (rationalStalkDerivationTangentEquiv p x hx D).property.closedPoint
  obtain ⟨φ, hφ⟩ : ∃ φ : X.presheaf.stalk (x (IsLocalRing.closedPoint k)) ⟶
      CommRingCat.of (DualNumber (DualNumber k)),
      Spec.map φ ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint k)) = F := by
    rw [← hpoint]
    exact ⟨Scheme.stalkClosedPointTo F, Scheme.Spec_stalkClosedPointTo_fromSpecStalk F⟩
  have hD' : (DualNumberDouble.leftAxis k).toRingHom.comp φ.hom =
      (derivationDualNumberLift (rationalStalkAugmentation p x hx) D).toRingHom := by
    rw [← hφ, rationalStalkDerivationTangentEquiv_apply_val,
      ← Category.assoc] at hD
    have h := (cancel_mono (X.fromSpecStalk (x (IsLocalRing.closedPoint k)))).mp hD
    change Spec.map _ ≫ Spec.map _ = Spec.map _ at h
    rw [← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hE' : (DualNumberDouble.rightAxis k).toRingHom.comp φ.hom =
      (derivationDualNumberLift (rationalStalkAugmentation p x hx) E).toRingHom := by
    rw [← hφ, rationalStalkDerivationTangentEquiv_apply_val,
      ← Category.assoc] at hE
    have h := (cancel_mono (X.fromSpecStalk (x (IsLocalRing.closedPoint k)))).mp hE
    change Spec.map _ ≫ Spec.map _ = Spec.map _ at h
    rw [← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hfold := DualNumberDouble.fold_comp_eq_lift
    (rationalStalkAugmentation p x hx) D E φ.hom hD' hE'
  rw [← hφ, rationalStalkDerivationTangentEquiv_apply_val, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext hfold

/-- The slice-valued infinitesimal point defined by a rational stalk derivation. -/
def rationalStalkDerivationPoint (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) :
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    Derivation k (P.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) k →
      (dualNumberTest k ⟶ P) := by
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  intro D
  exact Over.homMk
    (rationalStalkDerivationTangentEquiv P.hom e.left (Over.w e) D).val
    (rationalStalkDerivationTangentEquiv P.hom e.left (Over.w e) D).property.1

@[simp]
lemma rationalStalkDerivationPoint_left (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) :
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    ∀ D, (rationalStalkDerivationPoint P e D).left =
      (rationalStalkDerivationTangentEquiv P.hom e.left (Over.w e) D).val := by
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  intro D
  rfl

@[simp]
lemma rationalStalkDerivationPoint_closedPoint (P : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P) :
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    ∀ D, dualNumberClosedPoint k ≫ rationalStalkDerivationPoint P e D = e := by
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  intro D
  apply Over.OverMorphism.ext
  exact (rationalStalkDerivationTangentEquiv P.hom e.left (Over.w e) D).property.2

/-- Addition on the actual identity stalk is multiplication of actual
dual-number points for every monoid scheme over the field. -/
lemma rationalStalkDerivationPoint_add (P : Over (Spec (CommRingCat.of k))) [MonObj P] :
    let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P := 1
    letI := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
    ∀ D E, rationalStalkDerivationPoint P e (D + E) =
      rationalStalkDerivationPoint P e D * rationalStalkDerivationPoint P e E := by
  let e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P := 1
  let := stalkAlgebraOver P.hom (e.left (IsLocalRing.closedPoint k))
  let := (rationalStalkAugmentation P.hom e.left (Over.w e)).toRingHom.toAlgebra
  change ∀ D E, rationalStalkDerivationPoint P e (D + E) =
    rationalStalkDerivationPoint P e D * rationalStalkDerivationPoint P e E
  intro D E
  let t := rationalStalkDerivationPoint P e D
  let s := rationalStalkDerivationPoint P e E
  let F : DualNumberDouble.test k ⟶ P :=
    (DualNumberDouble.fst k ≫ t) * (DualNumberDouble.snd k ≫ s)
  have ht : dualNumberClosedPoint k ≫ t = 1 :=
    rationalStalkDerivationPoint_closedPoint P e D
  have hs : dualNumberClosedPoint k ≫ s = 1 :=
    rationalStalkDerivationPoint_closedPoint P e E
  have hleft : DualNumberDouble.inl k ≫ F = t := by
    dsimp only [F]
    rw [MonObj.comp_mul, ← Category.assoc, DualNumberDouble.inl_fst,
      Category.id_comp, ← Category.assoc, DualNumberDouble.inl_snd,
      Category.assoc, hs, MonObj.comp_one, mul_one]
  have hright : DualNumberDouble.inr k ≫ F = s := by
    dsimp only [F]
    rw [MonObj.comp_mul, ← Category.assoc, DualNumberDouble.inr_fst,
      Category.assoc, ht, MonObj.comp_one, ← Category.assoc,
      DualNumberDouble.inr_snd, Category.id_comp, one_mul]
  have hdiag : DualNumberDouble.diagonal k ≫ F = t * s := by
    dsimp only [F]
    rw [MonObj.comp_mul, ← Category.assoc, DualNumberDouble.diagonal_fst,
      Category.id_comp, ← Category.assoc, DualNumberDouble.diagonal_snd,
      Category.id_comp]
  have hsum := tangent_diagonal_eq_add P.hom e.left (Over.w e) D E F.left
    (congrArg (fun g ↦ g.left) hleft) (congrArg (fun g ↦ g.left) hright)
  apply Over.OverMorphism.ext
  exact hsum.symm.trans (congrArg (fun g ↦ g.left) hdiag)

end Langlands.AlgebraicGeometry.Picard
