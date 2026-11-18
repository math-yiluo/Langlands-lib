import Langlands.AlgebraicGeometry.NormalStalkValuationSubring

/-! # The algebra of rational functions regular at a set of points -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- The intersection in the function field of the local rings at `E`. -/
def stalkIntersection (X : Scheme.{u}) [IsIntegral X] (E : Set X) :
    Subring X.functionField :=
  ⨅ x : E, stalkImageSubring X x

theorem mem_stalkIntersection {E : Set X} {a : X.functionField} :
    a ∈ stalkIntersection X E ↔ ∀ x ∈ E, a ∈ stalkImageSubring X x := by
  simp only [stalkIntersection, Subring.mem_iInf, Subtype.forall]

/-- The canonical map from the intersection to any selected stalk. -/
def stalkIntersectionToStalk (E : Set X) (x : X) (hx : x ∈ E) :
    stalkIntersection X E →+* X.presheaf.stalk x :=
  (stalkEquivImage X x).symm.toRingHom.comp
    (Subring.inclusion (iInf_le (fun y : E ↦ stalkImageSubring X y) ⟨x, hx⟩))

@[simp]
theorem algebraMap_stalkIntersectionToStalk (E : Set X) (x : X) (hx : x ∈ E)
    (a : stalkIntersection X E) :
    algebraMap (X.presheaf.stalk x) X.functionField
        (stalkIntersectionToStalk E x hx a) = a := by
  exact algebraMap_stalkEquivImage_symm X x _

theorem stalkIntersectionToStalk_field_comp (E : Set X) (x : X) (hx : x ∈ E) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp
        (stalkIntersectionToStalk E x hx) = (stalkIntersection X E).subtype := by
  ext a
  exact algebraMap_stalkIntersectionToStalk E x hx a

section Base

variable {R : Type u} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R))

/-- The base ring acts on every stalk through the structure morphism. -/
def baseToStalk (x : X) : R →+* X.presheaf.stalk x :=
  (Spec.preimage (X.fromSpecStalk x ≫ p)).hom

omit [IsIntegral X] in
@[simp]
theorem specMap_baseToStalk (x : X) :
    Spec.map (CommRingCat.ofHom (baseToStalk p x)) = X.fromSpecStalk x ≫ p :=
  Spec.map_preimage _

/-- The map from the base into the scheme's function field. -/
def baseToFunctionField : R →+* X.functionField :=
  baseToStalk p (genericPoint X)

set_option backward.isDefEq.respectTransparency false in
theorem baseToStalk_field_comp (x : X) :
    (algebraMap (X.presheaf.stalk x) X.functionField).comp (baseToStalk p x) =
      baseToFunctionField p := by
  apply_fun fun k : R →+* X.functionField ↦ CommRingCat.ofHom k
  · apply Spec.map_injective
    dsimp only
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_baseToStalk,
      ← Category.assoc]
    change Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
        X.fromSpecStalk x ≫ p =
      Spec.map (CommRingCat.ofHom (baseToStalk p (genericPoint X)))
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, specMap_baseToStalk]
  · intro f g h
    exact congrArg CommRingCat.Hom.hom h

/-- The base ring maps into the intersection, with no finiteness requirement
on the selected set. -/
def baseToStalkIntersection (E : Set X) : R →+* stalkIntersection X E :=
  (baseToFunctionField p).codRestrict (stalkIntersection X E) fun a ↦
    mem_stalkIntersection.mpr fun x _hx ↦
      ⟨baseToStalk p x a,
        congrArg (fun k : R →+* X.functionField ↦ k a) (baseToStalk_field_comp p x)⟩

/-- The intersection with its canonical algebra structure over the base. -/
@[instance_reducible]
def stalkIntersectionAlgebra (E : Set X) : Algebra R (stalkIntersection X E) :=
  (baseToStalkIntersection p E).toAlgebra

@[simp]
theorem subtype_baseToStalkIntersection (E : Set X) :
    (stalkIntersection X E).subtype.comp (baseToStalkIntersection p E) =
      baseToFunctionField p := rfl

set_option backward.isDefEq.respectTransparency false in
theorem stalkIntersection_generic_over (E : Set X) :
    Spec.map (CommRingCat.ofHom (stalkIntersection X E).subtype) ≫
        Spec.map (CommRingCat.ofHom (baseToStalkIntersection p E)) =
      X.fromSpecStalk (genericPoint X) ≫ p := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, subtype_baseToStalkIntersection]
  exact specMap_baseToStalk p _

end Base

@[simp]
theorem stalkIntersection_empty :
    stalkIntersection X ∅ = ⊤ := by
  ext a
  simp [mem_stalkIntersection]

/-- The generic point imposes no condition on rational functions. -/
theorem stalkIntersection_diff_genericPoint (E : Set X) :
    stalkIntersection X (E \ {genericPoint X}) = stalkIntersection X E := by
  ext a
  simp only [mem_stalkIntersection]
  constructor
  · intro h x hx
    by_cases hη : x = genericPoint X
    · subst x
      rw [stalkImageSubring_genericPoint]
      trivial
    · exact h x ⟨hx, hη⟩
  · intro h x hx
    exact h x hx.1

end Langlands.AlgebraicGeometry
