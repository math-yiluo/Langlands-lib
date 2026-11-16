import Langlands.GroupScheme.IsomorphismScheme
import Langlands.GroupScheme.ActionFibre
import Langlands.AlgebraicGeometry.FiniteGenericSection

/-! # Supplied outer-isomorphism quotients and their actual fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A supplied fpqc outer-class morphism with exact all-test inner orbits.
The action on isomorphisms is the canonical inverse-precomposition action. -/
structure OuterIsomorphismScheme {S : Scheme.{u}} {G H A : GroupScheme S}
    (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G) where
  parameter : Over S
  classMap : I.parameter ⟶ parameter
  flat : Flat classMap.left
  surjective : Surjective classMap.left
  quasiCompact : QuasiCompact classMap.left
  invariant : ∀ (T : Over S) (d : T ⟶ A.X) (p : T ⟶ I.parameter),
    (lift d p ≫ I.actionHom a) ≫ classMap = p ≫ classMap
  orbit : ∀ (T : Over S) (p q : T ⟶ I.parameter),
    p ≫ classMap = q ≫ classMap →
      ∃! (d : T ⟶ A.X), lift d p ≫ I.actionHom a = q

attribute [instance] OuterIsomorphismScheme.flat
  OuterIsomorphismScheme.surjective OuterIsomorphismScheme.quasiCompact

namespace OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a) (s : Over.mk (𝟙 S) ⟶ O.parameter)

/-- The actual scheme of isomorphisms in a specified integral outer class. -/
def fibre : Over S :=
  ActionFibre.parameter O.classMap s

/-- The actual inclusion into the supplied isomorphism scheme. -/
def fibreProjection : O.fibre s ⟶ I.parameter :=
  ActionFibre.projection O.classMap s

/-- The canonical inverse-precomposition action restricted to an outer class. -/
@[instance_reducible]
def fibreModObj : ModObj A.X (O.fibre s) :=
  letI := I.modObj a
  ActionFibre.modObj O.classMap s A O.invariant

instance : Flat (O.fibre s).hom := by
  unfold fibre
  infer_instance

instance : Surjective (O.fibre s).hom := by
  unfold fibre
  infer_instance

instance : QuasiCompact (O.fibre s).hom := by
  unfold fibre
  infer_instance

/-- The restricted action's actual shear is an isomorphism. -/
theorem fibreShear :
    letI := O.fibreModObj s
    IsIso (ModObj.leftSMul A.X (O.fibre s)) := by
  let := I.modObj a
  exact ActionFibre.leftSMul_isIso O.classMap s A O.invariant O.orbit

/-- Projection from the outer fibre respects the canonical action. -/
theorem fibre_smul_projection {T : Over S} (d : T ⟶ A.X)
    (p : T ⟶ O.fibre s) :
    letI := O.fibreModObj s
    (d • p) ≫ O.fibreProjection s =
      lift d (p ≫ O.fibreProjection s) ≫ I.actionHom a := by
  let := I.modObj a
  exact ActionFibre.smul_projection O.classMap s A O.invariant d p

/-- The universal isomorphism restricted to the actual outer fibre. -/
def fibreLocalIso : LocalGroupIso G H (O.fibre s) :=
  I.universalIso.refine (O.fibreProjection s)

/-- The fibre's universal family has the required inverse-precomposition law. -/
theorem fibreLocalIso_smul {T : Over S} (d : T ⟶ A.X)
    (p : T ⟶ O.fibre s) (g : T ⟶ G.X) :
    letI := O.fibreModObj s
    (O.fibreLocalIso s).toFun (d • p) g =
      (O.fibreLocalIso s).toFun p (a.act d⁻¹ g) := by
  let := O.fibreModObj s
  change I.universalIso.toFun ((d • p) ≫ O.fibreProjection s) g =
    I.universalIso.toFun (p ≫ O.fibreProjection s) (a.act d⁻¹ g)
  rw [O.fibre_smul_projection]
  exact I.actionHom_eval a d (p ≫ O.fibreProjection s) g

/-- An actual isomorphism point with the specified class lifts to the fibre. -/
def fibrePoint {T : Over S} (p : T ⟶ I.parameter)
    (hp : p ≫ O.classMap = toUnit T ≫ s) : T ⟶ O.fibre s :=
  ActionFibre.pointLift O.classMap s p hp

/-- Lifting to the outer fibre retains the exact universal isomorphism. -/
theorem fibreLocalIso_refine_fibrePoint {T : Over S} (p : T ⟶ I.parameter)
    (hp : p ≫ O.classMap = toUnit T ≫ s) :
    (O.fibreLocalIso s).refine (O.fibrePoint s p hp) = I.universalIso.refine p := by
  apply LocalGroupIso.ext_toFun
  intro W t g
  change I.universalIso.toFun
    ((t ≫ O.fibrePoint s p hp) ≫ O.fibreProjection s) g =
      I.universalIso.toFun (t ≫ p) g
  rw [Category.assoc]
  change I.universalIso.toFun
    (t ≫ (ActionFibre.pointLift O.classMap s p hp ≫
      ActionFibre.projection O.classMap s)) g = _
  rw [ActionFibre.pointLift_projection]

end OuterIsomorphismScheme

/-- A finite relative scheme containing the outer class of a specified point.
Only this component is required finite, not the whole isomorphism scheme. -/
structure FiniteGenericOuterClass {S : Scheme.{u}} {G H A : GroupScheme S}
    {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
    (O : OuterIsomorphismScheme I a) {T : Over S} (p : T ⟶ I.parameter) where
  component : Over S
  [finite : IsFinite component.hom]
  classMap : component ⟶ O.parameter
  genericPoint : T ⟶ component
  generic_class : genericPoint ≫ classMap = p ≫ O.classMap

attribute [instance] FiniteGenericOuterClass.finite

namespace FiniteGenericOuterClass

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G H A : GroupScheme (Spec (CommRingCat.of R))}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  {O : OuterIsomorphismScheme I a}
  {p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter}
  (C : FiniteGenericOuterClass O p)

/-- Extend the specified finite-component point and take its outer class. -/
def integralClass : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ O.parameter :=
  Langlands.AlgebraicGeometry.finiteGenericSection R K C.component C.genericPoint ≫
    C.classMap

/-- The integral outer class retains the class of the prescribed generic point. -/
theorem integralClass_generic :
    toUnit (Over.mk (Spec.algebraMap R K)) ≫ C.integralClass = p ≫ O.classMap := by
  change (Over.homMk (Spec.algebraMap R K) : Over.mk (Spec.algebraMap R K) ⟶
    Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫
      (Langlands.AlgebraicGeometry.finiteGenericSection R K C.component C.genericPoint ≫
        C.classMap) = _
  rw [← Category.assoc, Langlands.AlgebraicGeometry.finiteGenericSection_generic,
    C.generic_class]

/-- The prescribed generic isomorphism point belongs to the integral outer fibre. -/
def genericFibrePoint : Over.mk (Spec.algebraMap R K) ⟶ O.fibre C.integralClass :=
  O.fibrePoint C.integralClass p C.integralClass_generic.symm

/-- Evaluation at the constructed generic fibre point retains the original family. -/
theorem genericFibrePoint_localIso :
    (O.fibreLocalIso C.integralClass).refine C.genericFibrePoint =
      I.universalIso.refine p :=
  O.fibreLocalIso_refine_fibrePoint C.integralClass p C.integralClass_generic.symm

end FiniteGenericOuterClass

end Langlands.GroupScheme
