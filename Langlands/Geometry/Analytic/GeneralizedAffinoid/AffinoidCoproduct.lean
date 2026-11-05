import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Actual scalar presentation and bounded affinoid coproducts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The zero-variable closed quotient, with no defining relations. -/
def initialAlgebra : PresentedAffinoidAlgebra K :=
  ofRelations K 0 (PositivePolyradius.unit (Fin 0)) ∅

variable (E : Type v) [NormedCommRing E] [NormedAlgebra K E]

/-- No coordinates remain, so any two bounded maps from the scalar
presentation coincide, even without completeness of the target. -/
theorem initial_hom_ext (f g : BoundedAlgHom K (initialAlgebra K) E) : f = g := by
  apply hom_ext_coordinate K E (initialAlgebra K)
  intro i
  exact Fin.elim0 i

variable [IsUltrametricDist E] [CompleteSpace E]

/-- Evaluate the actual zero-variable relation quotient in any complete
ultrametric target; the bound allows a zero target or a non-normalized unit. -/
def initialMap : BoundedAlgHom K (initialAlgebra K) E :=
  evaluateRelations K E 0 (PositivePolyradius.unit (Fin 0)) ∅ Fin.elim0
    (by
      refine ⟨‖(1 : E)‖ + 1, by positivity, ?_⟩
      intro d
      have hd : d = 0 := Subsingleton.elim _ _
      simp [hd, StrictTateAlgebra.monomialValue])
    (by intro _ hf; exact False.elim hf)

variable [CompleteSpace K]

/-- The original coefficient field maps into its explicit scalar presentation. -/
def scalarInclusion : BoundedAlgHom K K (initialAlgebra K) where
  toAlgHom := Algebra.ofId K (initialAlgebra K)
  bounded := ⟨‖(1 : initialAlgebra K)‖ + 1, by positivity, fun c => by
    change ‖algebraMap K (initialAlgebra K) c‖ ≤
      (‖(1 : initialAlgebra K)‖ + 1) * ‖c‖
    rw [_root_.norm_algebraMap]
    nlinarith [norm_nonneg c]⟩

@[simp]
theorem initialMap_scalarInclusion (c : K) :
    initialMap K K (scalarInclusion K c) = c := by
  exact (initialMap K K).toAlgHom.commutes c

/-- A bounded algebra equivalence identifies the constructed scalar
presentation with the unchanged coefficient field. -/
def initialAlgebraEquiv : BoundedAlgEquiv K (initialAlgebra K) K :=
  BoundedAlgEquiv.ofHomInv (initialMap K K) (scalarInclusion K)
    (fun x => congrArg
      (fun f : BoundedAlgHom K (initialAlgebra K) (initialAlgebra K) => f x)
      (initial_hom_ext K (initialAlgebra K)
        ((scalarInclusion K).comp (initialMap K K))
        (BoundedAlgHom.id K (initialAlgebra K))))
    (initialMap_scalarInclusion K)

variable (A B : PresentedAffinoidAlgebra K)

/-- An actual finite closed weighted Tate quotient, formed by pushing
out over the constructed scalar presentation. -/
def algebra : PresentedAffinoidAlgebra K :=
  AffinoidPushout.algebra (initialMap K A) (initialMap K B)

/-- The bounded inclusion of the first original algebra. -/
def leftMap : BoundedAlgHom K A (algebra K A B) :=
  AffinoidPushout.leftMap (initialMap K A) (initialMap K B)

/-- The bounded inclusion of the second original algebra. -/
def rightMap : BoundedAlgHom K B (algebra K A B) :=
  AffinoidPushout.rightMap (initialMap K A) (initialMap K B)

theorem norm_leftMap_le (a : A) : ‖leftMap K A B a‖ ≤ ‖a‖ :=
  AffinoidPushout.norm_leftMap_le (initialMap K A) (initialMap K B) a

theorem norm_rightMap_le (b : B) : ‖rightMap K A B b‖ ≤ ‖b‖ :=
  AffinoidPushout.norm_rightMap_le (initialMap K A) (initialMap K B) b

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- Both complete algebra legs determine the entire bounded map. -/
theorem hom_ext (f g : BoundedAlgHom K (algebra K A B) E)
    (hl : f.comp (leftMap K A B) = g.comp (leftMap K A B))
    (hr : f.comp (rightMap K A B) = g.comp (rightMap K A B)) : f = g :=
  AffinoidPushout.hom_ext (initialMap K A) (initialMap K B) E f g hl hr

variable (α : BoundedAlgHom K A E) (β : BoundedAlgHom K B E)

/-- Any two bounded algebra maps agree over the scalar presentation, so
the previous bounded pushout constructs their absolute coproduct lift. -/
def lift : BoundedAlgHom K (algebra K A B) E :=
  AffinoidPushout.lift (initialMap K A) (initialMap K B) E α β
    (initial_hom_ext K E _ _)

@[simp]
theorem lift_comp_leftMap : (lift K E A B α β).comp (leftMap K A B) = α :=
  AffinoidPushout.lift_comp_leftMap (initialMap K A) (initialMap K B) E α β
    (initial_hom_ext K E _ _)

@[simp]
theorem lift_comp_rightMap : (lift K E A B α β).comp (rightMap K A B) = β :=
  AffinoidPushout.lift_comp_rightMap (initialMap K A) (initialMap K B) E α β
    (initial_hom_ext K E _ _)

/-- The full bounded-Hom universal property into arbitrary complete
ultrametric target algebras, whose universe is independent of K. -/
def boundedHomEquiv : BoundedAlgHom K (algebra K A B) E ≃
    (BoundedAlgHom K A E × BoundedAlgHom K B E) where
  toFun f := ⟨f.comp (leftMap K A B), f.comp (rightMap K A B)⟩
  invFun p := lift K E A B p.1 p.2
  left_inv _f := hom_ext K E A B _ _ (lift_comp_leftMap K E A B _ _)
    (lift_comp_rightMap K E A B _ _)
  right_inv p := Prod.ext (lift_comp_leftMap K E A B p.1 p.2)
    (lift_comp_rightMap K E A B p.1 p.2)

/-- On products of original elements the actual lift is multiplication of
their images, with no algebraic-tensor or reducedness assumption. -/
theorem lift_mul (a : A) (b : B) :
    lift K E A B α β (leftMap K A B a * rightMap K A B b) = α a * β b := by
  have hl := congrArg (fun f : BoundedAlgHom K A E => f a)
    (lift_comp_leftMap K E A B α β)
  have hr := congrArg (fun f : BoundedAlgHom K B E => f b)
    (lift_comp_rightMap K E A B α β)
  exact (map_mul (lift K E A B α β).toAlgHom _ _).trans (congrArg₂ (· * ·) hl hr)

variable {E}

/-- The diagonal algebra map has an explicitly constructed bounded section. -/
def diagonal : BoundedAlgHom K (algebra K A A) A :=
  lift K A A A (BoundedAlgHom.id K A) (BoundedAlgHom.id K A)

@[simp]
theorem diagonal_comp_leftMap :
    (diagonal K A).comp (leftMap K A A) = BoundedAlgHom.id K A :=
  lift_comp_leftMap K A A A _ _

@[simp]
theorem diagonal_comp_rightMap :
    (diagonal K A).comp (rightMap K A A) = BoundedAlgHom.id K A :=
  lift_comp_rightMap K A A A _ _

/-- Every original element has a diagonal preimage of no greater norm. -/
theorem diagonal_preimage (a : A) :
    ∃ z : algebra K A A, diagonal K A z = a ∧ ‖z‖ ≤ ‖a‖ := by
  refine ⟨leftMap K A A a, ?_, norm_leftMap_le K A A a⟩
  exact congrArg (fun f : BoundedAlgHom K A A => f a) (diagonal_comp_leftMap K A)

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct
