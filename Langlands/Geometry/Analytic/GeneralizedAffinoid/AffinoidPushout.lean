import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Embedding

/-! # Actual bounded pushouts of finite positive-radius affinoid presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B C : PresentedAffinoidAlgebra K}

/-- A series representative of an actual quotient element. -/
def representative (B : PresentedAffinoidAlgebra K) (b : B) :
    GeneralizedTateAlgebra B.polyradius K :=
  (presentationMap_surjective K B b).choose

@[simp]
theorem presentationMap_representative (B : PresentedAffinoidAlgebra K) (b : B) :
    presentationMap K B (representative B b) = b :=
  (presentationMap_surjective K B b).choose_spec

variable (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- Both old ideals and the equalities of all original coefficient classes. -/
def relations : Set (GeneralizedTateAlgebra (B.polyradius.append C.polyradius) K) :=
  (appendLeft B.polyradius C.polyradius K '' (B.ideal : Set _) ∪
    appendRight B.polyradius C.polyradius K '' (C.ideal : Set _)) ∪
    Set.range fun a : A =>
      appendLeft B.polyradius C.polyradius K (representative B (f a)) -
        appendRight B.polyradius C.polyradius K (representative C (g a))

/-- The actual closed quotient of the appended weighted Tate presentation. -/
def algebra : PresentedAffinoidAlgebra K :=
  ofRelations K (B.arity + C.arity) (B.polyradius.append C.polyradius) (relations f g)

/-- The first coordinate block descends through the original closed ideal. -/
def leftMap : BoundedAlgHom K B (algebra f g) := by
  let q := (presentationMap K (algebra f g)).comp
    (appendLeft B.polyradius C.polyradius K)
  have hq : ∀ p ∈ B.ideal, q p = 0 := by
    intro p hp
    exact presentationMap_relation K _ _ (relations f g)
      (Set.mem_union_left _ (Set.mem_union_left _ ⟨p, hp, rfl⟩))
  let := B.ideal_closed
  exact BoundedAlgHom.liftQuotient K B.ideal q hq

/-- The second coordinate block descends through the other original closed ideal. -/
def rightMap : BoundedAlgHom K C (algebra f g) := by
  let q := (presentationMap K (algebra f g)).comp
    (appendRight B.polyradius C.polyradius K)
  have hq : ∀ p ∈ C.ideal, q p = 0 := by
    intro p hp
    exact presentationMap_relation K _ _ (relations f g)
      (Set.mem_union_left _ (Set.mem_union_right _ ⟨p, hp, rfl⟩))
  let := C.ideal_closed
  exact BoundedAlgHom.liftQuotient K C.ideal q hq

@[simp]
theorem leftMap_presentationMap (p : GeneralizedTateAlgebra B.polyradius K) :
    leftMap f g (presentationMap K B p) =
      presentationMap K (algebra f g) (appendLeft B.polyradius C.polyradius K p) := rfl

@[simp]
theorem rightMap_presentationMap (p : GeneralizedTateAlgebra C.polyradius K) :
    rightMap f g (presentationMap K C p) =
      presentationMap K (algebra f g) (appendRight B.polyradius C.polyradius K p) := rfl

theorem norm_leftMap_le (b : B) : ‖leftMap f g b‖ ≤ ‖b‖ := by
  let := B.ideal_closed
  have h := BoundedAlgHom.quotient_norm_bound B.ideal
    (leftMap f g).toAlgHom.toRingHom 1 zero_lt_one (fun p => by
      change ‖presentationMap K (algebra f g)
        (appendLeft B.polyradius C.polyradius K p)‖ ≤ 1 * ‖p‖
      rw [one_mul]
      exact (norm_presentationMap_le K (algebra f g) _).trans_eq
        (norm_appendLeft B.polyradius C.polyradius K p)) b
  change ‖leftMap f g b‖ ≤ 1 * ‖b‖ at h
  simpa only [one_mul] using h

theorem norm_rightMap_le (c : C) : ‖rightMap f g c‖ ≤ ‖c‖ := by
  let := C.ideal_closed
  have h := BoundedAlgHom.quotient_norm_bound C.ideal
    (rightMap f g).toAlgHom.toRingHom 1 zero_lt_one (fun p => by
      change ‖presentationMap K (algebra f g)
        (appendRight B.polyradius C.polyradius K p)‖ ≤ 1 * ‖p‖
      rw [one_mul]
      exact (norm_presentationMap_le K (algebra f g) _).trans_eq
        (norm_appendRight B.polyradius C.polyradius K p)) c
  change ‖rightMap f g c‖ ≤ 1 * ‖c‖ at h
  simpa only [one_mul] using h

/-- The two actual quotient maps agree over the original algebra. -/
theorem condition : (leftMap f g).comp f = (rightMap f g).comp g := by
  apply BoundedAlgHom.ext
  intro a
  have h := presentationMap_relation K _ _ (relations f g) (Set.mem_union_right _
    (Set.mem_range_self a))
  change Ideal.Quotient.mk (Ideal.span (relations f g)).closure (_ - _) = 0 at h
  rw [map_sub] at h
  change leftMap f g (presentationMap K B (representative B (f a))) -
    rightMap f g (presentationMap K C (representative C (g a))) = 0 at h
  change leftMap f g (f a) = rightMap f g (g a)
  simpa only [presentationMap_representative, sub_eq_zero] using h

@[simp]
theorem leftMap_coordinate (i : Fin B.arity) :
    leftMap f g (coordinate K B i) =
      coordinate K (algebra f g) (Fin.castAdd C.arity i) := by
  change presentationMap K (algebra f g)
    (appendLeft B.polyradius C.polyradius K (X B.polyradius K i)) = _
  rw [appendLeft_X]
  rfl

@[simp]
theorem rightMap_coordinate (j : Fin C.arity) :
    rightMap f g (coordinate K C j) =
      coordinate K (algebra f g) (Fin.natAdd B.arity j) := by
  change presentationMap K (algebra f g)
    (appendRight B.polyradius C.polyradius K (X C.polyradius K j)) = _
  rw [appendRight_X]
  rfl

variable (E : Type v) [NormedCommRing E] [NormedAlgebra K E]

/-- Both quotient legs determine a bounded map into any normed target. -/
theorem hom_ext (p q : BoundedAlgHom K (algebra f g) E)
    (hl : p.comp (leftMap f g) = q.comp (leftMap f g))
    (hr : p.comp (rightMap f g) = q.comp (rightMap f g)) : p = q := by
  apply hom_ext_coordinate K E (algebra f g)
  intro i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · rw [← leftMap_coordinate]
    exact congrArg (fun h : BoundedAlgHom K B E => h (coordinate K B k)) hl
  · rw [← rightMap_coordinate]
    exact congrArg (fun h : BoundedAlgHom K C E => h (coordinate K C k)) hr

variable (α : BoundedAlgHom K B E) (β : BoundedAlgHom K C E)

/-- Images of both original coordinate blocks form a bounded weighted tuple. -/
theorem tuple_bounded :
    HasBoundedMonomials (B.polyradius.append C.polyradius) E
      (Fin.append (fun i => α (coordinate K B i)) (fun j => β (coordinate K C j))) :=
  hasBoundedMonomials_append B.polyradius C.polyradius E _ _
    (hasBoundedMonomials_coordinate K E B α) (hasBoundedMonomials_coordinate K E C β)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- Evaluate the concatenated original coordinate images in the actual target. -/
def evaluation : BoundedAlgHom K
    (GeneralizedTateAlgebra (B.polyradius.append C.polyradius) K) E :=
  evaluateHom (B.polyradius.append C.polyradius) K E
    (Fin.append (fun i => α (coordinate K B i)) (fun j => β (coordinate K C j)))
    (tuple_bounded E α β)

@[simp]
theorem evaluation_left (p : GeneralizedTateAlgebra B.polyradius K) :
    evaluation E α β (appendLeft B.polyradius C.polyradius K p) =
      α (presentationMap K B p) := by
  have h : (evaluation E α β).comp (appendLeft B.polyradius C.polyradius K) =
      α.comp (presentationMap K B) := by
    apply GeneralizedTateAlgebra.hom_ext B.polyradius K E
    intro i
    change evaluate (B.polyradius.append C.polyradius) K E _
      (appendLeft B.polyradius C.polyradius K (X B.polyradius K i)) = _
    rw [appendLeft_X, evaluate_X]
    exact Fin.append_left _ _ i
  exact congrArg (fun h : BoundedAlgHom K (GeneralizedTateAlgebra B.polyradius K) E => h p) h

@[simp]
theorem evaluation_right (p : GeneralizedTateAlgebra C.polyradius K) :
    evaluation E α β (appendRight B.polyradius C.polyradius K p) =
      β (presentationMap K C p) := by
  have h : (evaluation E α β).comp (appendRight B.polyradius C.polyradius K) =
      β.comp (presentationMap K C) := by
    apply GeneralizedTateAlgebra.hom_ext C.polyradius K E
    intro i
    change evaluate (B.polyradius.append C.polyradius) K E _
      (appendRight B.polyradius C.polyradius K (X C.polyradius K i)) = _
    rw [appendRight_X, evaluate_X]
    exact Fin.append_right _ _ i
  exact congrArg (fun h : BoundedAlgHom K (GeneralizedTateAlgebra C.polyradius K) E => h p) h

variable (hcompat : α.comp f = β.comp g)

include hcompat in
/-- The evaluated original ideals and all coefficient-identification relations vanish. -/
theorem evaluation_relations : ∀ p ∈ relations f g, evaluation E α β p = 0 := by
  intro p hp
  rcases hp with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨a, rfl⟩
  · rw [evaluation_left, (presentationMap_eq_zero_iff K B p).mpr hp]
    exact map_zero α.toAlgHom
  · rw [evaluation_right, (presentationMap_eq_zero_iff K C p).mpr hp]
    exact map_zero β.toAlgHom
  · change (evaluation E α β).toAlgHom (_ - _) = 0
    rw [map_sub, evaluation_left, evaluation_right,
      presentationMap_representative, presentationMap_representative, sub_eq_zero]
    exact congrArg (fun h : BoundedAlgHom K A E => h a) hcompat

/-- The actual descended bounded map from the constructed quotient. -/
def lift : BoundedAlgHom K (algebra f g) E :=
  descendRelations K _ _ (relations f g) E (evaluation E α β)
    (evaluation_relations f g E α β hcompat)

@[simp]
theorem lift_presentationMap (p : GeneralizedTateAlgebra (B.polyradius.append C.polyradius) K) :
    lift f g E α β hcompat (presentationMap K (algebra f g) p) = evaluation E α β p := rfl

/-- The first original bounded map is recovered by the first quotient leg. -/
theorem lift_comp_leftMap : (lift f g E α β hcompat).comp (leftMap f g) = α := by
  apply hom_ext_presentation K E B
  intro p
  change lift f g E α β hcompat (leftMap f g (presentationMap K B p)) = _
  rw [leftMap_presentationMap, lift_presentationMap, evaluation_left]

/-- The second original bounded map is recovered by the second quotient leg. -/
theorem lift_comp_rightMap : (lift f g E α β hcompat).comp (rightMap f g) = β := by
  apply hom_ext_presentation K E C
  intro p
  change lift f g E α β hcompat (rightMap f g (presentationMap K C p)) = _
  rw [rightMap_presentationMap, lift_presentationMap, evaluation_right]

include hcompat in
/-- The finite closed quotient is a bounded pushout into every complete ultrametric target. -/
theorem existsUnique_lift : ∃! h : BoundedAlgHom K (algebra f g) E,
    h.comp (leftMap f g) = α ∧ h.comp (rightMap f g) = β := by
  refine ⟨lift f g E α β hcompat,
    ⟨lift_comp_leftMap f g E α β hcompat, lift_comp_rightMap f g E α β hcompat⟩, ?_⟩
  intro h hh
  apply hom_ext f g E
  · exact hh.1.trans (lift_comp_leftMap f g E α β hcompat).symm
  · exact hh.2.trans (lift_comp_rightMap f g E α β hcompat).symm

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
