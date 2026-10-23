import Langlands.Geometry.Analytic.StrictTestDomain.RationalBaseChange
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Actual algebra presheaves on rational presentations -/

noncomputable section

universe u

namespace Langlands.Analytic

open CategoryTheory

/-- Forget the presentation and norm, retaining the actual commutative algebra
and the algebra map underlying every bounded morphism. -/
def PresentedStrictAffinoidAlgebra.toCommAlgCat (K : Type u)
    [NormedField K] [IsUltrametricDist K] :
    PresentedStrictAffinoidAlgebra K ⥤ CommAlgCat K where
  obj A := CommAlgCat.of K A
  map f := CommAlgCat.ofHom f.toAlgHom
  map_id _ := rfl
  map_comp _ _ := rfl

namespace StrictTestDomain.RationalData

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K)

/-- The presheaf of actual rational quotient algebras and bounded restrictions. -/
def rationalBoundedPresheaf : (RationalData K P)ᵒᵖ ⥤ PresentedStrictAffinoidAlgebra K where
  obj d := d.unop.algebra
  map h := h.unop.restriction
  map_id d := Inclusion.restriction_id d.unop
  map_comp h k := Inclusion.restriction_comp k.unop h.unop

/-- The same presheaf retaining the complete normed ring structure. -/
def rationalBanachPresheaf : (RationalData K P)ᵒᵖ ⥤ BanachRing :=
  rationalBoundedPresheaf K P ⋙ PresentedStrictAffinoidAlgebra.toBanachRing K

/-- The commutative K-algebra-valued rational presheaf. -/
def rationalPresheaf : (RationalData K P)ᵒᵖ ⥤ CommAlgCat K :=
  rationalBoundedPresheaf K P ⋙ PresentedStrictAffinoidAlgebra.toCommAlgCat K

/-- The actual base maps define a natural transformation from the constant
bounded-algebra presheaf. -/
def rationalBaseMap : (Functor.const (RationalData K P)ᵒᵖ).obj P ⟶
    rationalBoundedPresheaf K P where
  app d := d.unop.baseMap
  naturality d e h := by
    change e.unop.baseMap.comp (BoundedAlgHom.id K P) = h.unop.restriction.comp d.unop.baseMap
    simpa only [BoundedAlgHom.comp_id] using h.unop.restriction_comp_baseMap.symm

variable {K P} {Q : PresentedStrictAffinoidAlgebra K}

/-- The actual bounded comparisons form a morphism of algebra presheaves. -/
def rationalBoundedComparison (φ : BoundedAlgHom K P Q) :
    rationalBoundedPresheaf K P ⟶ (pullbackFunctor φ).op ⋙ rationalBoundedPresheaf K Q where
  app d := d.unop.comparison φ
  naturality d e h := by
    exact (h.unop.restriction_pullback_comp_comparison φ).symm

/-- The base-change comparison as a morphism of commutative K-algebra presheaves. -/
def rationalPresheafComparison (φ : BoundedAlgHom K P Q) :
    rationalPresheaf K P ⟶ (pullbackFunctor φ).op ⋙ rationalPresheaf K Q where
  app d := CommAlgCat.ofHom (d.unop.comparison φ).toAlgHom
  naturality d e h := by
    apply CommAlgCat.hom_ext
    exact congrArg BoundedAlgHom.toAlgHom
      (h.unop.restriction_pullback_comp_comparison φ).symm

/-- On sections the presheaf comparison commutes with the actual base maps. -/
@[simp]
theorem rationalPresheafComparison_baseMap (φ : BoundedAlgHom K P Q)
    (d : RationalData K P) (a : P) :
    (rationalPresheafComparison φ).app (Opposite.op d) (d.baseMap a) =
      (d.pullback φ).baseMap (φ a) :=
  congrArg (fun f : BoundedAlgHom K P (d.pullback φ).algebra => f a)
    (d.comparison_comp_baseMap φ)

variable (K P)

/-- The whole-spectrum presentation admits the inverse to its base map. -/
theorem existsUnique_wholeEvaluation :
    ∃! φ : BoundedAlgHom K (whole K P).algebra P,
      φ.comp (whole K P).baseMap = BoundedAlgHom.id K P := by
  apply (rationalRepresentation K P (whole K P)).2.2
  intro x
  rw [locus_whole]
  exact Set.mem_univ _

/-- The bounded inverse is constructed from the proved rational representation. -/
def wholeEvaluation : BoundedAlgHom K (whole K P).algebra P :=
  (existsUnique_wholeEvaluation K P).choose

@[simp]
theorem wholeEvaluation_comp_baseMap :
    (wholeEvaluation K P).comp (whole K P).baseMap = BoundedAlgHom.id K P :=
  (existsUnique_wholeEvaluation K P).choose_spec.1

@[simp]
theorem wholeBaseMap_comp_evaluation :
    (whole K P).baseMap.comp (wholeEvaluation K P) =
      BoundedAlgHom.id K (whole K P).algebra := by
  apply (whole K P).hom_ext
  rw [BoundedAlgHom.comp_assoc, wholeEvaluation_comp_baseMap]
  rfl

/-- The value at the whole-spectrum object is the base algebra, by an actual
bounded isomorphism rather than an identification of presentations. -/
def rationalBoundedWholeIso :
    P ≅ (rationalBoundedPresheaf K P).obj (Opposite.op (whole K P)) where
  hom := (whole K P).baseMap
  inv := wholeEvaluation K P
  hom_inv_id := wholeEvaluation_comp_baseMap K P
  inv_hom_id := wholeBaseMap_comp_evaluation K P

/-- The induced isomorphism of commutative K-algebras at the whole object. -/
def rationalWholeIso :
    CommAlgCat.of K P ≅ (rationalPresheaf K P).obj (Opposite.op (whole K P)) :=
  (PresentedStrictAffinoidAlgebra.toCommAlgCat K).mapIso (rationalBoundedWholeIso K P)

/-- Restriction from the whole-spectrum value agrees with the actual base map. -/
theorem restriction_whole_baseMap (d : RationalData K P) :
    (toWhole d).restriction.comp (rationalBoundedWholeIso K P).hom = d.baseMap :=
  (toWhole d).restriction_comp_baseMap

end StrictTestDomain.RationalData
end Langlands.Analytic
