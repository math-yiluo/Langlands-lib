import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentConstancyProof
import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroGeometricComponentComparisonStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The origin-component-to-Picard-zero implication -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)
  {P : Over S} (L : relative f ε section_eq P)
  (hL : IsUniversal f ε section_eq L)

/-- A universal family is classified by the identity of its parameter. -/
lemma classifyFamily_self : classifyFamily f ε section_eq L hL L = 𝟙 P := by
  apply (hL P).injective
  rw [classifyFamily_spec, classifyingMap_id f ε section_eq Langlands.SchemeModule.RigidifiedModule.pullbackCoherence]

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  {P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (L : RigidifiedFamily A P)
  (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L)

/-- The family pulled back along any parameter map factoring through the trivial parameter
is geometrically Picard-zero. -/
lemma isPicardZeroFamily_pullback_of_eq_trivialParameter {T : Over _} (h : T ⟶ P)
    (hh : h = Over.mkIdTerminal.from T ≫
      RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A) h).obj
        L) := by
  have hc : RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) L hL
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) h).obj L) =
      RigidifiedLineBundle.classifyFamily A.X.hom (unitSection A) (unitSection_comp A) L hL
        (RigidifiedLineBundle.relativeTrivial A.X.hom (unitSection A) (unitSection_comp A) T) := by
    rw [RigidifiedLineBundle.classifyFamily_pullback, RigidifiedLineBundle.classifyFamily_self,
      Category.comp_id, hh, RigidifiedLineBundle.classifyFamily_trivial]
  exact (isPicardZeroFamily_iff_of_iso A
    (RigidifiedLineBundle.isoOfClassifyFamilyEq _ _ _ L hL _ _ hc)).2
    (isPicardZeroFamily_trivial A T)

/-- Every point of the base field spectrum maps to the origin point under the trivial
parameter. -/
lemma trivialParameter_apply (y : Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :
    (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL).left
      y = fullPicardOriginPoint k A L hL := by
  unfold fullPicardOriginPoint
  congr 1
  have : Subsingleton (Spec (CommRingCat.of k)) := inferInstance
  exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _

/-- A geometric point in the origin component pulls the universal family back to a
geometrically Picard-zero family. -/
theorem isPicardZeroFamily_of_mem_originComponent
    (hP : LocallyOfFiniteType P.hom)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ P.left)
    (hs : Set.range s ⊆ connectedComponent (fullPicardOriginPoint k A L hL)) :
    IsPicardZeroFamily A
      ((RigidifiedLineBundle.relativePullback A.X.hom
        (unitSection A) (unitSection_comp A)
        (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) := by
  let tp := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A) (unitSection_comp A) L hL
  let ι : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶
      Scheme.Spec.obj (Opposite.op (CommRingCat.of k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let s₀ : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ P.left := ι ≫ tp.left
  refine fieldPicardZeroComponentConstancy k A P L hP hL (fullPicardOriginPoint k A L hL)
    (AlgebraicClosure k) s₀ K s ?_ hs ?_
  · rintro _ ⟨y, rfl⟩
    have : s₀ y = tp.left (ι y) := rfl
    rw [this, trivialParameter_apply]
    exact mem_connectedComponent
  · apply isPicardZeroFamily_pullback_of_eq_trivialParameter L hL
    ext
    simp [s₀, tp, ι]

end Langlands.AbelianScheme
