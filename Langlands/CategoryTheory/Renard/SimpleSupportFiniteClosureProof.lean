import Langlands.CategoryTheory.Renard.SimpleSupportFiniteClosureStatements
import Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Renard A.IX: proof of finite closure and abelianness of supported objects

Proof of the published target `SimpleSupportFiniteClosureStatement` for the
unnumbered assertion on printed268/PDF274 of the French edition dated
9 July 2026. The closure properties hold for every set of object classes in
every abelian category; the source antecedents are retained but unused.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Langlands.Renard

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A zero object has no simple subquotients. -/
theorem simpleSubquotientClasses_eq_empty_of_isZero {Z : C} (hZ : IsZero Z) :
    simpleSubquotientClasses Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨A, B, h, hs, rfl⟩
  have := hs
  have hB : IsZero (B : C) := IsZero.of_mono B.arrow hZ
  exact Simple.not_isZero _ (IsZero.of_epi (cokernel.π (Subobject.ofLE A B h)) hB)

/-- Every simple subquotient of the middle term of a short exact sequence is a
simple subquotient of one of its ends. -/
theorem simpleSubquotientClasses_subset_union_of_shortExact {S : ShortComplex C}
    (hS : S.ShortExact) :
    simpleSubquotientClasses S.X₂ ⊆
      simpleSubquotientClasses S.X₁ ∪ simpleSubquotientClasses S.X₃ := by
  have := hS.mono_f
  let P : Subobject S.X₂ := Subobject.mk S.f
  let e : cokernel P.arrow ≅ S.X₃ :=
    (cokernelEpiComp (Subobject.underlyingIso S.f).inv P.arrow).symm ≪≫
      cokernelIsoOfEq (Subobject.underlyingIso_arrow S.f) ≪≫
        IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel
  refine (simpleSubquotientClasses_subset_union S.X₂ P).trans
    (Set.union_subset_union ?_ ?_)
  · exact simpleSubquotientClasses_subset_of_mono (Subobject.underlyingIso S.f).hom
  · exact simpleSubquotientClasses_subset_of_mono e.hom

variable (S : Set (ObjectClass C))

/-- The actual support predicate is a Serre class. -/
instance simpleSupportObjects_isSerreClass : (simpleSupportObjects S).IsSerreClass where
  exists_zero := ⟨0, isZero_zero C, fun q hq => by
    rw [simpleSubquotientClasses_eq_empty_of_isZero (isZero_zero C)] at hq
    exact hq.elim⟩
  prop_of_mono f _ hY := fun _ hq => hY (simpleSubquotientClasses_subset_of_mono f hq)
  prop_of_epi f _ hX := fun _ hq => hX (simpleSubquotientClasses_subset_of_epi f hq)
  prop_X₂_of_shortExact hS h₁ h₃ := fun _ hq =>
    (Set.union_subset h₁ h₃) (simpleSubquotientClasses_subset_union_of_shortExact hS hq)

/-- The actual support predicate is closed under binary products. -/
instance simpleSupportObjects_isClosedUnderBinaryProducts :
    (simpleSupportObjects S).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact (simpleSupportObjects S).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      ((simpleSupportObjects S).prop_biprod (p.prop_diag_obj ⟨.left⟩)
        (p.prop_diag_obj ⟨.right⟩))

/-- The actual support predicate is closed under finite products. -/
instance simpleSupportObjects_isClosedUnderFiniteProducts :
    (simpleSupportObjects S).IsClosedUnderFiniteProducts :=
  .mk'

/-- Mathlib's abelian structure on the actual supported full subcategory has the
inherited preadditive structure. -/
theorem simpleSupportSubcategory_abelian :
    ∃ a : Abelian (SimpleSupportSubcategory S),
      a.toPreadditive = Preadditive.fullSubcategory (simpleSupportObjects S) :=
  ⟨inferInstance, rfl⟩

/-- The actual inclusion preserves finite limits. -/
instance simpleSupportInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (simpleSupportInclusion S) := by
  have := (simpleSupportObjects S).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The actual inclusion preserves finite colimits. -/
instance simpleSupportInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (simpleSupportInclusion S) := by
  have := (simpleSupportObjects S).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

end

/-- Renard A.IX, printed268/PDF274: finite closure, inherited abelianness and
exactness of the inclusion for the actual supported full subcategory. -/
theorem simpleSupportFiniteClosure
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportFiniteClosureStatement.{w} C :=
  ⟨fun _ _ _ _ => inferInstance, fun _ _ _ _ => inferInstance,
    fun _ _ S _ => simpleSupportSubcategory_abelian S,
    fun _ _ _ _ => ⟨inferInstance, inferInstance⟩⟩

end Langlands.Renard
