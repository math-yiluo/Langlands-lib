import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.ConstituentDichotomy
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Serre classes defined by actual irreducible subquotients

Any predicate on irreducible smooth objects defines a Serre class by requiring
it of every actual irreducible subquotient. Its full subcategory is abelian,
and the inclusion preserves finite limits and colimits.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual quotient by the image kills the original intertwiner. -/
theorem actualCokernel_condition {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    f ≫ cokernelπ f = 0 := by
  ext v
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩

/-- The actual module quotient by an intertwiner's image is its categorical
cokernel in the smooth category. -/
def actualCokernelIsColimit {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (actualCokernel_condition f)) := by
  letI : Epi (cokernelπ f) := (epi_iff_surjective _).mpr (mkQ_surjective _ _)
  apply CokernelCofork.IsColimit.ofπ'
  intro Z k hk
  have hker : (hom f).range.toSubmodule ≤ (hom k).toLinearMap.ker := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun t => hom t v) hk
  let l : cokernel f ⟶ Z := ofHom {
    toLinearMap := (hom f).range.toSubmodule.liftQ (hom k).toLinearMap hker
    isIntertwining' g := by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ (hom k) g v }
  exact ⟨l, by ext v; rfl⟩

/-- In a categorical short exact row, the actual quotient by the first image
is isomorphic to the third object. -/
def actualCokernelIsoOfShortExact {S : ShortComplex (SmoothRep.{uR, uG, uV} R G)}
    (hS : S.ShortExact) : cokernel S.f ≅ S.X₃ :=
  IsColimit.coconePointUniqueUpToIso (actualCokernelIsColimit S.f) hS.gIsCokernel

/-- Every actual irreducible subquotient satisfies the supplied predicate. -/
def irreducibleSubquotientsProperty
    (P : ObjectProperty (SmoothRep.{uR, uG, uV} R G)) :
    ObjectProperty (SmoothRep.{uR, uG, uV} R G) :=
  fun A => ∀ D : SmoothRep.{uR, uG, uV} R G,
    D.IsIrreducible → IsSubquotient D A → P D

variable (P : ObjectProperty (SmoothRep.{uR, uG, uV} R G))

/-- The constituent property passes to all actual subquotients. -/
theorem irreducibleSubquotientsProperty_of_isSubquotient
    {A B : SmoothRep.{uR, uG, uV} R G}
    (hA : irreducibleSubquotientsProperty P A) (hBA : IsSubquotient B A) :
    irreducibleSubquotientsProperty P B :=
  fun D hD hDB => hA D hD (smoothSubquotientTransitivity R G A B D hDB hBA)

/-- An actual irreducible object cannot occur as a subquotient of zero. -/
theorem not_isSubquotient_of_isZero {Z D : SmoothRep.{uR, uG, uV} R G}
    (hZ : IsZero Z) (hD : D.IsIrreducible) : ¬ IsSubquotient D Z := by
  intro h
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  have hi0 : i = 0 := hZ.eq_of_tgt i 0
  have hC : ∀ c : C, c = 0 := by
    intro c
    apply hi
    rw [hi0]
    rfl
  have hD0 : ∀ d : D, d = 0 := by
    intro d
    obtain ⟨c, rfl⟩ := hq d
    rw [hC c, map_zero]
  let : D.representation.IsIrreducible := hD
  have hnt : Nontrivial D.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra R G) D.representation.asModule
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  exact hxy ((hD0 x).trans (hD0 y).symm)

/-- The actual constituent property is a Serre class without a finite-length
assumption. -/
instance irreducibleSubquotientsProperty_isSerreClass :
    (irreducibleSubquotientsProperty P).IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, fun D hD h => (not_isSubquotient_of_isZero
    (isZero_zero _) hD h).elim⟩
  prop_of_mono f _ hY := irreducibleSubquotientsProperty_of_isSubquotient P hY
    (IsSubrepresentation.isSubquotient ⟨f, (mono_iff_injective f).mp inferInstance⟩)
  prop_of_epi f _ hX := irreducibleSubquotientsProperty_of_isSubquotient P hX
    (IsQuotient.isSubquotient ⟨f, (epi_iff_surjective f).mp inferInstance⟩)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    intro D hD h
    rcases irreducibleSubquotient_image_or_cokernel hD h S.f with hI | hQ
    · let p : S.X₁ ⟶ image S.f := ofHom {
        toLinearMap := (hom S.f).toLinearMap.rangeRestrict
        isIntertwining' g := by
          ext v
          exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _
            (hom S.f) g v) }
      have hp : Function.Surjective (hom p) := by
        rintro ⟨_, v, rfl⟩
        exact ⟨v, rfl⟩
      exact h₁ D hD (smoothSubquotientTransitivity R G _ _ D hI
        (IsQuotient.isSubquotient ⟨p, hp⟩))
    · exact h₃ D hD (hQ.of_iso_right (actualCokernelIsoOfShortExact hS))

/-- Binary products preserve the actual constituent property. -/
instance irreducibleSubquotientsProperty_isClosedUnderBinaryProducts :
    (irreducibleSubquotientsProperty P).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact (irreducibleSubquotientsProperty P).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      ((irreducibleSubquotientsProperty P).prop_biprod (p.prop_diag_obj ⟨.left⟩)
        (p.prop_diag_obj ⟨.right⟩))

/-- Finite products preserve the actual constituent property. -/
instance irreducibleSubquotientsProperty_isClosedUnderFiniteProducts :
    (irreducibleSubquotientsProperty P).IsClosedUnderFiniteProducts := .mk'

/-- The full subcategory is abelian with its inherited additive structure. -/
theorem irreducibleSubquotientsSubcategory_abelian :
    ∃ a : Abelian (irreducibleSubquotientsProperty P).FullSubcategory,
      a.toPreadditive = Preadditive.fullSubcategory (irreducibleSubquotientsProperty P) :=
  ⟨inferInstance, rfl⟩

/-- The full-subcategory inclusion preserves finite limits. -/
instance irreducibleSubquotientsInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (irreducibleSubquotientsProperty P).ι := by
  have := (irreducibleSubquotientsProperty P).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The full-subcategory inclusion preserves finite colimits. -/
instance irreducibleSubquotientsInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (irreducibleSubquotientsProperty P).ι := by
  have := (irreducibleSubquotientsProperty P).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

end Langlands.SmoothRep
