import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The abelian category of smooth representations

Smoothness is closed under subobjects, quotients and finite products in Mathlib's
abelian category of algebraic representations. Hence the published full
subcategory of smooth representations is abelian, and its inclusion preserves
monomorphisms and epimorphisms.
-/

noncomputable section

namespace Langlands

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uG uV

variable (R : Type uR) (G : Type uG) [CommRing R] [Group G] [TopologicalSpace G]

namespace SmoothRep

omit [TopologicalSpace G] in
/-- Elements of an actual limit of algebraic representations are determined by
their projections. -/
theorem rep_limit_ext {J : Type*} [Category J] (F : J ⥤ Rep.{uV} R G) [HasLimit F]
    [PreservesLimit F (forget₂ (Rep.{uV} R G) (ModuleCat.{uV} R))]
    [PreservesLimit (F ⋙ forget₂ (Rep.{uV} R G) (ModuleCat.{uV} R))
      (forget (ModuleCat.{uV} R))]
    (x y : (limit F).V) (h : ∀ j, (limit.π F j).hom x = (limit.π F j).hom y) : x = y :=
  Concrete.isLimit_ext (F ⋙ forget₂ (Rep.{uV} R G) (ModuleCat.{uV} R))
    (isLimitOfPreserves (forget₂ (Rep.{uV} R G) (ModuleCat.{uV} R)) (limit.isLimit F))
    x y h

/-- A zero representation is smooth. -/
instance smoothRepProperty_containsZero :
    (smoothRepProperty.{uR, uG, uV} R G).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro v
    have hv : v = 0 := by
      have h := congrArg (fun f : (0 : Rep.{uV} R G) ⟶ 0 => f.hom v)
        ((isZero_zero (Rep.{uV} R G)).eq_of_src (𝟙 _) 0)
      exact h
    rw [hv]
    exact isSmoothVector_zero

/-- A subrepresentation of a smooth representation is smooth. -/
instance smoothRepProperty_isClosedUnderSubobjects :
    (smoothRepProperty.{uR, uG, uV} R G).IsClosedUnderSubobjects where
  prop_of_mono f _ hY :=
    isSmooth_of_injective f.hom ((Rep.mono_iff_injective f).1 inferInstance) hY

/-- A quotient of a smooth representation is smooth. -/
instance smoothRepProperty_isClosedUnderQuotients :
    (smoothRepProperty.{uR, uG, uV} R G).IsClosedUnderQuotients where
  prop_of_epi f _ hX :=
    isSmooth_of_surjective f.hom ((Rep.epi_iff_surjective f).1 inferInstance) hX

/-- A binary product of smooth representations is smooth: an element is fixed by
the intersection of open subgroups fixing its two projections. -/
instance smoothRepProperty_isClosedUnderBinaryProducts :
    (smoothRepProperty.{uR, uG, uV} R G).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩ x
    obtain ⟨K₁, hK₁⟩ := hF ⟨.left⟩ ((limit.π F ⟨.left⟩).hom x)
    obtain ⟨K₂, hK₂⟩ := hF ⟨.right⟩ ((limit.π F ⟨.right⟩).hom x)
    refine ⟨K₁ ⊓ K₂, ?_⟩
    rw [mem_fixedVectors_iff]
    intro k
    apply rep_limit_ext R G F
    rintro ⟨⟨⟩⟩
    · rw [Rep.hom_comm_apply]
      exact (mem_fixedVectors_iff _ _).1 hK₁ ⟨k, k.2.1⟩
    · rw [Rep.hom_comm_apply]
      exact (mem_fixedVectors_iff _ _).1 hK₂ ⟨k, k.2.2⟩)

/-- Finite products of smooth representations are smooth. -/
instance smoothRepProperty_isClosedUnderFiniteProducts :
    (smoothRepProperty.{uR, uG, uV} R G).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The published category of smooth representations is abelian. -/
instance abelian : Abelian (SmoothRep.{uR, uG, uV} R G) :=
  inferInstance

/-- The inclusion into algebraic representations preserves monomorphisms. -/
instance toRep_preservesMonomorphisms :
    (toRep (R := R) (G := G) : SmoothRep.{uR, uG, uV} R G ⥤ _).PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- The inclusion into algebraic representations preserves epimorphisms. -/
instance toRep_preservesEpimorphisms :
    (toRep (R := R) (G := G) : SmoothRep.{uR, uG, uV} R G ⥤ _).PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

variable {R G}

/-- Monomorphisms of smooth representations are exactly injective intertwiners. -/
theorem mono_iff_injective {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (hom f) := by
  constructor
  · intro _
    exact (Rep.mono_iff_injective (toRep.map f)).1 inferInstance
  · intro h
    exact toRep.mono_of_mono_map ((Rep.mono_iff_injective (toRep.map f)).2 h)

/-- Epimorphisms of smooth representations are exactly surjective intertwiners. -/
theorem epi_iff_surjective {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective (hom f) := by
  constructor
  · intro _
    exact (Rep.epi_iff_surjective (toRep.map f)).1 inferInstance
  · intro h
    exact toRep.epi_of_epi_map ((Rep.epi_iff_surjective (toRep.map f)).2 h)

end SmoothRep

end Langlands
