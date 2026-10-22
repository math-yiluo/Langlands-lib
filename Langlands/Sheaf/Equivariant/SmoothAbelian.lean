import Langlands.Sheaf.Equivariant.SmoothPart
import Langlands.Sheaf.Equivariant.Exact
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The abelian category of smooth equivariant sheaves

Smoothness of equivariant module sheaves is closed under subobjects, quotients
and finite products, so smooth equivariant module sheaves form an abelian full
subcategory. Its inclusion is exact. Since the smooth part is right adjoint to
the inclusion, which preserves monomorphisms, the smooth part preserves
injective objects and the smooth category has enough injectives.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] in
/-- A subsheaf of a smooth equivariant module sheaf is smooth. -/
instance smoothSheafProperty_isClosedUnderSubobjects :
    (smoothSheafProperty R G X).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := IsSmoothSheaf.of_mono R f hY

/-- A zero equivariant module sheaf is smooth: it embeds into the smooth part
of any sheaf, here of itself. -/
instance smoothSheafProperty_containsZero : (smoothSheafProperty R G X).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    let f : (0 : TopologicalSheaf G X (ModuleCat.{u} R)) ⟶ (smoothSubsheafFunctor R).obj 0 := 0
    have : Mono f := ⟨fun g h _ => (isZero_zero _).eq_of_tgt g h⟩
    exact IsSmoothSheaf.of_mono R f (isSmoothSheaf_smoothSubsheaf R 0)

variable {G X} in
omit [IsTopologicalGroup G] [HasStableNeighbourhoods G X] in
/-- A quotient of a smooth equivariant module sheaf is smooth. An epimorphism is
locally surjective on the underlying ordinary sheaves, so near every point a
section is the image of a locally fixed section. -/
theorem IsSmoothSheaf.of_epi {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (f : F ⟶ F')
    [Epi f] (hF : IsSmoothSheaf R G X F) : IsSmoothSheaf R G X F' := by
  intro U t x hx
  have hepi : Epi ((toSheaf G X (ModuleCat.{u} R)).map f) := inferInstance
  obtain ⟨V, hVU, ⟨s, hs⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi _).2 hepi) U.openSet t x hx
  have h₁ := IsLocallyFixedAt.map R f.hom (hF ⟨V⟩ s x hxV)
  have h₂ : (f.hom.app (op ⟨V⟩)).hom s =
      (F'.obj.map (ActionOpens.inclusionHom (U := (⟨V⟩ : ActionOpens G X)) (V := U)
        hVU).op).hom t := hs
  rw [h₂] at h₁
  exact IsLocallyFixedAt.of_restrict R hVU h₁

omit [IsTopologicalGroup G] [HasStableNeighbourhoods G X] in
/-- A quotient of a smooth equivariant module sheaf is smooth. -/
instance smoothSheafProperty_isClosedUnderQuotients :
    (smoothSheafProperty R G X).IsClosedUnderQuotients where
  prop_of_epi f _ hX := IsSmoothSheaf.of_epi R f hX

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] in
/-- Sections of a limit of equivariant module sheaves are determined by their
projections. -/
theorem limit_sections_ext {J : Type} [Category J] [FinCategory J]
    (D : J ⥤ TopologicalSheaf G X (ModuleCat.{u} R)) {U : ActionOpens G X}
    (a b : (limit D).obj.obj (op U))
    (h : ∀ j, ((limit.π D j).hom.app (op U)).hom a = ((limit.π D j).hom.app (op U)).hom b) :
    a = b :=
  Concrete.isLimit_ext (D ⋙ evaluation G X (ModuleCat.{u} R) U)
    (isLimitOfPreserves (evaluation G X (ModuleCat.{u} R) U) (limit.isLimit D)) a b h

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] in
/-- Morphisms of equivariant sheaves commute with restriction and transport of
sections. -/
theorem hom_app_map_apply {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (f : F ⟶ F')
    {A B : (ActionOpens G X)ᵒᵖ} (g : A ⟶ B) (a : F.obj.obj A) :
    (f.hom.app B).hom ((F.obj.map g).hom a) = (F'.obj.map g).hom ((f.hom.app A).hom a) := by
  have key := congrArg (fun k => k.hom a) (f.hom.naturality g)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using key

omit [IsTopologicalGroup G] [ContinuousConstSMul G X] in
/-- A binary product of smooth equivariant module sheaves is smooth: the two
projections of a section are fixed on a common stable neighbourhood by a
common open subgroup. -/
instance smoothSheafProperty_isClosedUnderBinaryProducts :
    (smoothSheafProperty R G X).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨D, hD⟩ U s x hx
    have hl := hD ⟨.left⟩ U (((limit.π D ⟨.left⟩).hom.app (op U)).hom s) x hx
    have hr := hD ⟨.right⟩ U (((limit.π D ⟨.right⟩).hom.app (op U)).hom s) x hx
    obtain ⟨V, hV₁, _, K, hV, hxV, h₁, h₂⟩ := IsLocallyFixedAt.exists_common R hl hr
    refine ⟨V, hV₁, K, hV, hxV, fun k => ?_⟩
    apply limit_sections_ext R G X D
    rintro ⟨⟨⟩⟩
    · rw [hom_app_map_apply, hom_app_map_apply]
      exact h₁ k
    · rw [hom_app_map_apply, hom_app_map_apply]
      exact h₂ k)

/-- Finite products of smooth equivariant module sheaves are smooth. -/
instance smoothSheafProperty_isClosedUnderFiniteProducts :
    (smoothSheafProperty R G X).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Smooth equivariant module sheaves form an abelian category. -/
instance smoothTopologicalSheaf_abelian : Abelian (SmoothTopologicalSheaf R G X) :=
  inferInstance

/-- The inclusion of smooth sheaves preserves monomorphisms. -/
instance smoothInclusion_preservesMonomorphisms :
    (smoothInclusion R G X).PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- The inclusion of smooth sheaves preserves epimorphisms. -/
instance smoothInclusion_preservesEpimorphisms :
    (smoothInclusion R G X).PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

/-- The smooth part of an injective equivariant module sheaf is injective in
the smooth category. -/
theorem injective_smoothCoreflector_obj (I : TopologicalSheaf G X (ModuleCat.{u} R))
    [Injective I] : Injective ((smoothCoreflector R).obj I) :=
  (smoothAdjunction R).map_injective I inferInstance

/-- Smooth equivariant module sheaves have enough injectives: a smooth sheaf
embeds into the smooth part of any injective equivariant sheaf containing it,
and that smooth part is injective in the smooth category. -/
instance smoothTopologicalSheaf_enoughInjectives :
    EnoughInjectives (SmoothTopologicalSheaf R G X) :=
  EnoughInjectives.of_adjunction (smoothAdjunction R)

end Langlands.Sheaf.Equivariant
