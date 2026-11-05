import Langlands.Geometry.Analytic.SaturatedDomainPreimage
import Langlands.Geometry.Analytic.OriginalDomainTopology
import Mathlib.CategoryTheory.Limits.Preserves.Lattice
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Inverse image on actual domain sites and sheaf direct image -/

noncomputable section

universe u v w p q

namespace Langlands.Analytic

open CategoryTheory CategoryTheory.Limits Set Filter
open scoped Topology

namespace AtlasTopology

/-- Continuous inverse image retains finite relative neighborhood refinements.
Neither surjectivity nor injectivity is required. -/
theorem LocallyRefines.preimage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {υ τ : Set (Set Y)} (h : LocallyRefines υ τ) (f : X → Y) (hf : Continuous f) :
    LocallyRefines ((fun U => f ⁻¹' U) '' υ) ((fun U => f ⁻¹' U) '' τ) := by
  rintro _ ⟨U, hU, rfl⟩ x hx
  obtain ⟨σ, hfin, hsub, hmem, hnhds⟩ := h U hU (f x) hx
  let δ : Set (Set X) := (fun V => f ⁻¹' V) '' σ
  refine ⟨δ, hfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨V, hsub hV, rfl⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨Set.preimage_mono (hmem V hV).1, (hmem V hV).2⟩
  · have heq : ⋃₀ δ = f ⁻¹' ⋃₀ σ := by
      ext y
      constructor
      · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
        exact ⟨V, hV, hy⟩
      · rintro ⟨V, hV, hy⟩
        exact ⟨_, ⟨V, hV, rfl⟩, hy⟩
    rw [heq]
    exact (hf.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy)) hnhds

end AtlasTopology

namespace SaturatedAtlasPresentation.SourceCategory

open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Actual domain inverse image preserves finite intersections and the full domain. -/
def domainPreimageInfTopHom (F : ofPresentation A ⟶ ofPresentation B) :
    InfTopHom B.presentation.atlas.OriginalChartDomain
      A.presentation.atlas.OriginalChartDomain where
  toFun := domainPreimage F
  map_inf' := domainPreimage_inf F
  map_top' := domainPreimage_top F

/-- The site functor sends a domain to its constructed literal inverse image
and an inclusion to the induced inclusion. -/
def domainPreimageFunctor (F : ofPresentation A ⟶ ofPresentation B) :
    B.presentation.atlas.OriginalChartDomain ⥤ A.presentation.atlas.OriginalChartDomain :=
  (OrderHom.ofClass (domainPreimageInfTopHom F)).toFunctor

@[simp]
theorem domainPreimageFunctor_obj (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    (domainPreimageFunctor F).obj S = domainPreimage F S := rfl

/-- Literal inverse image is functorial for identity analytic arrows. -/
def domainPreimageFunctorId :
    domainPreimageFunctor (𝟙 (ofPresentation A)) ≅
      𝟭 A.presentation.atlas.OriginalChartDomain :=
  NatIso.ofComponents (fun S => eqToIso (domainPreimage_id S))
    (fun _ => Subsingleton.elim _ _)

/-- Composition of analytic arrows reverses the order of inverse-image functors. -/
def domainPreimageFunctorComp (F : ofPresentation A ⟶ ofPresentation B)
    (G : ofPresentation B ⟶ ofPresentation C) :
    domainPreimageFunctor (F ≫ G) ≅ domainPreimageFunctor G ⋙ domainPreimageFunctor F :=
  NatIso.ofComponents (fun S => eqToIso (domainPreimage_comp F G S))
    (fun _ => Subsingleton.elim _ _)

instance domainPreimageFunctor_preservesFiniteLimits
    (F : ofPresentation A ⟶ ofPresentation B) :
    PreservesFiniteLimits (domainPreimageFunctor F) := by
  dsimp [domainPreimageFunctor]
  infer_instance

instance domainPreimageFunctor_representablyFlat
    (F : ofPresentation A ⟶ ofPresentation B) :
    RepresentablyFlat (domainPreimageFunctor F) :=
  flat_of_preservesFiniteLimits _

/-- The finite relative neighborhood witnesses of a covering sieve pull back
to witnesses in its full functorial pushforward. -/
theorem domainPreimageFunctor_isCovering
    (F : ofPresentation A ⟶ ofPresentation B)
    {S : B.presentation.atlas.OriginalChartDomain} {R : Sieve S} (hR : IsCovering R) :
    IsCovering (R.functorPushforward (domainPreimageFunctor F)) := by
  have h := hR.preimage (spaceFunctor.map F) (spaceFunctor.map F).hom.continuous
  rw [Set.image_singleton] at h
  apply h.mono ?_ Subset.rfl
  rintro _ ⟨U, ⟨V, hVS, hRV, rfl⟩, rfl⟩
  refine ⟨domainPreimage F V, (domainPreimageOrderHom F).monotone hVS, ?_, rfl⟩
  have heq : homOfLE ((domainPreimageOrderHom F).monotone hVS) =
      (domainPreimageFunctor F).map (homOfLE hVS) := Subsingleton.elim _ _
  erw [heq]
  exact Sieve.image_mem_functorPushforward (domainPreimageFunctor F) R hRV

/-- Inverse image preserves every quasinet covering sieve. -/
theorem domainPreimageFunctor_coverPreserving (F : ofPresentation A ⟶ ofPresentation B) :
    CoverPreserving (quasinetTopology B.presentation.atlas)
      (quasinetTopology A.presentation.atlas) (domainPreimageFunctor F) where
  cover_preserve := domainPreimageFunctor_isCovering F

/-- Precomposition by actual domain inverse image carries sheaves to sheaves. -/
instance domainPreimageFunctor_isContinuous (F : ofPresentation A ⟶ ofPresentation B) :
    (domainPreimageFunctor F).IsContinuous (quasinetTopology B.presentation.atlas)
      (quasinetTopology A.presentation.atlas) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (domainPreimageFunctor_coverPreserving F)

variable (D : Type p) [Category.{q} D]

/-- Direct image on sheaves is restriction along the constructed inverse-image
domain functor, with sheafhood supplied by the proved site continuity. -/
def domainSheafPushforward (F : ofPresentation A ⟶ ofPresentation B) :
    Sheaf (quasinetTopology A.presentation.atlas) D ⥤
      Sheaf (quasinetTopology B.presentation.atlas) D :=
  (domainPreimageFunctor F).sheafPushforwardContinuous D
    (quasinetTopology B.presentation.atlas) (quasinetTopology A.presentation.atlas)

@[simp]
theorem domainSheafPushforward_obj_obj (F : ofPresentation A ⟶ ofPresentation B)
    (M : Sheaf (quasinetTopology A.presentation.atlas) D)
    (S : B.presentation.atlas.OriginalChartDomain) :
    ((domainSheafPushforward D F).obj M).obj.obj (Opposite.op S) =
      M.obj.obj (Opposite.op (domainPreimage F S)) := rfl

@[simp]
theorem domainSheafPushforward_obj_map (F : ofPresentation A ⟶ ofPresentation B)
    (M : Sheaf (quasinetTopology A.presentation.atlas) D)
    {S T : B.presentation.atlas.OriginalChartDomain} (i : S ⟶ T) :
    ((domainSheafPushforward D F).obj M).obj.map i.op =
      M.obj.map ((domainPreimageFunctor F).map i).op := rfl

@[simp]
theorem domainSheafPushforward_map_app (F : ofPresentation A ⟶ ofPresentation B)
    {M N : Sheaf (quasinetTopology A.presentation.atlas) D} (α : M ⟶ N)
    (S : B.presentation.atlas.OriginalChartDomain) :
    ((domainSheafPushforward D F).map α).hom.app (Opposite.op S) =
      α.hom.app (Opposite.op (domainPreimage F S)) := rfl

/-- Direct image along an identity analytic arrow is naturally the identity. -/
def domainSheafPushforwardId :
    domainSheafPushforward D (𝟙 (ofPresentation A)) ≅
      𝟭 (Sheaf (quasinetTopology A.presentation.atlas) D) :=
  Functor.sheafPushforwardContinuousId' (domainPreimageFunctorId (A := A)) D
    (quasinetTopology A.presentation.atlas)

/-- Successive sheaf direct images identify with direct image along the
composite analytic arrow. -/
def domainSheafPushforwardComp (F : ofPresentation A ⟶ ofPresentation B)
    (G : ofPresentation B ⟶ ofPresentation C) :
    domainSheafPushforward D F ⋙ domainSheafPushforward D G ≅
      domainSheafPushforward D (F ≫ G) :=
  Functor.sheafPushforwardContinuousComp' (domainPreimageFunctorComp F G).symm D
    (quasinetTopology C.presentation.atlas) (quasinetTopology B.presentation.atlas)
    (quasinetTopology A.presentation.atlas)

end SaturatedAtlasPresentation.SourceCategory

end Langlands.Analytic
