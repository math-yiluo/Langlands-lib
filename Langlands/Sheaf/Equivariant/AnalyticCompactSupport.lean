import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Langlands.Sheaf.Equivariant.TwistedCompactSupport
import Langlands.Geometry.Analytic.EtaleGeometricPointEquivariance
import Langlands.Geometry.Analytic.SaturatedSourceCategory

/-!
# Compactly supported sections of étale `G`-sheaves on analytic spaces

Let `G` act on an analytic space `X`. The `L`-valued points of `X` carry the
topology induced from the underlying space `|X|`, and `G` acts on them by
homeomorphisms. If every `L`-valued point satisfies the point axioms, the
`L`-valued points form a translation-compatible family of points of the étale
site, so the general construction of `TwistedCompactSupport` gives the compactly
supported global sections of sheaves on the twisted étale site, as
representations and as smooth representations of `G`. A section is compactly
supported for this topology exactly when the image of its support in `|X|` lies in
a compact subset of `|X|` made of underlying points of `L`-valued points.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

section Topology

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The underlying point in `|X|` of an `L`-valued point of `X`. -/
def pointProjection : (localizedFieldPointFunctor L).obj X → localizedSpaceFunctor.obj X :=
  fun x => ((localizedFieldPointProjection L).app X x).down

/-- The topology on the `L`-valued points of `X` induced from `|X|` by the underlying
point map. -/
abbrev pointTopology : TopologicalSpace ((localizedFieldPointFunctor L).obj X) :=
  TopologicalSpace.induced (pointProjection L X) inferInstance

theorem isInducing_pointProjection :
    @Topology.IsInducing _ _ (pointTopology L X) _ (pointProjection L X) :=
  @Topology.IsInducing.induced _ _ _ (pointProjection L X)

variable {X}

/-- The underlying point map commutes with morphisms of analytic spaces. -/
theorem pointProjection_map {Y : LocalizedCategory.{u, v, v} (K := K)} (f : X ⟶ Y)
    (x : (localizedFieldPointFunctor L).obj X) :
    pointProjection L Y ((localizedFieldPointFunctor L).map f x) =
      localizedSpaceFunctor.map f (pointProjection L X x) :=
  congrArg ULift.down (NatTrans.naturality_apply (localizedFieldPointProjection L) f x)

/-- A set of `L`-valued points lies in a compact set exactly when its image in `|X|`
lies in a compact set of underlying points of `L`-valued points. -/
theorem exists_isCompact_superset_iff (S : Set ((localizedFieldPointFunctor L).obj X)) :
    (∃ C, @IsCompact _ (pointTopology L X) C ∧ S ⊆ C) ↔
      ∃ C : Set (localizedSpaceFunctor.obj X), IsCompact C ∧
        C ⊆ Set.range (pointProjection L X) ∧ pointProjection L X '' S ⊆ C := by
  let := pointTopology L X
  constructor
  · rintro ⟨C, hC, hSC⟩
    exact ⟨_, hC.image (isInducing_pointProjection L X).continuous, Set.image_subset_range _ _,
      Set.image_mono hSC⟩
  · rintro ⟨C, hC, hCr, hSC⟩
    exact ⟨_, (isInducing_pointProjection L X).isCompact_preimage' hC hCr,
      (Set.subset_preimage_image _ S).trans (Set.preimage_mono hSC)⟩

/-- If every point of `|X|` underlies an `L`-valued point, a set of `L`-valued points
lies in a compact set exactly when its image lies in a compact subset of `|X|`. -/
theorem exists_isCompact_superset_iff_of_surjective
    (hX : Function.Surjective (pointProjection L X))
    (S : Set ((localizedFieldPointFunctor L).obj X)) :
    (∃ C, @IsCompact _ (pointTopology L X) C ∧ S ⊆ C) ↔
      ∃ C : Set (localizedSpaceFunctor.obj X), IsCompact C ∧ pointProjection L X '' S ⊆ C := by
  rw [exists_isCompact_superset_iff, hX.range_eq]
  simp only [Set.subset_univ, true_and]

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- `G` acts on the `L`-valued points of `X` by homeomorphisms: the underlying point
of `g • x` is the image of the underlying point of `x` under `ρ g`. -/
theorem continuousConstSMul_pointAction :
    letI := pointTopology L X
    letI := EtaleSite.pointAction L ρ
    ContinuousConstSMul G ((localizedFieldPointFunctor L).obj X) := by
  let := pointTopology L X
  let := EtaleSite.pointAction L ρ
  refine ⟨fun g => ?_⟩
  rw [continuous_induced_rng]
  have e : (pointProjection L X ∘ fun x => g • x) =
      localizedSpaceFunctor.map (ρ g).hom ∘ pointProjection L X :=
    funext fun x => pointProjection_map L (ρ g).hom x
  rw [e]
  exact (localizedSpaceFunctor.map (ρ g).hom).hom.continuous.comp continuous_induced_dom

end Topology

section Sites

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The étale site of `X` has `Hom`-types in `Type (max u v)` up to equivalence. -/
instance etaleSite_locallySmall : LocallySmall.{max u v} (EtaleSite X) :=
  locallySmall_of_faithful (MorphismProperty.Over.forget (etale (K := K)) ⊤ X)

/-- The étale site of `X` is locally small at the universe `max u (v + 1) uL` of the
points given by `L`-valued points. -/
theorem etaleSite_locallySmall_points : LocallySmall.{max u (v + 1) uL} (EtaleSite X) where
  hom_small U V := small_lift.{max u (v + 1), max u v, max u (v + 1) uL} (U ⟶ V)

end Sites

section Support

variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)

/-- The family of points of the étale site of `X` given by its `L`-valued points. -/
abbrev etalePoints (x : (localizedFieldPointFunctor L).obj X) :
    (etaleTopology X).Point.{max u (v + 1) uL} :=
  EtaleSite.toPoint L x (h x)

/-- A section of a module presheaf on the étale site is compactly supported for the
`L`-valued points exactly when the image of its support in `|X|` lies in a compact
set of underlying points of `L`-valued points. -/
theorem isCompactlySupported_etalePoints_iff {R : Type (max u (v + 1) uL)} [CommRing R]
    {F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R} {U : EtaleSite X}
    (s : F.obj (op U)) :
    letI := pointTopology L X
    IsCompactlySupported (etalePoints L h) F s ↔
      ∃ C : Set (localizedSpaceFunctor.obj X), IsCompact C ∧
        C ⊆ Set.range (pointProjection L X) ∧
          pointProjection L X '' support (etalePoints L h) F s ⊆ C :=
  exists_isCompact_superset_iff L _

end Support

section CompactSections

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Compactly supported global sections of module sheaves on the twisted étale site of
`X`, as representations of `G`; supports are taken in the `L`-valued points. -/
def etaleCompactSectionsRep :
    Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI : LocallySmall.{max u (v + 1) uL} (EtaleSite X) := etaleSite_locallySmall_points.{u, v, uL} X
  sheafCompactSectionsRep (etaleTopology X) R (EtaleSite.pointEquivariance L ρ h)

instance etaleCompactSectionsRep_additive : (etaleCompactSectionsRep L ρ h R).Additive :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI : LocallySmall.{max u (v + 1) uL} (EtaleSite X) := etaleSite_locallySmall_points.{u, v, uL} X
  inferInstanceAs (sheafCompactSectionsRep (etaleTopology X) R
    (EtaleSite.pointEquivariance L ρ h)).Additive

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Berkovich's `Γ_{c,X{G}}` on the twisted étale site: the smooth part of the
compactly supported global sections. -/
def etaleCompactSectionsSmooth :
    Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  etaleCompactSectionsRep L ρ h R ⋙ SmoothRep.smoothPartFunctor R G

instance etaleCompactSectionsSmooth_additive :
    (etaleCompactSectionsSmooth L ρ h R).Additive where
  map_add := rfl

/-- `Γ_{c,X{G}}` on Berkovich's étale `G`-sheaves. -/
def etaleGSheafCompactSections :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  (distinguishedLiftSystem ρ).smoothSheafInclusion _ _ ⋙ etaleCompactSectionsSmooth L ρ h R

end CompactSections

end Langlands.Sheaf.Equivariant.Analytic
