import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology

/-!
# Compact and ordinary étale cohomology on a compact analytic space

The inclusion of compactly supported sections in all sections is an isomorphism when
`|X|` is compact and every underlying point comes from an `L`-valued point. Deriving this
isomorphism identifies the two cohomology functors in every degree.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The natural inclusion of compactly supported étale sections into all sections. -/
def etaleCompactSectionsInclusion :
    etaleCompactSections L h R ⟶ etaleSections.{u, v, uL} X R :=
  letI := pointTopology L X
  Functor.whiskerLeft (sheafToPresheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (compactSectionsι (etalePoints L h) R (etaleSelf X))

/-- The inclusion sends a compactly supported section to its underlying section. -/
theorem etaleCompactSectionsInclusion_app_apply
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : (etaleCompactSections L h R).obj F) :
    (etaleCompactSectionsInclusion L h R).app F s = s.1 := rfl

/-- On compact `|X|` with surjective point projection, every section has compact support. -/
theorem isCompactlySupported_etalePoints_of_compactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X))
    {F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R} {U : EtaleSite X}
    (s : F.obj (op U)) :
    letI := pointTopology L X
    IsCompactlySupported (etalePoints L h) F s := by
  exact (exists_isCompact_superset_iff_of_surjective L hX _).2
    ⟨Set.univ, isCompact_univ, Set.subset_univ _⟩

/-- On compact `|X|` the inclusion of compactly supported sections is an isomorphism. -/
theorem isIso_etaleCompactSectionsInclusion_of_compactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X)) :
    IsIso (etaleCompactSectionsInclusion L h R) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨Subtype.val_injective, ?_⟩
  intro s
  exact ⟨⟨s, isCompactlySupported_etalePoints_of_compactSpace L h R hX s⟩, rfl⟩

/-- Compactly supported and ordinary sections agree on compact `|X|`. -/
def etaleCompactSectionsIsoOfCompactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X)) :
    etaleCompactSections L h R ≅ etaleSections.{u, v, uL} X R :=
  haveI := isIso_etaleCompactSectionsInclusion_of_compactSpace L h R hX
  asIso (etaleCompactSectionsInclusion L h R)

/-- Compactly supported and ordinary étale cohomology agree in every degree on compact
`|X|`, by deriving the inclusion of sections. -/
def etaleCompactCohomologyIsoOfCompactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X)) (q : ℕ) :
    etaleCompactCohomology L h R q ≅ etaleCohomology.{u, v, uL} X R q :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  let e := etaleCompactSectionsIsoOfCompactSpace L h R hX
  show (etaleCompactSections L h R).rightDerived q ≅
    (etaleSections.{u, v, uL} X R).rightDerived q from
  { hom := NatTrans.rightDerived e.hom q
    inv := NatTrans.rightDerived e.inv q
    hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
    inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id] }

/-- On compact `|X|`, vanishing of compactly supported and ordinary cohomology is equivalent. -/
theorem isZero_etaleCompactCohomology_iff_of_compactSpace
    [CompactSpace (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X)) (q : ℕ)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    IsZero ((etaleCompactCohomology L h R q).obj F) ↔
      IsZero ((etaleCohomology.{u, v, uL} X R q).obj F) := by
  let e := (etaleCompactCohomologyIsoOfCompactSpace L h R hX q).app F
  exact ⟨fun hz => IsZero.of_iso hz e.symm, fun hz => IsZero.of_iso hz e⟩

end Langlands.Sheaf.Equivariant.Analytic
