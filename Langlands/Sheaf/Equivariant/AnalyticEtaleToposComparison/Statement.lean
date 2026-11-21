import Mathlib.CategoryTheory.Adjunction.Restrict
import Langlands.Sheaf.Equivariant.AnalyticInverseImage

/-!
# The étale comparison with smooth analytic `G`-sheaves

The module-valued étale case of Berkovich's Theorem 1.4.2, stated through
smoothness of the inverse image and invertibility of the unit and counit of
its adjunction with invariant sections. Image pullbacks are the geometric
premise used to construct the inverse image and its right adjoint. The
proposition also assumes that every quotient of `G` by an open subgroup is
small in the geometric universe, so that Berkovich's coset-indexed spaces
`U_{G/N}` can exist in the site.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (X : GSpace.{u, v, v} K G) (R : Type (max u (v + 1) z uL)) [CommRing R]
variable (hX : HasImagePullbacks (EquivariantEtaleSite.toEtaleSite X))

/-- The smoothness clause: the actual inverse image of every sheaf on `X(G)_ét`
lands in the full subcategory of étale `G`-sheaves. -/
abbrev EtaleInverseImageSmooth : Prop :=
  ∀ E : Sheaf (equivariantEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R),
    (distinguishedLiftSystem X.obj.ρAut).smoothSheafProperty
      (ModuleCat.{max u (v + 1) z uL} R) (twistedEtaleTopology X.obj.ρAut)
      ((etaleSheafInverseImage.{u, v, uL, z} X R hX).obj E)

/-- Factor `b^*` through smooth `G`-sheaves given the smoothness clause. -/
def etaleSmoothInverseImage (h : EtaleInverseImageSmooth.{u, v, uL, z} X R hX) :
    Sheaf (equivariantEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R) ⥤
      EtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) z uL} R) :=
  ObjectProperty.lift _ (etaleSheafInverseImage.{u, v, uL, z} X R hX) h

/-- Restrict the published inverse-image/invariant-sections adjunction to the full
subcategory of smooth sheaves on the twisted site. -/
def etaleSmoothInverseImageAdjunction (h : EtaleInverseImageSmooth.{u, v, uL, z} X R hX) :
    etaleSmoothInverseImage.{u, v, uL, z} X R hX h ⊣ etaleGSheafInvariantSheaf X R hX :=
  (etaleSheafInverseImageAdjunction.{u, v, uL, z} X R hX).restrictFullyFaithful
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι
      ((distinguishedLiftSystem X.obj.ρAut).smoothSheafProperty
        (ModuleCat.{max u (v + 1) z uL} R) (twistedEtaleTopology X.obj.ρAut)))
    (Iso.refl _) (Iso.refl _)

/-- The size condition on `G` relative to the geometric universe `v`: every
quotient of `G` by an open subgroup is `v`-small. It allows the coset-indexed
induced spaces `U_{G/N}` to be objects of the site of `v`-small analytic spaces. -/
abbrev OpenQuotientsSmall : Prop :=
  ∀ N : OpenSubgroup G, Small.{v} (G ⧸ (N : Subgroup G))

/-- Berkovich, Theorem 1.4.2, étale case for module sheaves: when the
open-subgroup quotients of `G` are `v`-small, the actual inverse image is smooth
and the restricted adjunction is an equivalence. -/
def EtaleGSheafToposComparisonStatement [IsTopologicalGroup G] : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    ∃ h : EtaleInverseImageSmooth.{u, v, uL, z} X R hX,
      let adj := etaleSmoothInverseImageAdjunction.{u, v, uL, z} X R hX h
      IsIso adj.unit ∧ IsIso adj.counit

/-- The comparison proposition and the size condition yield an equivalence with
the specified smooth inverse image and invariant-sheaf functor. -/
def etaleGSheafEquivalenceOfStatement [IsTopologicalGroup G]
    (h : EtaleGSheafToposComparisonStatement.{u, v, uL, z} X R hX)
    (hG : OpenQuotientsSmall.{v, z} (G := G)) :
    Sheaf (equivariantEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R) ≌
      EtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) z uL} R) := by
  let adj := etaleSmoothInverseImageAdjunction.{u, v, uL, z} X R hX (h hG).choose
  haveI : IsIso adj.unit := (h hG).choose_spec.1
  haveI : IsIso adj.counit := (h hG).choose_spec.2
  exact adj.toEquivalence

end Langlands.Sheaf.Equivariant.Analytic
