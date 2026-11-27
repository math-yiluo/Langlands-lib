import Langlands.Sheaf.Equivariant.AnalyticEtaleToposComparison.Statement
import Langlands.Sheaf.Equivariant.AnalyticCompactProbeInverseImage

/-!
# Quasi-étale comparison with smooth analytic `G`-sheaves

The module-valued quasi-étale case of Berkovich's Theorem 1.4.2, for the
inverse image and the invariant-sheaf functors of the equivariant site.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf (HasImagePullbacks)

namespace Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (X : GSpace.{u, v, v} K G) (R : Type (max u (v + 1) z uL)) [CommRing R]
variable (hX : HasImagePullbacks (EquivariantQuasiEtaleSite.toQuasiEtaleSite X))

/-- The inverse image of every module sheaf on `X(G)_qét` is a quasi-étale
`G`-sheaf, with discrete sections for the lifts on compact test objects. -/
abbrev CompactProbeQuasiEtaleInverseImageDiscrete : Prop :=
  ∀ E : Sheaf (equivariantCompactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R),
    (compactLiftSystem X.obj.ρAut).discreteSheafProperty
      (ModuleCat.{max u (v + 1) z uL} R) (twistedCompactProbeQuasiEtaleTopology X.obj.ρAut)
      ((compactProbeQuasiEtaleInverseImage.{u, v, z, uL} X R).obj E)

/-- Factor `b^*` through the full subcategory of quasi-étale `G`-sheaves. -/
def compactProbeQuasiEtaleDiscreteInverseImage
    (h : CompactProbeQuasiEtaleInverseImageDiscrete.{u, v, uL, z} X R) :
    Sheaf (equivariantCompactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) z uL} R) ⥤
      CompactProbeQuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) z uL} R) :=
  ObjectProperty.lift _ (compactProbeQuasiEtaleInverseImage.{u, v, z, uL} X R) h

/-- Restrict the inverse-image/invariant-sheaf adjunction to the discrete
sheaves on the twisted quasi-étale site. -/
def compactProbeQuasiEtaleDiscreteInverseImageAdjunction
    (h : CompactProbeQuasiEtaleInverseImageDiscrete.{u, v, uL, z} X R) :
    compactProbeQuasiEtaleDiscreteInverseImage.{u, v, uL, z} X R h ⊣
      ObjectProperty.ι _ ⋙ compactProbeQuasiEtaleInvariantSheaf.{u, v, z, uL} X R hX :=
  (compactProbeQuasiEtaleInverseImageAdjunction.{u, v, z, uL} X R hX).restrictFullyFaithful
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι
      ((compactLiftSystem X.obj.ρAut).discreteSheafProperty
        (ModuleCat.{max u (v + 1) z uL} R) (twistedCompactProbeQuasiEtaleTopology X.obj.ρAut)))
    (Iso.refl _) (Iso.refl _)

/-- Berkovich, Theorem 1.4.2, quasi-étale case for module sheaves: for
`v`-small open-subgroup quotients, `b^*` has discrete sections over compact
objects and its adjunction with `(b_*-)^G` is an equivalence. -/
def CompactProbeQuasiEtaleGSheafToposComparisonStatement [IsTopologicalGroup G] : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    ∃ h : CompactProbeQuasiEtaleInverseImageDiscrete.{u, v, uL, z} X R,
      let adj := compactProbeQuasiEtaleDiscreteInverseImageAdjunction.{u, v, uL, z} X R hX h
      IsIso adj.unit ∧ IsIso adj.counit

end Langlands.Sheaf.Equivariant.Analytic
