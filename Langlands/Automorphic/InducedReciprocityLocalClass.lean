import Langlands.Automorphic.InducedReciprocityBasic
import Langlands.Global.Factors.RelativeWeilLocalHecke

/-!
# The local class of an induced reciprocity representation at a place with one place above

For `F ⊆ E' ⊆ L` with `L / F` Galois, a finite place `z` of `F` with exactly one place `u`
of `E'` above it, and a local map `ι : W_{F_z} → W_{L/F}`, Tate's local restriction formula
computes the restriction along `ι` of `Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` as the induction
along `W_{E'_u} → W_{F_z}` of the Weil character of the component `ξ_u`.
-/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField Langlands.VirtualRepresentation
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

attribute [local instance] relativeGaloisTopology

variable {c : FundamentalClass.ClassFamily.{u}} {F E' L : Type u} [Field F] [NumberField F]
  [Field E'] [NumberField E'] [Field L] [NumberField L] [Algebra F E'] [Algebra F L]
  [Algebra E' L] [IsScalarTower F E' L] [IsGalois F L]

theorem continuousRestrict_inducedReciprocityRepresentation_class
    (hN2 : LocalInducedRestrictionStatement.{uV, u})
    (h : FundamentalClass.Restriction c) (ξ : HeckeCharacter E')
    {z : Langlands.Global.FinitePlace F} (w : Langlands.Global.FinitePlace L)
    [w.asIdeal.LiesOver z.asIdeal]
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : KrullLocalMap c F L z) (hι : IsLocalRelativeWeilMap z w e ι)
    (u : Langlands.Global.FinitePlace E') [u.asIdeal.LiesOver z.asIdeal]
    [Subsingleton (FinitePlacesAbove E' z)]
    (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z u))
    (heu : LocalClassField.GeometricWeilReciprocityRelation (towerPadicField z u)
      (towerPadicField z u).canonicalTopologicalData eu) :
    ExactGrothendieckGroup.continuousRestrict (discreteLocalMap ι)
        (ExactGrothendieckGroup.ofRepresentation _
          ⟨inducedReciprocityRepresentation.{u, uV} c F E' L h ξ,
            inducedReciprocityRepresentation_isContinuous_discrete c F E' L h ξ⟩) =
      ExactGrothendieckGroup.continuousInduceAlong (completionWeilMap z u)
        (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
        (ExactGrothendieckGroup.characterClass.{u, uV}
          (LocalFactor.RankOne.weilCharacter (towerPadicField z u) eu
            (quasicharacterAt u (residuePrime_eq z u) (ξ.finiteComponent u)))) := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  obtain ⟨ιu, hτ, hres⟩ := hN2 c F E' L h z w e ι hι
  let u₀ : FinitePlacesAbove E' z := ⟨u, inferInstance⟩
  rw [inducedReciprocityRepresentation_class, hres, Fintype.sum_subsingleton _ u₀,
    ExactGrothendieckGroup.continuousRestrict_characterClass,
    continuousReciprocityCharacter_comp_eq_weilCharacter ξ u (residuePrime_eq z u) eu (ιu u₀)
      (hτ u₀ eu heu)]

end Langlands.ClassField.Global.RelativeWeilGroup
