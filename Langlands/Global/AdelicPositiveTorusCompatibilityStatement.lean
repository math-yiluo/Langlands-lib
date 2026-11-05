import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Global.InfinitePlaceLeviIwasawaStatement
import Langlands.Global.AdelicGroupLocalPoints

/-! # Adelic positive-torus compatibility from supplied local Levi compacts -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- For every number field and affine ambient group scheme, split positive-torus
data and an all-test standard-Levi centralizer equality imply the actual
positive-torus compatibility of every adelic subgroup whose infinite-place
projections lie in supplied Levi-compatible Iwasawa compacts. -/
def AdelicPositiveTorusCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
    IsSplitTorus T₀.toGrp →
      standardLevi i ν ∅ = torusCentralizer i →
        ∀ (K : Subgroup (AdelicGroupPoints F G))
          (Karch : ∀ v : NumberField.InfinitePlace F,
            Subgroup (InfinitePlaceGroupPoints F G v)),
          (∀ v, InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G
            (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
            (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅) v (Karch v)) →
            (∀ v k, k ∈ K → atInfinitePlace F G v k ∈ Karch v) →
              IsPositiveTorusCompatible F G T i ν T₀ j K

end Langlands.Global.AdelicSiegelFactors
