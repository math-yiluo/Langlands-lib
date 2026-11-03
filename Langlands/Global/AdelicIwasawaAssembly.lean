import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.CoordinateCompactPatching
import Langlands.Global.IntegralIwasawaFamilyStatement
import Langlands.Global.AdelicIwasawaStatement

/-! # Conditional Iwasawa assembly on actual adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Extend a finite-place subgroup family to all places by the full subgroup at
each archimedean place. The archimedean members are later replaced if necessary. -/
def extendFinite
    (K : ∀ v : FinitePlace F, Subgroup (FinitePlaceGroupPoints F G v)) :
    ∀ i : Place F, Subgroup (PlaceGroupPoints F G i)
  | .inl _ => ⊤
  | .inr v => K v

/-- Actual adelic Iwasawa assembly from local existence at every place and one
almost-everywhere integral Iwasawa family. Both structural inputs are retained
as hypotheses. -/
theorem exists_parabolicIwasawaCompact_of_local_integral
    [IsAffine G.X.left]
    (P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P.X.left] (p : P ⟶ G)
    (hlocal : ∀ i : Place F, ∃ K : Subgroup (PlaceGroupPoints F G i),
      CoordinateCompactPatching.IsLocalIwasawaCompact
        (P.affinePointsTarget p (placeCompletion F i)) K)
    (K : ∀ v : FinitePlace F, Subgroup (FinitePlaceGroupPoints F G v))
    (hK : IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p K) :
    ∃ L : Subgroup (AdelicGroupPoints F G), IsParabolicIwasawaCompact F G P p L := by
  obtain ⟨hlocalK, habsorb, hintegral⟩ := hK
  have hint : IsUniformlyIntegral F G (extendFinite F G K) := hintegral
  exact CoordinateCompactPatching.exists_compact_maximal_cover_of_ae_local
    (fun i => (atPlace F G i : AdelicGroupPoints F G →* PlaceGroupPoints F G i))
    (map F P G p : AdelicGroupPoints F P →* AdelicGroupPoints F G)
    (fun i => (atPlace F P i : AdelicGroupPoints F P →* PlaceGroupPoints F P i))
    (fun i => P.affinePointsTarget p (placeCompletion F i))
    (extendFinite F G K) hlocal
    (eventually_place_of_finite F
      (hlocalK.mono fun v hv => ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩))
    (fun _ _ h => ext_atPlace F G h)
    (fun i => (atPlace F G i).continuous)
    (fun i b => atPlace_map F P p i b)
    (eventually_atPlace_mem_of_finite F G habsorb)
    (fun _ heq => (hint.of_eventuallyEq heq).compactProductLift)
    (fun q hq => exists_atPlace_eq_of_eventually_one F P q hq)

end Langlands.Global.AdelicGroupPoints
