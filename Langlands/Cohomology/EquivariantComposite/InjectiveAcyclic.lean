import Langlands.Cohomology.EquivariantComposite.CofreeAcyclic
import Langlands.Cohomology.EquivariantComposite.SmoothCompactComparison
import Langlands.Cohomology.EquivariantComposite.CompactFamilies
import Langlands.Sheaf.Equivariant.Godement.SmoothCoinduced

/-! # Compact sections of injective smooth sheaves are invariants-acyclic -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- Compact sections of the degree-zero smooth Godement sheaf are cofree. -/
def smoothGodementCompactCofreeIso (F : SmoothTopologicalSheaf R G X) :
    (smoothSheafCompactSections R G X).obj ((Godement.smoothZeroFunctor R G X).obj F) ≅
      cofreeObj R G (compactRows (CoinducedFamilies.Coefficients F.obj)) :=
  (smoothSheafCompactSections R G X).mapIso ((Godement.smoothZeroCoinducedIso R G X).app F) ≪≫
    (smoothCompactComparisonIso R G X).app (CoinducedFamilies.coinducedZero F.obj) ≪≫
    (SmoothCompactSections.smoothFunctor R G X).mapIso
      (CoinducedFamilies.coinducedZeroIso F.obj) ≪≫
    compactFamiliesCofreeIso (CoinducedFamilies.Coefficients F.obj)

/-- Higher invariants vanish on compact sections of every degree-zero smooth Godement sheaf. -/
theorem isZero_smoothGodementCompact_higherInvariants
    (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    IsZero (((invariants R G).rightDerived (q + 1)).obj
      ((smoothSheafCompactSections R G X).obj ((Godement.smoothZeroFunctor R G X).obj F))) :=
  IsZero.of_iso (isZero_cofree_higherInvariants R G _ q)
    (((invariants R G).rightDerived (q + 1)).mapIso (smoothGodementCompactCofreeIso R G X F))

/-- An injective smooth sheaf retracts off its monic Godement coaugmentation;
its compact sections are therefore acyclic for invariants. -/
theorem isZero_compactSections_higherInvariants_of_injective
    (I : SmoothTopologicalSheaf R G X) [Injective I] (q : ℕ) :
    IsZero (((invariants R G).rightDerived (q + 1)).obj
      ((smoothSheafCompactSections R G X).obj I)) := by
  let H := smoothSheafCompactSections R G X ⋙ (invariants R G).rightDerived (q + 1)
  let i := (Godement.smoothCoaugmentation R G X).app I
  let r := Injective.factorThru (𝟙 I) i
  have hr : i ≫ r = 𝟙 I := Injective.comp_factorThru (𝟙 I) i
  have hz : IsZero (H.obj ((Godement.smoothZeroFunctor R G X).obj I)) :=
    isZero_smoothGodementCompact_higherInvariants R G X I q
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (H.obj I) = 0
  calc
    𝟙 (H.obj I) = H.map i ≫ H.map r := by
      rw [← H.map_comp, hr]
      exact (H.map_id I).symm
    _ = 0 := by rw [hz.eq_of_src (H.map r) 0, comp_zero]

end Langlands.Cohomology.EquivariantComposite
