import Langlands.Global.AdelicEisensteinRootHyperplaneCompactReduction
import Langlands.Global.AdelicStandardLeviCompactAssembly
import Langlands.Global.InfinitePlaceStandardLeviCompact
import Langlands.Global.FinitePlaceStandardLeviCompact
import Langlands.Global.InfiniteAdelicMaximalCompactConjugacy
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicEisensteinFamilyCompactConjugation

/-! # Compacts in good position and their archimedean conjugates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Bruhat–Tits theory supplies, for every standard family, a maximal compact subgroup in good
position: Iwasawa for the minimal standard parabolic and with maximal compact intersections
with all standard Levis. -/
theorem StandardParabolicFamily.exists_goodCompact
    (hBT : Langlands.Geometry.Building.BruhatTitsAvailabilityStatement.{u})
    (fam : StandardParabolicFamily F G) :
    ∃ K : Subgroup (AdelicGroupPoints F G), IsMaximalCompactSubgroup F G K ∧
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K ∧
      ∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom) := by
  have hlocal : ∀ v : Place F, ∃ L : Subgroup (PlaceGroupPoints F G v),
      fam.IsStandardLeviCompact v L := by
    rintro (v | v)
    · exact InfinitePlaceGroupPoints.infinitePlaceStandardLeviCompact F G fam v
    · exact FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction hBT F G fam v
  obtain ⟨K, ⟨hKmax, hKcov⟩, hKlevi⟩ := fam.standardLeviCompactAssembly hlocal
  exact ⟨K, hKmax, ⟨hKmax.1, hKcov⟩, hKlevi⟩

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- **Archimedean matching of a good compact.** Given maximal compact subgroups `K` and `K₀`,
there is an archimedean point `s` such that `C = t⁻¹ K₀ t` (`t = ofInfinite s`) is maximal
compact with the same infinite projection as `K`. -/
theorem exists_archimedeanConjugate_infinite_eq (hG : IsConnectedReductive G)
    {K K₀ : Subgroup (AdelicGroupPoints F G)} (hK : IsMaximalCompactSubgroup F G K)
    (hK₀ : IsMaximalCompactSubgroup F G K₀) :
    ∃ s : InfiniteAdelicGroupPoints F G,
      IsMaximalCompactSubgroup F G (K₀.map (MulAut.conj (ofInfinite F G s)⁻¹).toMonoidHom) ∧
      K.map (infinite F G).toMonoidHom =
        (K₀.map (MulAut.conj (ofInfinite F G s)⁻¹).toMonoidHom).map (infinite F G).toMonoidHom := by
  obtain ⟨a, ha⟩ := InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy F G
    (K₀.comap (ofInfinite F G).toMonoidHom) (K.comap (ofInfinite F G).toMonoidHom) hG
    (IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite hK₀)
    (IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite hK)
  have hC := AdelicGroupPoints.IsMaximalCompactSubgroup.map_conj hK₀ (ofInfinite F G a⁻¹)⁻¹
  refine ⟨a⁻¹, hC, ?_⟩
  rw [← AdelicGroupPoints.IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite hK,
    ← AdelicGroupPoints.IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite hC, ← ha]
  have h := comap_ofInfinite_map_conj K₀ a⁻¹
  -- `(C.comap ofInfinite).map (conj a⁻¹) = K₀.comap ofInfinite`
  have hid : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp [mul_assoc]
  rw [← h, Subgroup.map_map, hid, Subgroup.map_id]

end Langlands.Global
