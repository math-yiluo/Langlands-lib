import Langlands.ClassFieldTheory.Global.LocalUnitVanishing
import Langlands.ClassFieldTheory.Global.IdeleLocalInjectivity
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.ClassFieldTheory.Local.RelativeInvariantEquivalences
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# The units of an unramified completion are cohomologically trivial

Let `E / F` be a finite Galois extension of number fields and `w | v` finite places with
ramification index `1`. Then `Hⁿ(Gal(E_w/F_v), U_w) = 0` for every `n ≥ 1`, where `U_w` are the
valuation units of `E_w`: in degree one because a fixed uniformizer splits `U_w → E_wˣ` and
`H¹(Gal(E_w/F_v), E_wˣ) = 0`; in degree two by the Library's `isZero_H2_localUnits`, whose
hypothesis on the order of `H²(Gal(E_w/F_v), E_wˣ)` is the local class formation; in higher degrees
by the periodicity of the cohomology of the cyclic group `Gal(E_w/F_v)`. The same holds for the
module `Coind(U_w)` of `Gal(E/F)` coinduced along `decompositionHom v w` (Shapiro's lemma).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic FundamentalClass
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

section Periodicity

variable {k G : Type u} [CommRing k] [Group G] [Finite G] [IsCyclic G] (A : Rep.{u} k G)

/-- For a finite cyclic group, cohomology in odd degree `n` is isomorphic to `H¹`. -/
theorem isZero_groupCohomology_odd (h1 : IsZero (groupCohomology A 1)) (n : ℕ) (hn : Odd n) :
    IsZero (groupCohomology A n) := by
  classical
  let _ : CommGroup G := IsCyclic.commGroup
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact h1.of_iso (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm)

/-- For a finite cyclic group, cohomology in even degree `n ≠ 0` is isomorphic to `H²`. -/
theorem isZero_groupCohomology_even (h2 : IsZero (groupCohomology A 2)) (n : ℕ) [NeZero n]
    (hn : Even n) : IsZero (groupCohomology A n) := by
  classical
  let _ : CommGroup G := IsCyclic.commGroup
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact h2.of_iso (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg n hn ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm)

/-- For a finite cyclic group, vanishing of `H¹` and `H²` gives vanishing in every degree `≥ 1`. -/
theorem isZero_groupCohomology_succ_of_isCyclic (h1 : IsZero (groupCohomology A 1))
    (h2 : IsZero (groupCohomology A 2)) (n : ℕ) : IsZero (groupCohomology A (n + 1)) := by
  rcases Nat.even_or_odd (n + 1) with hn | hn
  · exact isZero_groupCohomology_even A h2 (n + 1) hn
  · exact isZero_groupCohomology_odd A h1 (n + 1) hn

end Periodicity

section LocalUnits

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Hilbert 90 for a completion: `H¹(Gal(E_w/F_v), E_wˣ) = 0`. -/
theorem subsingleton_relativeCohomology_one_adicCompletion :
    Subsingleton (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 1) := by
  have := isGalois_adicCompletion v w
  have := FiniteExtension.local_finite v w
  obtain ⟨I, -, hRCF, -⟩ := localRelativeClassFormation.{u} (residuePrime v)
  exact hRCF.1 (padicField v) (w.adicCompletion E)

/-- The order of `H²(Gal(E_w/F_v), E_wˣ)` is `[E_w : F_v]`, and the group is finite. -/
theorem finite_relativeCohomology_two_adicCompletion :
    Finite (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) ∧
      Nat.card (relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) =
        Module.finrank (v.adicCompletion F) (w.adicCompletion E) := by
  have := isGalois_adicCompletion v w
  have := FiniteExtension.local_finite v w
  obtain ⟨I, -, hRCF, -⟩ := localRelativeClassFormation.{u} (residuePrime v)
  exact ⟨I.relativeH2_finite hRCF.2.1 (padicField v) _, I.relativeH2_card hRCF.2.1 (padicField v) _⟩

/-- At an unramified place, `H¹(Gal(E_w/F_v), U_w) = 0`: the inclusion `U_w → E_wˣ` has a
retraction and `H¹(Gal(E_w/F_v), E_wˣ) = 0`. -/
theorem isZero_H1_localUnits (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    IsZero (groupCohomology (localUnitsRepresentation v w) 1) := by
  obtain ⟨π, hπ1, hπ⟩ := exists_fixed_uniformizer v w he
  have hri := localUnitsInclusion_comp_unitsRetraction v w hπ1 hπ
  have hsub := subsingleton_relativeCohomology_one_adicCompletion v w
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  have key : ∀ c : groupCohomology (localUnitsRepresentation v w) 1, c = 0 := by
    intro c
    have hc : groupCohomology.map (MonoidHom.id _) (unitsRetraction hπ1 hπ) 1
        (groupCohomology.map (MonoidHom.id _) (localUnitsInclusion v w) 1 c) = c := by
      rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_id_comp, hri,
        groupCohomology.map_id]
      rfl
    rw [← hc, show groupCohomology.map (MonoidHom.id _) (localUnitsInclusion v w) 1 c = 0 from
      Subsingleton.elim (α := relativeCohomology (padicField v).Carrier (w.adicCompletion E) 1)
        _ _, map_zero]
  rw [key a, key b]

/-- At an unramified place, `H²(Gal(E_w/F_v), U_w) = 0`. -/
theorem isZero_H2_localUnits_of_ramificationIdx (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    IsZero (groupCohomology (localUnitsRepresentation v w) 2) := by
  obtain ⟨hfin, hcard⟩ := finite_relativeCohomology_two_adicCompletion v w
  exact isZero_H2_localUnits v w he (le_of_eq hcard)

/-- **Unramified units are cohomologically trivial**: at a place `w | v` with ramification index
`1`, `Hⁿ⁺¹(Gal(E_w/F_v), U_w) = 0` for every `n`. -/
theorem isZero_groupCohomology_localUnits (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (n : ℕ) :
    IsZero (groupCohomology (localUnitsRepresentation v w) (n + 1)) := by
  have := FiniteExtension.local_finite v w
  have := isCyclic_localGal v w he
  exact isZero_groupCohomology_succ_of_isCyclic _ (isZero_H1_localUnits v w he)
    (isZero_H2_localUnits_of_ramificationIdx v w he) n

/-- The same for the coinduced module `Coind(U_w)` of `Gal(E/F)` (Shapiro's lemma). -/
theorem isZero_groupCohomology_coindLocalUnits (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (n : ℕ) :
    IsZero (groupCohomology (Rep.coind (decompositionHom v w) (localUnitsRepresentation v w))
      (n + 1)) :=
  (isZero_groupCohomology_localUnits v w he n).of_iso
    (Shapiro.shapiroIsoOf (decompositionHom_injective v w) _ (n + 1))

end LocalUnits

end Langlands.GaloisCohomology
