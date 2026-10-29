import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Langlands.Automorphic.PadicLocalCategory
import Langlands.VirtualRepresentation.Weil.ExactRealization
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport
import Langlands.VirtualRepresentation.Presentation

/-!
# Integral images of witnessed relative global pairs

The index retains actual relative Weil and cuspidal objects, a characterized
local map, and expansions of their full local components. No local expansion
or absolute global comparison is chosen or asserted to exist.
-/

noncomputable section

universe uF uW uP

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The actual full local restriction, in continuous exact K0. -/
def localExactClass
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    LocalWeil.ContinuousExactGroup.{uF, uW} (padicField v) :=
  ExactGrothendieckGroup.ofRepresentation _
    ⟨RelativeWeilGroup.localComponent S ι,
      RelativeWeilGroup.localComponent_isContinuous ι hS⟩

/-- Restriction retains the whole carrier and its dimension. -/
@[simp]
theorem localExactClass_degree
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    ExactGrothendieckGroup.degree _
      (localExactClass F E c v S hS ι) = (S.rank : ℤ) := by
  rw [localExactClass, ExactGrothendieckGroup.degree_ofRepresentation]
  rfl

variable [CompactSpace (AdeleQuotient F)]

/-- Actual associated objects together with full local expansion witnesses.
The automorphic support carriers have the universe of the actual form space;
the Weil and presentation-factor carriers have independent universes. -/
structure WitnessedGenerator where
  rankIndex : ℕ
  weil : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E)
  weil_irreducible : weil.IsIrreducible
  weil_unitary : weil.IsUnitary
  cuspidal : CuspidalOperatorRealization F rankIndex
  presentation : CuspidalSpectralPresentation.{uF, uP} cuspidal
  associated : RelativeWeilGroup.IsWeaklyAssociated weil presentation.spectralSystem
  placeOver : FinitePlacesAbove E v
  reciprocity : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v placeOver.1)
  localMap : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E
  localMap_spec : RelativeWeilGroup.IsLocalRelativeWeilMap v placeOver.1 reciprocity localMap
  local_irreducible : (presentation.localComponent v).IsIrreducible
  local_admissible : (presentation.localComponent v).IsAdmissible
  weilElement : LocalWeil.UnitaryLattice.{uF, uW} (padicField v)
  weil_effective : weilElement ∈ effective
  weil_expansion : LocalWeil.ExactExpansion (padicField v)
    (localExactClass F E c v weil associated.1 localMap)
    (LocalWeil.includeUnitary (padicField v) weilElement)
  automorphicElement : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)
  automorphic_support : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
    ((presentation.localComponent v).padicObject local_irreducible local_admissible).obj
    automorphicElement

namespace WitnessedGenerator

variable {F E c v}
variable (d : WitnessedGenerator.{uF, uW, uP} F E c v)

/-- Weak association retains the actual full cuspidal class. -/
theorem associatedClass :
    RelativeWeilGroup.IsWeaklyAssociatedClass.{uF, uW, uP}
      d.weil d.cuspidal.isoClass :=
  (RelativeWeilGroup.isWeaklyAssociatedClass_isoClass_iff d.weil d.cuspidal).mpr
    ⟨d.presentation, d.associated⟩

/-- An explicit full exact expansion has the global representation's rank. -/
theorem weil_degree :
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
      ((d.rankIndex + 1 : ℕ) : ℤ) := by
  calc
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
        ExactGrothendieckGroup.degree _
          (LocalWeil.realizeExact (padicField v)
            (LocalWeil.includeUnitary (padicField v) d.weilElement)) :=
      (LocalWeil.degree_realizeExact _ _).symm
    _ = ExactGrothendieckGroup.degree _
        (localExactClass F E c v d.weil d.associated.1 d.localMap) :=
      congrArg _ d.weil_expansion
    _ = (d.weil.rank : ℤ) := localExactClass_degree _ _ _ _ _ _ _
    _ = ((d.rankIndex + 1 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) d.associated.2.1

/-- Actual normalized-induction support has the general linear group rank. -/
theorem automorphic_degree :
    PadicSupercuspidal.unitaryDegree (padicField v) d.automorphicElement =
      ((d.rankIndex + 1 : ℕ) : ℤ) :=
  d.automorphic_support.degree

theorem degrees_eq :
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
      PadicSupercuspidal.unitaryDegree (padicField v) d.automorphicElement :=
  d.weil_degree.trans d.automorphic_degree.symm

theorem automorphic_effective : d.automorphicElement ∈ effective :=
  d.automorphic_support.effective

end WitnessedGenerator

/-- The integral span of all actual witnessed relative pairs at this place. -/
def pairedLattice :
    Submodule ℤ (LocalWeil.UnitaryLattice.{uF, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)) :=
  generatedPairs
    (fun d : WitnessedGenerator.{uF, uW, uP} F E c v => d.weilElement)
    (fun d => d.automorphicElement)

/-- The Weil image generated by the full witnessed local restrictions. -/
def weilImage : Submodule ℤ (LocalWeil.UnitaryLattice.{uF, uW} (padicField v)) :=
  generated (fun d : WitnessedGenerator.{uF, uW, uP} F E c v => d.weilElement)

/-- The automorphic image generated by actual unitary supercuspidal supports. -/
def automorphicImage :
    Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)) :=
  generated (fun d : WitnessedGenerator.{uF, uW, uP} F E c v => d.automorphicElement)

/-- Projection retains membership in the actual Weil generated span. -/
def weilProjection :
    pairedLattice.{uF, uW, uP} F E c v →ₗ[ℤ] weilImage.{uF, uW, uP} F E c v :=
  pairLeft _ _

/-- Projection retains membership in the actual support generated span. -/
def automorphicProjection :
    pairedLattice.{uF, uW, uP} F E c v →ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v :=
  pairRight _ _

variable {F E c v}

theorem witnessed_pair_mem (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    (d.weilElement, d.automorphicElement) ∈ pairedLattice.{uF, uW, uP} F E c v :=
  Submodule.subset_span (Set.mem_range_self d)

theorem witnessed_weil_mem (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    d.weilElement ∈ weilImage.{uF, uW, uP} F E c v :=
  Submodule.subset_span (Set.mem_range_self d)

theorem witnessed_automorphic_mem (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    d.automorphicElement ∈ automorphicImage.{uF, uW, uP} F E c v :=
  Submodule.subset_span (Set.mem_range_self d)

/-- Equal generator degrees extend to every signed integral pair in the span. -/
theorem degrees_eq_of_mem
    {x : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)}
    (hx : x ∈ pairedLattice.{uF, uW, uP} F E c v) :
    LocalWeil.unitaryDegree (padicField v) x.1 =
      PadicSupercuspidal.unitaryDegree (padicField v) x.2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact d.degrees_eq
  | zero => simp
  | add x y hx hy ihx ihy => simp only [Prod.fst_add, Prod.snd_add, map_add, ihx, ihy]
  | smul a x hx ih =>
    change LocalWeil.unitaryDegree (padicField v) (a • x.1) =
      PadicSupercuspidal.unitaryDegree (padicField v) (a • x.2)
    rw [map_smul, map_smul, ih]

/-- Every Weil image element lifts to a pair in the actual paired span. -/
theorem exists_pair_of_mem_weilImage
    {x : LocalWeil.UnitaryLattice.{uF, uW} (padicField v)}
    (hx : x ∈ weilImage.{uF, uW, uP} F E c v) :
    ∃ y, (x, y) ∈ pairedLattice.{uF, uW, uP} F E c v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact ⟨d.automorphicElement, witnessed_pair_mem d⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, Submodule.add_mem _ ha hb⟩
  | smul a x hx ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a • b, Submodule.smul_mem _ a hb⟩

/-- Every support image element lifts to a pair in the actual paired span. -/
theorem exists_pair_of_mem_automorphicImage
    {y : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)}
    (hy : y ∈ automorphicImage.{uF, uW, uP} F E c v) :
    ∃ x, (x, y) ∈ pairedLattice.{uF, uW, uP} F E c v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, rfl⟩ := hy
    exact ⟨d.weilElement, witnessed_pair_mem d⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, Submodule.add_mem _ ha hb⟩
  | smul a x hx ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a • b, Submodule.smul_mem _ a hb⟩

theorem weilProjection_surjective :
    Function.Surjective (weilProjection.{uF, uW, uP} F E c v) := by
  intro x
  obtain ⟨y, hy⟩ := exists_pair_of_mem_weilImage x.property
  exact ⟨⟨(x.val, y), hy⟩, Subtype.ext rfl⟩

theorem automorphicProjection_surjective :
    Function.Surjective (automorphicProjection.{uF, uW, uP} F E c v) := by
  intro y
  obtain ⟨x, hx⟩ := exists_pair_of_mem_automorphicImage y.property
  exact ⟨⟨(x, y.val), hx⟩, Subtype.ext rfl⟩

end Langlands.VirtualRepresentation.RelativeGlobal
