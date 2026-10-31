import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.VirtualRepresentation.Weil.UnitaryExpansion
import Langlands.Weil.Representation.UnitaryRestriction

/-!
# Canonical effective expansions of full relative local restrictions

Restrict the actual unitary representation along its supplied continuous local
map and use the canonical exact coefficients. Genuine automorphic support
remains an explicit input to the witnessed-generator constructor.
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

/-- The full restriction has a canonical nonnegative unitary expansion on its
original carrier, without requiring an irreducible local restriction. -/
def localUnitaryExpansion
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hc : S.IsContinuous) (hu : S.IsUnitary)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    (effective : AddSubmonoid (LocalWeil.UnitaryLattice.{uF, uW} (padicField v))) :=
  LocalWeil.effectiveUnitaryExpansion (RelativeWeilGroup.localComponent S ι)
    (RelativeWeilGroup.localComponent_isContinuous ι hc)
    (FiniteRepresentation.isUnitary_restrict ι.toMonoidHom hu)

/-- Inclusion of the constructed coefficients recovers the entire local exact
class used by the existing relative-image construction. -/
theorem localUnitaryExpansion_spec
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hc : S.IsContinuous) (hu : S.IsUnitary)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    LocalWeil.ExactExpansion (padicField v) (localExactClass F E c v S hc ι)
      (LocalWeil.includeUnitary (padicField v)
        (localUnitaryExpansion F E c v S hc hu ι).val) :=
  LocalWeil.effectiveUnitaryExpansion_spec (RelativeWeilGroup.localComponent S ι)
    (RelativeWeilGroup.localComponent_isContinuous ι hc)
    (FiniteRepresentation.isUnitary_restrict ι.toMonoidHom hu)

/-- Restriction preserves the full carrier dimension, including rank zero. -/
@[simp]
theorem localUnitaryExpansion_degree
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hc : S.IsContinuous) (hu : S.IsUnitary)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    LocalWeil.unitaryDegree (padicField v)
      (localUnitaryExpansion F E c v S hc hu ι).val = (S.rank : ℤ) :=
  LocalWeil.effectiveUnitaryExpansion_degree (RelativeWeilGroup.localComponent S ι)
    (RelativeWeilGroup.localComponent_isContinuous ι hc)
    (FiniteRepresentation.isUnitary_restrict ι.toMonoidHom hu)

/-- Every full unitary-lattice expansion has these same coefficients; the
supplied expansion need not carry a positivity proof. -/
theorem localUnitaryExpansion_eq_of_expansion
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hc : S.IsContinuous) (hu : S.IsUnitary)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    {x : LocalWeil.UnitaryLattice.{uF, uW} (padicField v)}
    (hx : LocalWeil.ExactExpansion (padicField v) (localExactClass F E c v S hc ι)
      (LocalWeil.includeUnitary (padicField v) x)) :
    (localUnitaryExpansion F E c v S hc hu ι).val = x :=
  Weil.unitaryExactCoefficients_eq_of_expansion _ hx

/-- Actual invertible global intertwiners preserve the effective coefficients
at the fixed supplied local map. -/
theorem localUnitaryExpansion_eq_of_equiv
    {S T : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E)}
    (hcS : S.IsContinuous) (huS : S.IsUnitary)
    (hcT : T.IsContinuous) (huT : T.IsUnitary)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (e : FiniteRepresentation.Equiv S T) :
    localUnitaryExpansion F E c v S hcS huS ι =
      localUnitaryExpansion F E c v T hcT huT ι :=
  Weil.effectiveUnitaryExpansion_eq_of_equiv
    (RelativeWeilGroup.localComponent_isContinuous ι hcS)
    (FiniteRepresentation.isUnitary_restrict ι.toMonoidHom huS)
    (RelativeWeilGroup.localComponent_isContinuous ι hcT)
    (FiniteRepresentation.isUnitary_restrict ι.toMonoidHom huT)
    (FiniteRepresentation.restrictEquiv ι.toMonoidHom e)

variable [CompactSpace (AdeleQuotient F)]

namespace WitnessedGenerator

/-- Construct the existing witnessed generator from genuine associated objects
and actual automorphic support, filling all three Weil expansion fields. -/
def ofUnitarySupport
    {r : ℕ}
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hirr : S.IsIrreducible) (hu : S.IsUnitary)
    (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uP} T)
    (hassoc : RelativeWeilGroup.IsWeaklyAssociated S P.spectralSystem)
    (w : FinitePlacesAbove E v)
    (rec : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 rec ι)
    (hlirr : (P.localComponent v).IsIrreducible)
    (hladm : (P.localComponent v).IsAdmissible)
    (a : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v))
    (ha : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
      ((P.localComponent v).padicObject hlirr hladm).obj a) :
    WitnessedGenerator.{uF, uW, uP} F E c v where
  rankIndex := r
  weil := S
  weil_irreducible := hirr
  weil_unitary := hu
  cuspidal := T
  presentation := P
  associated := hassoc
  placeOver := w
  reciprocity := rec
  localMap := ι
  localMap_spec := hι
  local_irreducible := hlirr
  local_admissible := hladm
  weilElement := (localUnitaryExpansion F E c v S hassoc.1 hu ι).val
  weil_effective := (localUnitaryExpansion F E c v S hassoc.1 hu ι).property
  weil_expansion := localUnitaryExpansion_spec F E c v S hassoc.1 hu ι
  automorphicElement := a
  automorphic_support := ha

variable {F E c v}

/-- Existing witnessed generators already use the canonical Weil coefficients.
Only their automorphic support and other genuine data remain choices. -/
theorem weilElement_eq_localUnitaryExpansion
    (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    d.weilElement =
      (localUnitaryExpansion F E c v d.weil d.associated.1 d.weil_unitary d.localMap).val :=
  (localUnitaryExpansion_eq_of_expansion F E c v d.weil d.associated.1
    d.weil_unitary d.localMap d.weil_expansion).symm

end WitnessedGenerator

end Langlands.VirtualRepresentation.RelativeGlobal
