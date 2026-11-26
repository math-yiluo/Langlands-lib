import Langlands.Global.Factors.RelativePairLFactorProduct
import Langlands.VirtualRepresentation.Global.WitnessedLocalMapConjugacy
import Langlands.Global.Factors.TemperedPoleRegions
import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.LocalFactor.UnitaryArithmeticPair
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupportInduction

/-!
# The pair L-factor identity for witnessed generators

The unitary supercuspidal support of each witnessed generator gives a tempered
automorphic component. Henniart's Corollary 2.3 compares the pair factors of these
components with those of the local Weil representations. JPSS multiplicativity
then gives the virtual pair L-factor identity.
-/

noncomputable section

set_option autoImplicit false

universe uF uW uP uE

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

/-- The zero-monodromy local pair class does not change when the local map is
conjugated by an element of the relative Weil group. -/
theorem localPairClass_eq_of_conj {F E : Type uF} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] {c : FundamentalClass.ClassFamily.{uF}}
    {v : FinitePlace F}
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (g : RelativeWeilGroup c F E) (hg : ∀ x, ι' x = g * ι x * g⁻¹) :
    RelativeWeilGroup.localPairClass S ι' = RelativeWeilGroup.localPairClass S ι :=
  ((WeilDeligneRepresentation.classOf_eq_iff _ _).2
    ⟨WeilDeligneRepresentation.zeroMonodromyCongr _
      (RelativeWeilGroup.localComponentConjEquiv S ι ι' g hg)⟩).symm

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The canonical component at `v` of the standard global additive character. -/
abbrev canonicalLocalCharacter : Correspondence.NontrivialAdditiveCharacter (padicField v) :=
  HeckeFunctionalEquation.standardFiniteAdditiveComponent F v

/-- A witnessed unitary support makes the corresponding local component tempered. -/
theorem witnessed_isTempered (d : WitnessedGenerator.{uF, uW, uP} F E c v) :
    letI := (padicField v).canonicalTopologicalData.topology
    (padicField v).canonicalTopologicalData.IsTempered
      ((d.presentation.localComponent v).padicObject d.local_irreducible
        d.local_admissible).obj.representation := by
  let := (padicField v).canonicalTopologicalData.topology
  obtain ⟨B, σ, hσ, ⟨eσ⟩⟩ := PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct
    d.rankIndex.succ_pos d.automorphic_support
  exact Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct
    (padicField v) d.rankIndex.succ_pos B σ hσ _ eσ

/-- Henniart's tempered comparison applies to two witnessed generators at the
canonical additive character, using the first generator's local map. -/
theorem witnessed_isPairFactorMatch
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hcomparison : RelativeWeilGroup.AssociatedTemperedFactorStatement.{uF, uW, uP, uP, uE})
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) :
    RelativeWeilGroup.IsPairFactorMatch.{uF, uW, uE} (padicField v)
      (canonicalLocalCharacter F v) (witnessedLocalClass F E c v d)
      (witnessedLocalClass F E c v e)
      (RelativeWeilGroup.localPairClass d.weil d.localMap)
      (RelativeWeilGroup.localPairClass e.weil d.localMap)
      (RelativeWeilGroup.localPairClass d.weil.dual d.localMap)
      (RelativeWeilGroup.localPairClass e.weil.dual d.localMap) :=
  hcomparison c hc F E (HeckeFunctionalEquation.standardGlobalAdditiveCharacter F)
    (HeckeFunctionalEquation.standardGlobalAdditiveCharacter_diagonal F)
    d.weil e.weil d.cuspidal e.cuspidal d.associatedClass e.associatedClass
    d.presentation e.presentation v d.local_irreducible d.local_admissible
    e.local_irreducible e.local_admissible (witnessed_isTempered F E c v d)
    (witnessed_isTempered F E c v e) d.placeOver d.reciprocity d.localMap d.localMap_spec
    (RelativeWeilGroup.localComponent_isUnitary d.localMap d.weil_unitary)
    (RelativeWeilGroup.localComponent_isUnitary d.localMap e.weil_unitary)
    (canonicalLocalCharacter F v)
    (HeckeFunctionalEquation.isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent F v)

/-- The pair L-factor identity for two witnessed generators and every self-dual
measure, given Henniart's Corollary 2.3. -/
theorem witnessed_isUnitaryPairLFactor
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hcomparison : RelativeWeilGroup.AssociatedTemperedFactorStatement.{uF, uW, uP, uP, uE})
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν)
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) :
    PadicSupercuspidal.IsUnitaryPairLFactor (padicField v) ψ ν
      d.automorphicElement e.automorphicElement
      (LocalWeil.unitaryPairLFactor (padicField v) d.weilElement e.weilElement) := by
  let := (padicField v).canonicalTopologicalData.topology
  obtain ⟨g, hg⟩ := WitnessedGenerator.exists_conj_localMap F E c v d e
  rw [witnessed_unitaryPairLFactor,
    localPairClass_eq_of_conj e.weil d.localMap e.localMap g hg]
  have hm := witnessed_isPairFactorMatch F E c v hc hcomparison d e
  let ψv := canonicalLocalCharacter F v
  let νv := Correspondence.localSelfDualHaar (padicField v) ψv
  have hνv : Correspondence.IsSelfDualMeasure (padicField v) ψv νv :=
    Correspondence.isSelfDual_localSelfDualHaar (padicField v) ψv
  obtain ⟨P, hP, hPL⟩ := hm.1.2 νv hνv
  rw [hPL]
  refine PadicSupercuspidal.IsUnitaryPairLFactor.change hνv hν ?_
  obtain ⟨A, A', J, J', hA, hA', ⟨eJ⟩, ⟨eJ'⟩, hLang⟩ := hP
  obtain ⟨B, σ, hσ, ⟨eσ⟩⟩ := PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct
    d.rankIndex.succ_pos d.automorphic_support
  obtain ⟨C, τ, hτ, ⟨eτ⟩⟩ := PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct
    e.rankIndex.succ_pos e.automorphic_support
  obtain ⟨eA⟩ := (Correspondence.automorphicClassOf_eq_iff _ A _).mp hA
  obtain ⟨eA'⟩ := (Correspondence.automorphicClassOf_eq_iff _ A' _).mp hA'
  have hJirr : Representation.IsIrreducible J.representation :=
    LengthTwo.isIrreducible_of_equiv (eJ.trans eA).symm
      ((d.presentation.localComponent v).padicObject d.local_irreducible
        d.local_admissible).property.1
  have hJirr' : Representation.IsIrreducible J'.representation :=
    LengthTwo.isIrreducible_of_equiv (eJ'.trans eA').symm
      ((e.presentation.localComponent v).padicObject e.local_irreducible
        e.local_admissible).property.1
  have hJt := Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct
    (padicField v) d.rankIndex.succ_pos B σ hσ J.representation ((eJ.trans eA).trans eσ)
  have hJt' := Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct
    (padicField v) e.rankIndex.succ_pos C τ hτ J'.representation ((eJ'.trans eA').trans eτ)
  have hsym := RankinSelberg.IsLanglandsPairLPolynomial.symmetric_of_tempered hLang hJirr hJt
    hJirr' hJt'
  have hx : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v) J d.automorphicElement :=
    d.automorphic_support.of_iso (SmoothRep.mkIso (eJ.trans eA)).symm
  have hy : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v) J' e.automorphicElement :=
    e.automorphic_support.of_iso (SmoothRep.mkIso (eJ'.trans eA')).symm
  exact PadicSupercuspidal.isUnitaryPairLFactor_of_equiv_productInduced ψv νv hνv J J' hJirr
    hJirr' hx hy B σ hσ ((eJ.trans eA).trans eσ) C τ hτ ((eJ'.trans eA').trans eτ) hsym

end Langlands.Global.PoleComparison
