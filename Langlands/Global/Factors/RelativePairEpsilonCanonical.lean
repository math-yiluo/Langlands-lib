import Langlands.Global.Factors.RelativePairEpsilonWitnessed
import Langlands.Global.Factors.RelativePairEpsilonProduct
import Langlands.Global.Factors.RelativePairLFactorWitnessed

/-!
# The pair epsilon identity at the canonical additive character

Let `ψv` be the canonical component at `v` of the standard global additive character
and `νv` its self-dual measure. For every local-constant system and all witnessed
generators `d`, `e`, some `c q^(-ms)` is both the Weil virtual epsilon factor of
`(w_d, w_e)` and the virtual JPSS epsilon factor of `(a_d, a_e)`. Hence, by the span
reduction, the same holds on the graph of a generated positive isometry. The inputs
are the unitary support witnesses and the premise of Henniart's Corollary 2.3.
-/

noncomputable section

set_option autoImplicit false

universe uF uW uP uE

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The generator-level epsilon identity at the canonical additive character and its
self-dual measure, given Henniart's Corollary 2.3. -/
theorem witnessed_pairEpsilon_canonical
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hcomparison : RelativeWeilGroup.AssociatedTemperedFactorStatement.{uF, uW, uP, uP, uE})
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) :
    ∃ e' : ℂˣ × ℤ,
      LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε
        (canonicalLocalCharacter F v) d.weilElement e.weilElement e' ∧
      PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) (canonicalLocalCharacter F v)
        (Correspondence.localSelfDualHaar (padicField v) (canonicalLocalCharacter F v))
        d.automorphicElement e.automorphicElement e' := by
  let := (padicField v).canonicalTopologicalData.topology
  have hm := witnessed_isPairFactorMatch F E c v hc hcomparison d e
  let ψv := canonicalLocalCharacter F v
  let νv := Correspondence.localSelfDualHaar (padicField v) ψv
  have hνv : Correspondence.IsSelfDualMeasure (padicField v) ψv νv :=
    Correspondence.isSelfDual_localSelfDualHaar (padicField v) ψv
  obtain ⟨e', hAut, hAr⟩ := (hm.2.2 eC ε hε).2 νv hνv
  refine ⟨e', witnessed_isUnitaryPairEpsilonFactor_weil F E c v eC ε hε ψv d e hAr, ?_⟩
  obtain ⟨A, A', J, J', hA, hA', ⟨eJ⟩, ⟨eJ'⟩, hLang⟩ := hAut
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
  have hx : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v) J d.automorphicElement :=
    d.automorphic_support.of_iso (SmoothRep.mkIso (eJ.trans eA)).symm
  have hy : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v) J' e.automorphicElement :=
    e.automorphic_support.of_iso (SmoothRep.mkIso (eJ'.trans eA')).symm
  exact PadicSupercuspidal.isUnitaryPairEpsilonFactor_of_isLanglandsPairEpsilonFactor ψv νv hνv
    J J' hJirr hJirr' hx hy B σ hσ ((eJ.trans eA).trans eσ) C τ hτ ((eJ'.trans eA').trans eτ)
    hLang

/-- The pair epsilon clause on the graph of a generated positive isometry at the
canonical additive character and its self-dual measure, given Henniart's Corollary 2.3. -/
theorem relativePairEpsilon_canonical
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hcomparison : RelativeWeilGroup.AssociatedTemperedFactorStatement.{uF, uW, uP, uP, uE})
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (hT : RelativeGeneratedPositiveIsometry F E c v T)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    (x y : weilImage.{uF, uW, uP} F E c v) :
    ∃ e' : ℂˣ × ℤ,
      LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε
        (canonicalLocalCharacter F v) x.1 y.1 e' ∧
      PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) (canonicalLocalCharacter F v)
        (Correspondence.localSelfDualHaar (padicField v) (canonicalLocalCharacter F v))
        (T x).1 (T y).1 e' :=
  relativePairEpsilonFactor_of_witnessed F E c v T hT (canonicalLocalCharacter F v)
    (Correspondence.localSelfDualHaar (padicField v) (canonicalLocalCharacter F v))
    (Correspondence.isSelfDual_localSelfDualHaar (padicField v) (canonicalLocalCharacter F v))
    eC ε hε (LocalWeil.hasUnitaryBasisPairEpsilonFactors (padicField v) eC ε hε _)
    (witnessed_pairEpsilon_canonical F E c v hc hcomparison eC ε hε) x y

end Langlands.Global.PoleComparison
