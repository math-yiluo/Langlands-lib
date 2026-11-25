import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! # Archimedean standard-module components of cuspidal realizations

At an infinite place `v`, an actual cuspidal realization `T` of `GL_{r+1}` has the
standard-module parameter `ds` (`OperatorRealization.HasRealPlaceParameter`,
`OperatorRealization.HasComplexPlaceParameter`) when the `K_v`-finite functions of the
standard module of `ds` map injectively and `(𝔤_v, K_v)`-equivariantly into `T`. This module
states that such a standard module is the archimedean component of `T` in the sense used by
Getz–Hahn (2024), §11.4–§11.7, and derives the archimedean regularity used in the proof of
Getz–Hahn, Theorem 11.7.2:

* `ArchimedeanStandardAdmissibleStatement`: every real and complex standard module is an
  admissible `(𝔤, K)`-module;
* `CuspidalArchimedeanStandardIrreducibleStatement`: a standard module that is a parameter of
  an actual cuspidal realization is irreducible;
* `CuspidalArchimedeanStandardGenericStatement`: it is generic;
* `CuspidalArchimedeanStandardUnitarizableStatement`: if the central character of the
  realization is unitary, it is unitarizable;
* `CuspidalArchimedeanPairRegularityStatement`: for two actual cuspidal realizations with
  unitary central characters and parameters `ds`, `ds'` at the same infinite place, the
  archimedean pair `L`-factor `L(s, ds × ds')` has no pole on `Re(s) ≥ 1`;
* `CuspidalArchimedeanPairRegularityReductionStatement`: the four component statements and the
  archimedean case of Getz–Hahn, Theorem 11.5.2 (`Archimedean.RealUnitaryGenericPairRegularity
  Statement`, `Archimedean.ComplexUnitaryGenericPairRegularityStatement`) imply the pair
  regularity.

These are statements, not proofs.
-/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every real standard module and every complex standard module is admissible: for every
continuous finite-dimensional matrix representation of `O(n)` (resp. `U(n)`), the space of
`K`-intertwiners from it into the `K`-finite functions of the standard module is
finite-dimensional. -/
def ArchimedeanStandardAdmissibleStatement : Prop :=
  (∀ (n : ℕ) (ds : List RealBlock),
    Archimedean.IsAdmissibleGKModule (Archimedean.realStandardRep n ds)) ∧
  ∀ (n : ℕ) (ds : List ComplexCharacterData),
    Archimedean.IsAdmissibleGKModule (Archimedean.complexStandardRep n ds)

/-- **Irreducible archimedean components.** Let `T` be an actual cuspidal realization of
`GL_{r+1}` over a number field `F`. If `T` has the standard-module parameter `ds` at a real
place `v`, the `(𝔤𝔩_{r+1}(ℝ), O(r+1))`-module of the standard module of `ds` is irreducible;
if `T` has the parameter `ds` at a complex place `v`, the `(𝔤𝔩_{r+1}(ℂ), U(r+1))`-module of
the standard module of `ds` is irreducible. -/
def CuspidalArchimedeanStandardIrreducibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock),
      T.realization.HasRealPlaceParameter v ds →
        Archimedean.IsIrreducibleGKModule (Archimedean.realStandardRep (r + 1) ds)
          (Archimedean.realStandardLie (r + 1) ds)) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData),
      T.realization.HasComplexPlaceParameter v ds →
        Archimedean.IsIrreducibleGKModule (Archimedean.complexStandardRep (r + 1) ds)
          (Archimedean.complexStandardLie (r + 1) ds)

/-- **Generic archimedean components.** Let `T` be an actual cuspidal realization of
`GL_{r+1}` over a number field `F`. If `T` has the standard-module parameter `ds` at a real
(resp. complex) place `v`, the `(𝔤, K)`-module of the standard module of `ds` is generic: it
carries a nonzero Whittaker functional for some nondegenerate character of the upper
unipotent Lie algebra. -/
def CuspidalArchimedeanStandardGenericStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock),
      T.realization.HasRealPlaceParameter v ds →
        Archimedean.IsRealGenericGKModule (r + 1) (Archimedean.realStandardLie (r + 1) ds)) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData),
      T.realization.HasComplexPlaceParameter v ds →
        Archimedean.IsComplexGenericGKModule (r + 1)
          (Archimedean.complexStandardLie (r + 1) ds)

/-- **Unitarizable archimedean components.** Let `T` be an actual cuspidal realization of
`GL_{r+1}` over a number field `F` with unitary central character. If `T` has the
standard-module parameter `ds` at a real (resp. complex) place `v`, the `(𝔤, K)`-module of the
standard module of `ds` is unitarizable: it has a positive definite Hermitian form invariant
under `K` and skew under the real Lie algebra. -/
def CuspidalArchimedeanStandardUnitarizableStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock),
      T.realization.HasRealPlaceParameter v ds →
        Archimedean.IsRealUnitarizableGKModule (r + 1) (Archimedean.realStandardRep (r + 1) ds)
          (Archimedean.realStandardLie (r + 1) ds)) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData),
      T.realization.HasComplexPlaceParameter v ds →
        Archimedean.IsComplexUnitarizableGKModule (r + 1)
          (Archimedean.complexStandardRep (r + 1) ds)
          (Archimedean.complexStandardLie (r + 1) ds)

/-- **Archimedean pair regularity of unitary cuspidal realizations** (the archimedean input
of Getz–Hahn (2024), p. 309). Let `T` and `T'` be actual cuspidal realizations of
`GL_{r+1}` and `GL_{t+1}` over a number field `F`, both with unitary central characters. If
`ds` and `ds'` are standard-module parameters of `T` and `T'` at the same real (resp.
complex) place, the archimedean pair `L`-factor `L(s, ds × ds') = 1 / P(s)` has no pole on
`Re(s) ≥ 1`: its entire denominator `P` does not vanish there. -/
def CuspidalArchimedeanPairRegularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T' →
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds ds' : List RealBlock),
      T.realization.HasRealPlaceParameter v ds →
      T'.realization.HasRealPlaceParameter v ds' →
        ∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
      (ds ds' : List ComplexCharacterData),
      T.realization.HasComplexPlaceParameter v ds →
      T'.realization.HasComplexPlaceParameter v ds' →
        ∀ s : ℂ, 1 ≤ s.re → (complexPairLFactor ds ds').denominator s ≠ 0

/-- The admissibility, irreducibility, genericity and unitarizability of the archimedean
standard-module components, together with the archimedean case of Getz–Hahn, Theorem 11.5.2,
for carriers in `Type`, imply the archimedean pair regularity of unitary cuspidal
realizations. -/
def CuspidalArchimedeanPairRegularityReductionStatement : Prop :=
  ArchimedeanStandardAdmissibleStatement →
    CuspidalArchimedeanStandardIrreducibleStatement.{u} →
      CuspidalArchimedeanStandardGenericStatement.{u} →
        CuspidalArchimedeanStandardUnitarizableStatement.{u} →
          Archimedean.RealUnitaryGenericPairRegularityStatement.{0, 0} →
            Archimedean.ComplexUnitaryGenericPairRegularityStatement.{0, 0} →
              CuspidalArchimedeanPairRegularityStatement.{u}

end Langlands.Automorphic
