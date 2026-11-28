import Langlands.Correspondence.HenniartCyclicBaseChange
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.Arithmetic.HenniartHarrisDatumStatement
import Langlands.Global.CompletionPadic

/-! # Common CM bases for the two sides of a cyclic step -/

set_option autoImplicit false

universe uK

namespace Langlands.Global

open NumberField Weil.Local Henniart.Numerical GeneralPosition LocalFactor.CommonClosure
open AdelicFunctoriality CompletionPadic

namespace Harris

/-- Every subextension of a local bound has a paired-place configuration over a
specified CM number field at a specified place and with the specified comparison on
elements of the number field. -/
def HasCommonBaseConfigurations {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (B : Extension K) {F : Type} [Field F] [NumberField F] [IsCMField F]
    (v : FinitePlace F) (ι : FiniteCompletion F v ≃+* K.Carrier) : Prop :=
  ∀ B' : Extension K, B'.field ≤ B.field →
    ∃ (D L : Type) (_ : Field D) (_ : Field L) (_ : NumberField D) (_ : NumberField L)
      (_ : IsCMField D) (_ : IsCMField L)
      (_ : Algebra F D) (_ : Algebra F L) (_ : Algebra D L)
      (K₀ : IntermediateField ℚ F) (P Ps : PlaceDatum K B' F D L)
      (φ : FiniteCompletion D P.v' ≃+* B'.field)
      (φs : FiniteCompletion D Ps.v' ≃+* B'.field)
      (θ : (L ≃ₐ[F] L) ≃* ((galoisClosure K B').field ≃ₐ[K.Carrier] (galoisClosure K B').field)),
      IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧ P.v = v ∧
      ∀ x : F, P.iso (algebraMap F (FiniteCompletion F P.v) x) =
        ι (algebraMap F (FiniteCompletion F v) x)

end Harris

/-- The two local fields in a cyclic prime-degree step admit common bases for their
respective finite families of subextensions. The bases form a CM extension with the
same degree as the local step, and the completion isomorphisms at its distinguished
places commute with the local embedding. -/
def HenniartCyclicCommonBaseRealizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
    (B : Extension S.base) (T : Extension S.top),
    letI := S.base.canonicalTopology
    letI := S.top.canonicalTopology
    ∃ (F E : Type) (_ : Field F) (_ : Field E) (_ : NumberField F) (_ : NumberField E)
      (_ : IsCMField F) (_ : IsCMField E) (_ : Algebra F E) (_ : IsGalois F E)
      (v : FinitePlace F) (w : FinitePlacesAbove E v)
      (ι : FiniteCompletion F v ≃+* S.base.Carrier)
      (κ : FiniteCompletion E w.1 ≃+* S.top.Carrier),
      Module.finrank F E = S.degree ∧
      (∀ w' : FinitePlacesAbove E v, w' = w) ∧
      residuePrime v = p ∧ residuePrime w.1 = p ∧
      Continuous ι ∧ Continuous ι.symm ∧ Continuous κ ∧ Continuous κ.symm ∧
      (∀ x : FiniteCompletion F v, κ (FiniteExtension.completionMap v w.1 x) = S.embedding (ι x)) ∧
      Harris.HasCommonBaseConfigurations S.base B v ι ∧
      Harris.HasCommonBaseConfigurations S.top T w.1 κ

end Langlands.Global
