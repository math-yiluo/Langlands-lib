import Langlands.Global.Factors.RelativePolePairingStatement

/-!
# Certified local pole comparisons for witnessed relative pairs

Henniart (2000), Corollary 2.4 and Lemma 2.8, in the finite-relative witnessed
setting of `RelativeCertifiedPoleComparisons`: at every finite place, for
every arithmetic fundamental class family and every nontrivial additive
character, the certified pair-factor data exist and satisfy the regular
completed-germ comparison and both pole formulas at `s = 0`.
-/

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

/-- For all number fields `E/F` Galois, every arithmetic fundamental class
family, every finite place `v` of `F` and every nontrivial additive character
of `F_v`, the witnessed relative pairs at `v` admit certified pole
comparisons: a self-dual measure exists, and for every self-dual measure there
are actual dual classes, certified automorphic pair L-polynomials and
regular omitted/boundary data whose completed germs agree at `0`, while the
arithmetic and automorphic pair factors have order at `0` equal to minus the
respective unitary-lattice pairings. -/
def RelativeCertifiedPoleComparisonsStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ

end Langlands.Global.PoleComparison
