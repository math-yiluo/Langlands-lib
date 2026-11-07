import Langlands.GroupScheme.Rational.SteinbergCyclicGauge
import Langlands.GroupScheme.Rational.SteinbergFieldBaseChange
import Langlands.GroupScheme.Rational.SteinbergCanonicalRepresentatives
import Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof

/-! # Arbitrary-field comparison with canonical Steinberg representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (n m : p.SimpleReflectionRepresentatives)

/-- The quotient-isomorphism property is independent of the supplied reflection
representatives over every field for a semisimple group. -/
theorem isIso_quotient_iff_representatives_of_semisimple (hG : IsSemisimple G)
    (x : p.NormalizedSimpleRootParametrizations) :
    IsIso (steinbergProduct e x m ≫ ClassFunctions.rho G) ↔
      IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  let K := AlgebraicClosure k
  let GK := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have hGK : IsSemisimple GK := isSemisimpleFieldExtension k K G hG
  have hcompare :=
    isIso_quotient_iff_representatives
      (fieldBaseChangeOrder (F := K) e)
      (fieldBaseChangeRepresentatives (F := K) n)
      (fieldBaseChangeRepresentatives (F := K) m)
      hGK (fieldBaseChangeRootMaps (F := K) x)
  exact (isIso_steinbergQuotient_baseChange_iff (F := K) e x m).symm.trans
    (hcompare.trans (isIso_steinbergQuotient_baseChange_iff (F := K) e x n))

/-- Over every field, the exact supplied product has the quotient-isomorphism
property exactly when the canonical root-generated family does. -/
theorem isIso_quotient_iff_canonicalRepresentatives (hG : IsSemisimple G)
    (x : p.NormalizedSimpleRootParametrizations) :
    IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) ↔
      IsIso (steinbergProduct e x (canonicalSimpleReflectionRepresentatives x) ≫
        ClassFunctions.rho G) :=
  isIso_quotient_iff_representatives_of_semisimple e
    (canonicalSimpleReflectionRepresentatives x) n hG x

end SplitPinning

/-- The canonical quotient isomorphism for the root-generated representatives
determined by each supplied normalized root family, over arbitrary fields. -/
def SplitSteinbergCanonicalQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (x : p.NormalizedSimpleRootParametrizations),
      IsIso (SplitPinning.steinbergProduct e x
        (SplitPinning.canonicalSimpleReflectionRepresentatives x) ≫ ClassFunctions.rho G)

/-- The exact arbitrary-field target is equivalent to its canonical-representative
case, with no simple-connectedness ascent premise. -/
theorem splitSteinbergQuotient_iff_canonical :
    SplitSteinbergQuotientStatement.{u} ↔
      SplitSteinbergCanonicalQuotientStatement.{u} := by
  constructor
  · intro h k _ G _ p hG r e x
    exact h k G p hG r e x (SplitPinning.canonicalSimpleReflectionRepresentatives x)
  · intro h k _ G _ p hG r e x n
    exact (SplitPinning.isIso_quotient_iff_canonicalRepresentatives e n
      hG.isSemisimple x).mpr (h k G p hG r e x)

end Langlands.GroupScheme
