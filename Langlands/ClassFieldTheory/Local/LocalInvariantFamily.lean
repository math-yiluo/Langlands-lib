import Langlands.ClassFieldTheory.Local.AbsoluteInvariantAssembly
import Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationProof
import Langlands.ClassFieldTheory.Local.RelativeH2Transport

/-! # The local invariant family

The absolute invariant of a `p`-adic field is the map descended from the
unramified finite stages. A finite Galois extension `L/F` is placed in the
algebraic closure by one chosen embedding; its relative invariant is the
absolute invariant of the closure inflation of the transported class.
The unramified `H²` exhaustion statement is a parameter of the family.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

section Embedded

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

instance embeddedImage_finiteDimensional (f : L →ₐ[K] AlgebraicClosure K) :
    FiniteDimensional K f.fieldRange :=
  f.equivFieldRange.toLinearEquiv.finiteDimensional

instance embeddedImage_isGalois (f : L →ₐ[K] AlgebraicClosure K) :
    IsGalois K f.fieldRange :=
  IsGalois.of_algEquiv f.equivFieldRange

/-- Relative invariant through a supplied `K`-embedding into the algebraic closure:
transport to the image field, inflate to absolute `H²`, then apply `inv`. -/
def embeddedRelativeInvariant (inv : absoluteCohomology K 2 →+ RationalModIntegers)
    (f : L →ₐ[K] AlgebraicClosure K) :
    relativeCohomology K L 2 →+ RationalModIntegers :=
  (inv.comp (closureInflation K f.fieldRange 2)).comp
    (relativeH2Equiv f.equivFieldRange).toAddMonoidHom

@[simp]
theorem embeddedRelativeInvariant_apply
    (inv : absoluteCohomology K 2 →+ RationalModIntegers)
    (f : L →ₐ[K] AlgebraicClosure K) (x : relativeCohomology K L 2) :
    embeddedRelativeInvariant K L inv f x =
      inv (closureInflation K f.fieldRange 2 (relativeH2Equiv f.equivFieldRange x)) :=
  rfl

/-- The embedding chosen by `IsAlgClosed.lift`. -/
def closureEmbedding : L →ₐ[K] AlgebraicClosure K :=
  IsAlgClosed.lift

end Embedded

open AbsoluteInvariantAssembly

/-- The absolute invariant descended from unramified finite stages, using the
proved tower and unramified-inflation compatibilities. -/
def localAbsoluteInvariant (hEx : UnramifiedH2Exhaustion.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    absoluteCohomology F.Carrier 2 →+ RationalModIntegers :=
  descendedHom F hEx closureInflationTowerCompatibility
    unramifiedInvariantInflationCompatibility

/-- The local invariant family: descended absolute invariants, and relative
invariants through the chosen closure embedding. -/
def localInvariantFamily (hEx : UnramifiedH2Exhaustion.{u})
    (p : ℕ) [Fact p.Prime] : InvariantFamily.{u,u} p where
  absolute F := localAbsoluteInvariant hEx F
  relative F L := embeddedRelativeInvariant F.Carrier L
    (localAbsoluteInvariant hEx F) (closureEmbedding F.Carrier L)

@[simp]
theorem localInvariantFamily_absolute (hEx : UnramifiedH2Exhaustion.{u})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) :
    (localInvariantFamily hEx p).absolute F = localAbsoluteInvariant hEx F :=
  rfl

@[simp]
theorem localInvariantFamily_relative (hEx : UnramifiedH2Exhaustion.{u})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] :
    (localInvariantFamily hEx p).relative F L =
      embeddedRelativeInvariant F.Carrier L (localAbsoluteInvariant hEx F)
        (closureEmbedding F.Carrier L) :=
  rfl

end Langlands.ClassFieldTheory.Local
