import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement
import Langlands.ClassFieldTheory.Local.ClosureInflationIndependenceProof
import Langlands.ClassFieldTheory.Local.AbsoluteH1Proof
import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof

/-! # Continuous properties of the local invariant family

Hilbert 90 is the proved continuous statement. Bijectivity and the degree
law are the proved properties of the descended absolute invariant. Closure
compatibility holds because the relative invariant may be computed through
any identification of `L` with a normal subfield of the algebraic closure.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open AbsoluteInvariantAssembly

/-- The relative invariant of the local invariant family may be computed
through any `K`-isomorphism of `L` onto a normal finite subfield of the
algebraic closure, not only through the chosen embedding. -/
theorem localInvariantFamily_relative_eq (hEx : UnramifiedH2Exhaustion.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (L : Type u)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L]
    (E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    [FiniteDimensional F.Carrier E] [Normal F.Carrier E]
    (e : L ≃ₐ[F.Carrier] E) (x : relativeCohomology F.Carrier L 2) :
    (localInvariantFamily hEx p).relative F L x =
      localAbsoluteInvariant hEx F
        (closureInflation F.Carrier E 2 (relativeH2Equiv e x)) := by
  rw [localInvariantFamily_relative, embeddedRelativeInvariant_apply,
    closureInflationTransportIndependence F.Carrier L _ E
      (closureEmbedding F.Carrier L).equivFieldRange e x]

/-- The local invariant family has the continuous absolute invariant properties. -/
theorem localInvariantFamilyContinuous : LocalInvariantFamilyContinuousStatement.{u} := by
  intro hEx p _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F
    let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
    exact absoluteH1Vanishing F.Carrier
  · intro F
    exact ⟨descendedHom_injective F hEx closureInflationTowerCompatibility
        unramifiedInvariantInflationCompatibility,
      descendedHom_surjective F hEx closureInflationTowerCompatibility
        unramifiedInvariantInflationCompatibility⟩
  · intro F E _ _ _ _ _ x
    exact descendedHom_restriction F hEx closureInflationTowerCompatibility
      unramifiedInvariantInflationCompatibility unramifiedBaseChangeStageExistence
      closureInflationBaseChangeCompatibility unramifiedInvariantBaseChangeCompatibility E x
  · intro F E _ _ x
    rw [localInvariantFamily_relative_eq hEx F E E AlgEquiv.refl x, relativeH2Equiv_refl]
    rfl

end Langlands.ClassFieldTheory.Local
