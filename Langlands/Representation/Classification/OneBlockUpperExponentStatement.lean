import Langlands.Representation.Classification.TemperedExponentStatement
import Langlands.Representation.Classification.ProductLeviChamberBoundProof
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly

/-!
# Upper exponent bounds of `GL_n` on the single-block product Levi

The ordinary upper exponent bounds of a representation of `GL_n(F)` give the
refined upper exponent hypothesis of the same representation viewed on the
single-block product Levi.
-/

namespace Langlands

universe uF uV

/-- If every exponent of every upper normalized Jacquet module of an admissible
representation `π` of `GL_n(F)` has norm at most one on tuples with monotone
normalized absolute values, then `π`, viewed on the single-block product Levi
through `ScalarLayer.oneBlockLeviEquiv`, satisfies
`ProductLeviChamber.UpperExponentHypothesis`. -/
def GLOneBlockUpperExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (hn : 0 < n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V),
    (letI := T.topology
     IsAdmissible π) →
    (∀ (B : GeneralLinear.BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
      T.IsJacquetExponent B π χ →
      ∀ a : Fin B.length → F.Carrierˣ,
        Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
        ‖(χ a : ℂ)‖ ≤ 1) →
    letI := T.topology
    ProductLeviChamber.UpperExponentHypothesis T
      (CuspidalSupport.LeviAdmissibility.oneBlock n hn)
      (π.comp (ScalarLayer.oneBlockLeviEquiv T hn).toMonoidHom)

end Langlands
