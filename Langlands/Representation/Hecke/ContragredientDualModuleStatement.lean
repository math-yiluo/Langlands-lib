import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Representation.Hecke.HaarInversion
import Langlands.Algebra.NonUnitalModuleDualFunctor
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-!
# The contragredient as the dual Hecke module (Renard III.1.6)

Under the equivalence of III.1.4, the smooth contragredient of a smooth representation is
the nondegenerate dual module of I.4.1 of its Hecke module, right and left modules being
identified through the anti-involution `T ↦ Ť` of the Hecke algebra.
-/

namespace Langlands.Hecke

open MeasureTheory

universe u v

/-- Renard III.1.6, the paragraph before the Lemma: for a t.d. group `G` with a left Haar
measure `μ` and a smooth representation `A`, there is an additive equivalence `e` from the
smooth dual `Ṽ` onto the I.4.1 dual `Ṽ` of the Hecke module of `A`, given by
`e(ℓ)(v) = ℓ(v)`, which carries `π̃(T)` to the right action of `Ť`:
`e(π̃(T) ℓ) = e(ℓ) · Ť`, where `Ť` is the weighted inversion `haarInversion μ T`. -/
def ContragredientHeckeDualStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (A : SmoothRep.{0, u, v} ℂ G),
    let D := Algebra.NonUnitalModuleDual.dualObject (Homomorphism.isIdempotented μ)
      (heckeNondegenerateModule μ A)
    ∃ e : SmoothDual A.representation ≃+ D.obj,
      (∀ (ℓ : SmoothDual A.representation) (v : A),
        (e ℓ).val v = smoothDualPairing A.representation ℓ v) ∧
      ∀ (T : HeckeAlgebra μ) (ℓ : SmoothDual A.representation),
        e (heckeAction μ (smoothContragredient A.representation)
            (isSmooth_smoothContragredient A.representation) T ℓ) =
          MulOpposite.op (haarInversion μ T) • e ℓ

end Langlands.Hecke
