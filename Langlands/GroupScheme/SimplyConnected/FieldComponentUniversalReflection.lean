import Langlands.GroupScheme.SimplyConnected.TensorUniversalReflectionStatement
import Langlands.GroupScheme.Descent.FieldComponentFactorizations
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.Descent.TensorComponents
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Mathlib.RingTheory.Finiteness.Descent

/-! # Reflection of central-cover factorization through field components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {C G : GroupScheme (Spec (CommRingCat.of k))} {π : C ⟶ G}

/-- Reflect the explicit cover universal property using a finite field decomposition
of the actual double overlap with isomorphic structural maps. -/
theorem HasCentralCoverUniversalProperty.of_fieldComponents
    [Algebra.IsAlgebraic k K]
    (hπ : HasCentralCoverUniversalProperty ((baseChange (fieldMap k K)).map π))
    {I : Type} [Finite I] {L : I → Type u} [∀ i, Field (L i)]
    (r : ∀ i, Spec (CommRingCat.of (L i)) ⟶ Overlap (fieldMap k K))
    [IsIso (Limits.Sigma.desc r)]
    [∀ i, IsIso (r i ≫ fst (fieldMap k K))]
    [∀ i, IsIso (r i ≫ snd (fieldMap k K))] :
    HasCentralCoverUniversalProperty π := by
  let p := fieldMap k K
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective p := hsurj
  let : Flat p := hflat
  let : QuasiCompact p := hqc
  intro H q hH hq
  obtain ⟨a, ha, hu⟩ := hπ _ ((baseChange p).map q)
    hH.baseChange_of_algebraicExtension (hq.baseChange p)
  have hcompat : Compatible (canonicalDatum p C) (canonicalDatum p H) a :=
    (canonicalDatum_compatible p π).of_factorization_onFieldComponents
      (canonicalDatum_compatible p q) hπ hH.baseChange_of_algebraicExtension
      (hq.baseChange p) ha r
  let a₀ := Descent.FpqcHomDescent.hom p a hcompat
  have ha₀ : (baseChange p).map a₀ = a :=
    Descent.FpqcHomDescent.baseChange_hom p a hcompat
  refine ⟨a₀, ?_, ?_⟩
  · apply (baseChange p).map_injective
    rw [Functor.map_comp, ha₀, ha]
  · intro b hb
    apply (baseChange p).map_injective
    rw [ha₀]
    apply hu
    rw [← Functor.map_comp, hb]

/-- A supplied finite tensor decomposition provides the field components for
reflection of the explicit central-cover universal property. -/
theorem HasCentralCoverUniversalProperty.of_tensorDecomposition
    (hπ : HasCentralCoverUniversalProperty ((baseChange (fieldMap k K)).map π))
    {I : Type} [Finite I]
    (e : (K ⊗[k] K) ≃ₐ[K] (I → K)) (s : I → K ≃ₐ[k] K)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b) :
    HasCentralCoverUniversalProperty π := by
  let : Module.Finite K (K ⊗[k] K) := by
    rw [Module.Finite.equiv_iff e.toLinearEquiv]
    infer_instance
  let : Module.Finite k K := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K
  let (i : I) : IsIso (tensorComponent e i ≫ snd (fieldMap k K)) :=
    tensorComponent_snd_isIso e s he i
  exact hπ.of_fieldComponents (tensorComponent e)

/-- The exact published tensor-decomposition reflection statement. -/
theorem centralCoverUniversalPropertyTensorReflection :
    CentralCoverUniversalPropertyTensorReflectionStatement.{u} := by
  intro k K _ _ _ C G π I _ e s he hπ
  exact hπ.of_tensorDecomposition e s he

end Langlands.GroupScheme
