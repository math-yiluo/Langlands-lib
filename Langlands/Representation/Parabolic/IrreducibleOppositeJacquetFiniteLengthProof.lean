import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthStatement
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof

/-!
# Finite length of actual opposite Jacquet modules

The published block-reversal equivalence transfers upper normalized Jacquet
finite length to the actual opposite action. Irreducibility supplies ambient
finite generation through the cyclicity of a simple group-algebra module.
-/

noncomputable section

namespace Langlands.Parabolic

open scoped MonoidAlgebra

universe uF uV uG uK

namespace IrreducibleOppositeJacquetFiniteLength

/-- An irreducible representation is cyclic over its group algebra. -/
theorem finite_asModule_of_irreducible
    {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {V : Type uV} [AddCommGroup V] [Module k V]
    (π : Representation k G V) (hπ : Representation.IsIrreducible π) :
    Module.Finite k[G] π.asModule := by
  let : IsSimpleModule k[G] π.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule π).mp hπ
  let : Nontrivial π.asModule := IsSimpleModule.nontrivial k[G] π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : π.asModule)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] π.asModule v)
    (IsSimpleModule.toSpanSingleton_surjective k[G] hv)

end IrreducibleOppositeJacquetFiniteLength

/-- The actual opposite normalized Jacquet representation of admissible,
finitely generated ambient GL input has finite length, in every rank. -/
theorem oppositeJacquetFiniteLength
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (π : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible π →
      Module.Finite ℂ[GeneralLinear n F.Carrier] π.asModule →
      IsFiniteLength ℂ[B.Levi F.Carrier]
        (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ.asModule := by
  let := T.topology
  intro π hπ hfg
  let θ := OppositeCuspidalJacquetFiltration.leviReverseEquiv (R := F.Carrier) B
  let E := OppositeCuspidalJacquetFiltration.oppositeJacquetReverseEquiv T B (Rep.of π)
  have hupper := normalizedJacquetFiniteLength T B.reverse π hπ hfg
  have hpullback :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff
      (T.normalizedJacquet B.reverse π) θ.toMonoidHom θ.surjective).mp hupper
  exact FiniteLengthAssembly.finiteLength_of_surjective E.toIntertwiningMap
    E.toLinearEquiv.surjective hpullback

/-- The exact Library proposition for irreducible admissible ambient input. -/
theorem irreducibleOppositeJacquetFiniteLength :
    IrreducibleOppositeJacquetFiniteLengthStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ B V _ _ π hirr hadm
  exact oppositeJacquetFiniteLength T B π hadm
    (IrreducibleOppositeJacquetFiniteLength.finite_asModule_of_irreducible π hirr)

end Langlands.Parabolic
