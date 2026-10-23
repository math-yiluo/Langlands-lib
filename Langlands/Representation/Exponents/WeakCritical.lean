import Langlands.Representation.Exponents.ParabolicPair
import Langlands.Representation.Exponents.DualJacquet

/-! Weakly critical dual exponents with every concrete conjugate parabolic
pair included in the proper-refinement quantifier. -/

noncomputable section

namespace Langlands

universe uF uV

namespace Exponents.ConjugateBlockPair

variable {n : ℕ} {F : Type uF} [Field F]

/-- Pull back the representation into the standard coordinates of this pair. -/
def pullbackRep (P : ConjugateBlockPair n F)
    (A : Rep.{uV} ℂ (GeneralLinear n F)) : Rep.{uV} ℂ (GeneralLinear n F) :=
  Rep.of (A.ρ.comp (MulAut.conj P.conjugator).toMonoidHom)

/-- The opposite radical belonging to this concrete conjugate pair. -/
def oppositeUnipotent (P : ConjugateBlockPair n F) : Subgroup (GeneralLinear n F) :=
  (P.shape.oppositeUnipotentSubgroup F).map (MulAut.conj P.conjugator).toMonoidHom

/-- Pullback invariance is precisely invariance under the actual conjugate radical. -/
theorem mem_invariantDual_pullback_iff (P : ConjugateBlockPair n F)
    (A : Rep.{uV} ℂ (GeneralLinear n F)) (f : Module.Dual ℂ A) :
    f ∈ Jacquet.subgroupInvariantDual (P.pullbackRep A).ρ
      (P.shape.oppositeUnipotentSubgroup F) ↔
    f ∈ Jacquet.subgroupInvariantDual A.ρ P.oppositeUnipotent := by
  constructor
  · intro hf x v
    obtain ⟨y, hy, hxy⟩ := x.property
    have he := hf ⟨y, hy⟩ v
    change f (A.ρ ((MulAut.conj P.conjugator) y) v) = f v at he
    change (MulAut.conj P.conjugator) y = x.val at hxy
    rw [hxy] at he
    exact he
  · intro hf y v
    exact hf ⟨(MulAut.conj P.conjugator) y,
      ⟨y, y.property, rfl⟩⟩ v

end Exponents.ConjugateBlockPair

namespace PadicField.TopologicalData

open Exponents

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- The same-order source-functional formula in arbitrary conjugate coordinates.
The coefficient is the inverse upper half-modulus, with no character inversion. -/
theorem mem_conjugateDualJacquet_characterSpace_iff
    (P : ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ) (k : ℕ)
    (φ : Module.Dual ℂ (T.splitCentreOppositeJacquet P.shape (P.pullbackRep A))) :
    φ ∈ commutativeCharacterSpace
      (T.splitCentreDualJacquet P.shape (P.pullbackRep A)).ρ χ k ↔
      ∀ (a : Fin P.shape.length → F.Carrierˣ) (v : A),
        (T.splitCentreDualJacquetSourceEquiv P.shape (P.pullbackRep A) φ).val
          (((A.ρ (P.scalarMap a) -
            ((T.leviHalfModulus P.shape (P.shape.blockScalarLevi F.Carrier a) : ℂ)⁻¹ *
              (χ a : ℂ)) • 1) ^ k) v) = 0 :=
  T.mem_dualJacquet_characterSpace_iff P.shape (P.pullbackRep A) χ k φ

/-- A unitary dual exponent with strictly larger uniform nilpotence order
than every extending unitary dual exponent on every proper smaller pair. -/
def IsWeaklyCriticalDualJacquetExponent
    (P : ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ) : Prop :=
  T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ ∧
    ∀ (Q : ConjugateBlockPair n F.Carrier) (h : Q.StrictlyRefines P)
      (ψ : (Fin Q.shape.length → F.Carrierˣ) →* ℂˣ),
      T.IsUnitaryDualJacquetExponent Q.shape (Q.pullbackRep A) ψ →
      Q.CharacterExtends P h.1.2 ψ χ →
        T.dualJacquetExponentNilpotenceIndex Q.shape (Q.pullbackRep A) ψ <
          T.dualJacquetExponentNilpotenceIndex P.shape (P.pullbackRep A) χ

/-- A pair is weakly critical when at least one of its exponents is. -/
def IsWeaklyCriticalDualJacquetPair
    (P : ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  ∃ χ, T.IsWeaklyCriticalDualJacquetExponent P A χ

/-- Minimality of a pair with a nonempty unitary dual spectrum. -/
def IsWeaklyMinimalDualJacquetPair
    (P : ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  (∃ χ, T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ) ∧
    ∀ Q : ConjugateBlockPair n F.Carrier, Q.StrictlyRefines P →
      ¬ ∃ ψ, T.IsUnitaryDualJacquetExponent Q.shape (Q.pullbackRep A) ψ

/-- The easy direction follows from absence of finer unitary exponents under
minimality; the critical predicate itself remains the strict-order comparison. -/
theorem IsWeaklyMinimalDualJacquetPair.isWeaklyCritical
    {P : ConjugateBlockPair n F.Carrier}
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    (hP : T.IsWeaklyMinimalDualJacquetPair P A)
    {χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ}
    (hχ : T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ) :
    T.IsWeaklyCriticalDualJacquetExponent P A χ :=
  ⟨hχ, fun Q hQ ψ hψ _ => False.elim (hP.2 Q hQ ⟨ψ, hψ⟩)⟩

/-- Every minimal pair is critical, using an exponent from its nonempty spectrum. -/
theorem IsWeaklyMinimalDualJacquetPair.isWeaklyCriticalPair
    {P : ConjugateBlockPair n F.Carrier}
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    (hP : T.IsWeaklyMinimalDualJacquetPair P A) :
    T.IsWeaklyCriticalDualJacquetPair P A := by
  obtain ⟨χ, hχ⟩ := hP.1
  exact ⟨χ, hP.isWeaklyCritical T hχ⟩

end PadicField.TopologicalData
end Langlands
