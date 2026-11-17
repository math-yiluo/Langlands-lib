import Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof

/-! # The norm quotient of a finite abelian extension given as a separate field

For a finite abelian extension `D` of a p-adic field `F`, given as a separate
field in the universe of `F`, a continuous geometric finite Artin symbol induces
a topological group isomorphism from the actual norm quotient of `F.Carrierˣ`
onto `Gal(D/F.Carrier)`, sending the class of `a` to `geometricSymbol F D a`.
-/

namespace Langlands.LocalClassField.FiniteArtinSystemExistence

open Langlands.ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (D : Type u) [Field D]
  [Algebra F.Carrier D] [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D]

/-- For any topology on `F.Carrier` for which the geometric symbol is continuous,
the geometric symbol descends to a topological group isomorphism from the norm
quotient onto the finite discrete Galois group, with value the geometric symbol
on every class. -/
theorem exists_quotientEquiv_geometricSymbol [TopologicalSpace F.Carrier]
    (hc : Continuous (geometricSymbol F D)) :
    ∃ r : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := D))).range) ≃ₜ*
        Gal(D/F.Carrier),
      ∀ a : F.Carrierˣ, r (QuotientGroup.mk a) = geometricSymbol F D a := by
  let e : (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := D))).range) ≃*
      Gal(D/F.Carrier) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_geometricSymbol F D).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (geometricSymbol F D)
        (geometricSymbol_surjective F D))
  have he : ∀ a : F.Carrierˣ, e (QuotientGroup.mk a) = geometricSymbol F D a := fun _ => rfl
  refine ⟨{ e with
    continuous_toFun := ?_
    continuous_invFun := continuous_of_discreteTopology }, he⟩
  refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
  change Continuous (fun a : F.Carrierˣ => e (QuotientGroup.mk a))
  simp only [he]
  exact hc

end Langlands.LocalClassField.FiniteArtinSystemExistence
