import Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement
import Langlands.AlgebraicGeometry.UniqueRationalFiberFiniteNeighborhoodProof
import Langlands.AlgebraicGeometry.TangentKernelCotangentSurjectivityProof
import Langlands.AlgebraicGeometry.FiniteSingletonFiberStalk
import Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityProof
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The local closed-immersion criterion from its four steps

Write `z = x(closedPoint)`. The unique-rational-fibre step gives `f ⁻¹' {f z} = {z}` and an
open `V₀ ∋ f z` over which `f` is finite. The restriction `f ∣_ V₀` is finite and its fibre
through `z` is still a singleton, so the finite-singleton-fibre step makes its stalk map at `z`
finite. Through `morphismRestrictStalkMap` this is finiteness of the stalk map of `f` at `z`.
The tangent step makes the cotangent map of that stalk map surjective; the stalk of `X` is
Noetherian because `X` is locally of finite type over a field. The commutative-algebra step
then makes the stalk map surjective. Transported back to `f ∣_ V₀`, the second half of the
finite-singleton-fibre step gives an open `V' ⊆ V₀` around `f z` over which `f ∣_ V₀` is a
closed immersion, and `morphismRestrictRestrict` identifies `f ∣_ V₀ ∣_ V'` with
`f ∣_ V₀.ι ''ᵁ V'`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The local closed-immersion criterion follows from the unique-rational-fibre,
tangent-to-cotangent, finite-local-cotangent and finite-singleton-fibre statements. -/
theorem properRationalImmersion_localClosedImmersion_of
    (h₁ : UniqueRationalFiberFiniteNeighborhoodStatement.{u})
    (h₂ : TangentKernelCotangentSurjectivityStatement.{u})
    (h₃ : Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityStatement.{u, u, u})
    (h₄ : FiniteSingletonFiberLocalClosedImmersionStatement.{u}) :
    ProperRationalImmersionLocalClosedImmersionStatement.{u} := by
  intro K _ _ X Y p q _ _ f _ hfq x hx hP hT
  obtain ⟨hF, V₀, hzV₀, hfin⟩ := h₁ K X Y p q f hfq x hx hP
  -- The point `z` of `X`, seen in the preimage of `V₀`.
  let z' : (f ⁻¹ᵁ V₀).toScheme := ⟨x (IsLocalRing.closedPoint K), hzV₀⟩
  have hF' : (f ∣_ V₀) ⁻¹' {(f ∣_ V₀) z'} = {z'} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hw
      have hw' : f w.1 = f (x (IsLocalRing.closedPoint K)) := by
        have := congrArg Subtype.val hw
        rwa [morphismRestrict_base_coe, morphismRestrict_base_coe] at this
      have hmem : w.1 ∈ f ⁻¹' {f (x (IsLocalRing.closedPoint K))} := hw'
      rw [hF] at hmem
      exact Subtype.ext hmem
    · rintro rfl
      rfl
  obtain ⟨hfinite, hspread⟩ := h₄ _ _ (f ∣_ V₀) z' hF'
  -- Finiteness of the actual stalk map of `f` at `z`.
  have hfinite' : (f.stalkMap (x (IsLocalRing.closedPoint K))).hom.Finite :=
    (RingHom.finite_respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap f V₀ z')).mp hfinite
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let := Picard.stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := Picard.stalkAlgebraOver q (f (x (IsLocalRing.closedPoint K)))
  have hsurjAlg := h₃ K _ _ (Picard.rationalStalkAugmentation p x hx)
    (Picard.stalkMapAlgHomOver p q f hfq (x (IsLocalRing.closedPoint K)))
    (by
      rw [Picard.stalkMapAlgHomOver_toRingHom]
      exact hfinite')
    (h₂ K X Y p q f hfq x hx hT)
  have hsurj : Function.Surjective (f.stalkMap (x (IsLocalRing.closedPoint K))).hom := by
    rw [← Picard.stalkMapAlgHomOver_toRingHom p q f hfq]
    exact hsurjAlg
  have hsurj' : Function.Surjective ((f ∣_ V₀).stalkMap z').hom :=
    (RingHom.surjective_respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap f V₀ z')).mpr hsurj
  obtain ⟨V', hV', hci⟩ := hspread hsurj'
  refine ⟨V₀.ι ''ᵁ V', ⟨(f ∣_ V₀) z', hV', ?_⟩, ?_⟩
  · exact morphismRestrict_base_coe f V₀ z'
  · exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (morphismRestrictRestrict f V₀ V')).mp hci

/-- A proper morphism with a unique rational fibre and trivial rational tangent kernel at a
rational point is a closed immersion over an open neighbourhood of its image. -/
theorem properRationalImmersion_localClosedImmersion :
    ProperRationalImmersionLocalClosedImmersionStatement.{u} :=
  properRationalImmersion_localClosedImmersion_of
    uniqueRationalFiber_finiteNeighborhood.{u}
    tangentKernel_cotangentSurjectivity.{u}
    Langlands.CommutativeAlgebra.finiteLocalCotangentSurjectivity.{u, u, u}
    finiteSingletonFiber_localClosedImmersion.{u}

end Langlands.AlgebraicGeometry
