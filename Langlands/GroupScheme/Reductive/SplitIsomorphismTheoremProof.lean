import Langlands.GroupScheme.Reductive.SplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof

/-!
# The Isomorphism Theorem for split reductive groups

Every equivalence of root data between split reductive groups over a field comes from an
isomorphism of the groups mapping one split maximal torus onto the other (Milne,
*Algebraic Groups* (2017), Theorem 23.25 and Remark 23.26, existence part). The proof
realizes the weight map by an isomorphism of split tori, transports the root datum of the
second group along it, and applies the Isomorphism Theorem for a common torus.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isomorphism Theorem for split reductive groups** (Milne, Theorem 23.25 and
Remark 23.26, existence part). -/
theorem splitIsomorphismTheorem : SplitIsomorphismTheoremStatement.{u} := by
  intro k _ G G' hG hG' T T' hT hT' i i' hi hi' J J' P P' hP hP' f
  have := hG.isAffineHom
  have := hG'.isAffineHom
  -- The torus isomorphism `s : T' ≅ T` whose character pullback `s.inv ≫ -` is the
  -- weight map of `f`.
  let s : T' ≅ T := hT'.isoOfCharacterEquiv hT f.weightEquiv.toAddEquiv
  have hs : characterLattice.congr s = f.weightEquiv.toAddEquiv :=
    hT'.character_congr_isoOfCharacterEquiv hT _
  -- The inverse equivalence `P ≃ P'` has weight map `χ ↦ s.hom ≫ χ`.
  have he : ∀ χ, (RootPairing.Equiv.symm _ _ f).weightEquiv χ =
      characterLattice.congr s.symm χ := by
    intro χ
    apply f.weightEquiv.injective
    change f.weightEquiv (f.weightEquiv.symm χ) = f.weightEquiv (s.hom ≫ χ)
    rw [LinearEquiv.apply_symm_apply]
    have h := DFunLike.congr_fun hs (s.hom ≫ χ)
    rw [characterLattice.congr_apply, Iso.inv_hom_id_assoc] at h
    exact h
  -- Transport the root datum `P'` of `i'` to a root datum `P` of `s.symm ≫ i'`.
  have hR : IsRootDatumOf (CommGroupScheme.groupHom s.symm.hom ≫ i') P :=
    IsRootDatumOf.precomp_torusIso s.symm hP' hP.1 (RootPairing.Equiv.symm _ _ f) he
  have hM : IsMaximalTorus (CommGroupScheme.groupHom s.symm.hom ≫ i') :=
    IsMaximalTorus.precomp_torusIso s.symm hi'
  -- Isomorphism Theorem for the common torus `T` with the same root datum `P`.
  obtain ⟨φ, hφ⟩ := splitCommonTorusIsomorphism k G G' hG hG' T hT i
    (CommGroupScheme.groupHom s.symm.hom ≫ i') hi hM J J P P hP hR (Equiv.refl J) rfl rfl
  refine ⟨φ, s.symm, hφ, fun χ => ?_⟩
  exact (DFunLike.congr_fun hs χ).symm

end Langlands.GroupScheme
