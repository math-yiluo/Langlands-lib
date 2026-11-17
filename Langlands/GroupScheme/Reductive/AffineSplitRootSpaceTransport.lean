import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Torus.ExponentCharacters

/-! # Exponent weight spaces under a change of coordinate torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I]
  [DecidableEq I'] {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]

/-- **Weight spaces of the precomposed torus.** For a lattice isomorphism
`e : (I → ℤ) ≃ (I' → ℤ)`, the exponent-`m` weight space of the torus map
`precompTorus e i' : T_I ≅ T_{I'} ⟶ H` is the exponent-`e m` weight space of `i'`. -/
theorem exponentWeightSpace_precompTorus (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) (m : I → ℤ) :
    splitTorus.exponentWeightSpace I H (precompTorus e i') m =
      splitTorus.exponentWeightSpace I' H i' (e m) := by
  rw [splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter,
    splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
  let φ := splitTorus.exponentEquivIso (Spec (CommRingCat.of R)) e
  have hχ : φ.hom ≫ splitTorus.exponentCharacter _ I' (e m) =
      splitTorus.exponentCharacter _ I m := by
    change splitTorus.exponentHom _ I I' e.symm.toLinearMap ≫ _ = _
    rw [splitTorus.exponentHom_comp_exponentCharacter]
    simp
  have hc : CommGroupScheme.groupHom φ.inv ≫ precompTorus e i' = i' := by
    change CommGroupScheme.groupHom φ.inv ≫ CommGroupScheme.groupHom φ.hom ≫ i' = i'
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ i' = i'
    rw [Iso.inv_hom_id]
    exact Category.id_comp _
  have hχ' : φ.inv ≫ splitTorus.exponentCharacter _ I m =
      splitTorus.exponentCharacter _ I' (e m) := by
    rw [← hχ, Iso.inv_hom_id_assoc]
  ext X
  constructor
  · intro hX
    have h : X ∈ weightSpace (CommGroupScheme.groupHom φ.inv ≫ precompTorus e i')
        (φ.inv ≫ splitTorus.exponentCharacter _ I m) := by
      intro A _ _ t
      have h1 := hX A (t ≫ (CommGroupScheme.groupHom φ.inv).hom.hom)
      rw [Lie.characterValue_comp, Grp.comp_hom_hom]
      rw [Category.assoc] at h1
      exact h1
    rwa [hc, hχ'] at h
  · intro hX
    have h : X ∈ weightSpace (CommGroupScheme.groupHom φ.hom ≫ i')
        (φ.hom ≫ splitTorus.exponentCharacter _ I' (e m)) := by
      intro A _ _ t
      have h1 := hX A (t ≫ (CommGroupScheme.groupHom φ.hom).hom.hom)
      rw [Lie.characterValue_comp, Grp.comp_hom_hom]
      rw [Category.assoc] at h1
      exact h1
    rwa [hχ] at h

/-- **Free root spaces for the precomposed torus.** If `e : P ≃ Q` is an equivalence of root
data and every root space of `i'` for `Q` is free of rank one, then every root space of
`precompTorus e.weightEquiv i'` for `P` is free of rank one: the root space of `P.root α`
is the root space of `Q.root (e.indexEquiv α)`. -/
theorem nonempty_exponentWeightSpace_precompTorus {J J' : Type u}
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (e : RootPairing.Equiv P Q) (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hfree : ∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R))
    (α : J) :
    Nonempty (splitTorus.exponentWeightSpace I H (precompTorus e.weightEquiv i') (P.root α)
      ≃ₗ[CommRingCat.of R] CommRingCat.of R) := by
  obtain ⟨f⟩ := hfree (e.indexEquiv α)
  have hroot : e.weightEquiv (P.root α) = Q.root (e.indexEquiv α) := by
    rw [RootPairing.Equiv.weightEquiv_apply]
    exact RootPairing.Hom.root_weightMap_apply _ _ α e.toHom
  refine ⟨(LinearEquiv.ofEq _ _ ?_).trans f⟩
  rw [exponentWeightSpace_precompTorus, hroot]

end Langlands.GroupScheme.LocalSplitCell

/-! ### The statement -/

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Free root spaces under a change of coordinate torus.** Let `H` be a group scheme with
affine structure map over `Spec R` (`R` any commutative ring), `i' : 𝔾_m^{I'} → H` a torus
map and `e : P ≃ Q` an equivalence of root data on the coordinate lattices. If every root space
of `i'` for `Q` is free of rank one over `R`, then every root space of the precomposed torus
`precompTorus e.weightEquiv i' : 𝔾_m^I ≅ 𝔾_m^{I'} → H` for `P` is free of rank one. -/
def AffineSplitRootSpaceTransportStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I I' : Type u) [Fintype I] [Fintype I'] [DecidableEq I]
    [DecidableEq I'] (H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom H.X.hom]
    (J J' : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (e : RootPairing.Equiv P Q) (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    (∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R)) →
    ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I H (precompTorus e.weightEquiv i') (P.root α)
        ≃ₗ[CommRingCat.of R] CommRingCat.of R)

/-- Proof of `AffineSplitRootSpaceTransportStatement`, by
`LocalSplitCell.nonempty_exponentWeightSpace_precompTorus`. -/
theorem affineSplitRootSpaceTransport : AffineSplitRootSpaceTransportStatement.{u} := by
  intro R _ I I' _ _ _ _ H _ J J' P Q e i' hfree α
  exact nonempty_exponentWeightSpace_precompTorus e i' hfree α

end Langlands.GroupScheme
