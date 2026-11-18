import Langlands.GroupScheme.Torus.MultiplicativeTypeInfinitesimalCentralityStatement
import Langlands.GroupScheme.Torus.NilpotentConjugationAction

/-! # Proof: centrality of homomorphisms from groups of multiplicative type spreads from
nilpotent thickenings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.MultiplicativeTypeInfinitesimalCentrality

open MultiplicativeTypeAffineInfinitesimalCentrality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On an affine open `U`, the quotient of `Γ(S, U)` by the ideal of `i` maps to `S₀`
compatibly with `i`. -/
theorem exists_quotient_lift {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    (U : S.affineOpens) :
    ∃ e : Spec (CommRingCat.of (Γ(S, U) ⧸ i.ker.ideal U)) ⟶ S₀,
      Spec.algebraMap Γ(S, U) (Γ(S, U) ⧸ i.ker.ideal U) ≫ U.2.fromSpec = e ≫ i := by
  have hV : IsAffineOpen (i ⁻¹ᵁ (U : S.Opens)) := U.2.preimage i
  have hsurj := i.app_surjective U U.2
  have hker : i.ker.ideal U = RingHom.ker (i.app U).hom := Scheme.Hom.ker_apply i U
  let ψ : (Γ(S, U) ⧸ i.ker.ideal U) ≃+* Γ(S₀, i ⁻¹ᵁ U) :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hring : CommRingCat.ofHom (algebraMap Γ(S, U) (Γ(S, U) ⧸ i.ker.ideal U)) =
      i.appLE U (i ⁻¹ᵁ U) le_rfl ≫ CommRingCat.ofHom ψ.symm.toRingHom := by
    ext x
    change Ideal.Quotient.mk _ x = ψ.symm (i.appLE U (i ⁻¹ᵁ U) le_rfl x)
    rw [RingEquiv.eq_symm_apply, ← Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec i U.2 hV le_rfl,
    ← Spec.map_comp_assoc, ← hring]

/-- Globalization: centrality lifts across a closed immersion with locally nilpotent ideal. -/
theorem isCentral_of_locallyNilpotent
    {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : ∀ x : S, ∃ U : S.affineOpens, x ∈ (U : S.Opens) ∧ IsNilpotent (i.ker.ideal U))
    {G H : GroupScheme S} (hG : RelativeMultiplicativeType.IsMultiplicativeType G)
    (u : G ⟶ H) (hc : IsCentral ((GroupScheme.baseChange i).map u)) : IsCentral u := by
  choose U hxU hUnil using hi
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Flat) S :=
    Scheme.Cover.mkOfCovers S (fun x => Spec Γ(S, U x)) (fun x => (U x).2.fromSpec)
      (fun x => by
        have : x ∈ Set.range (U x).2.fromSpec := by
          rw [(U x).2.range_fromSpec]; exact hxU x
        obtain ⟨y, hy⟩ := this
        exact ⟨x, y, hy⟩)
      (fun x => inferInstance)
  apply IsCentral.of_flatCover 𝒰
  intro x
  obtain ⟨e, he⟩ := exists_quotient_lift i (U x)
  exact NilpotentConjugation.isCentral_of_isMultiplicativeType (hG.baseChange _) _
    (i.ker.ideal (U x)) (hUnil x)
    (isCentral_baseChange_of_commSq _ _ i e he u hc)

end MultiplicativeTypeInfinitesimalCentrality

/-- **Centrality spreads from a nilpotent thickening** (SGA 3, IX, Corollaire 3.9). -/
theorem multiplicativeTypeInfinitesimalCentrality :
    MultiplicativeTypeInfinitesimalCentralityStatement.{u} := by
  intro S S₀ i _ hi G H _ hG u hc
  exact MultiplicativeTypeInfinitesimalCentrality.isCentral_of_locallyNilpotent i hi hG u hc

end Langlands.GroupScheme
