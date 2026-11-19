import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex

/-! # Isotypy of cuspidal realizations at an infinite place -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global PlaceComponent

attribute [local instance 100] LieRing.ofAssociativeRing

section Transport

open Langlands.Archimedean

variable {K L V V' W W' : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ρ' : Representation ℂ K V'} {π' : L →ₗ⁅ℂ⁆ Module.End ℂ V'}
  {κ : Representation ℂ K W} {δ : L →ₗ⁅ℂ⁆ Module.End ℂ W}
  {κ' : Representation ℂ K W'} {δ' : L →ₗ⁅ℂ⁆ Module.End ℂ W'}

private theorem isotypic_of_surjective (h : IsGKIsotypic ρ' π' κ' δ')
    (a : V →ₗ[ℂ] V') (ha : a ∈ gkHoms ρ π ρ' π') (hsa : Function.Surjective a)
    (b : W' →ₗ[ℂ] W) (hb : b ∈ gkHoms κ' δ' κ δ) (hsb : Function.Surjective b) :
    IsGKIsotypic ρ π κ δ := by
  have hle : gkSpan ρ' π' κ' δ' ≤ (gkSpan ρ π κ δ).comap b := by
    refine iSup₂_le fun f hf => ?_
    rintro _ ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := hsa x'
    have hc : b.comp (f.comp a) ∈ gkHoms ρ π κ δ := by
      refine ⟨fun k y => ?_, fun X y => ?_⟩
      · change b (f (a (ρ k y))) = κ k (b (f (a y)))
        rw [ha.1 k y, hf.1 k (a y), hb.1 k (f (a y))]
      · change b (f (a (π X y))) = δ X (b (f (a y)))
        rw [ha.2 X y, hf.2 X (a y), hb.2 X (f (a y))]
    exact apply_mem_gkSpan hc x
  change gkSpan ρ π κ δ = ⊤
  apply top_unique
  intro w _
  obtain ⟨w', rfl⟩ := hsb w
  apply hle
  rw [show gkSpan ρ' π' κ' δ' = ⊤ from h]
  exact Submodule.mem_top

private theorem isotypic_restrict_of_equiv
    (e : W ≃ₗ[ℂ] W') (heκ : ∀ k w, e (κ k w) = κ' k (e w))
    (heδ : ∀ X w, e (δ X w) = δ' X (e w))
    {S : Submodule ℂ W} (hS : IsIrreducible κ δ S)
    (h : ∀ (S' : Submodule ℂ W') (hS' : IsIrreducible κ' δ' S'),
      IsGKIsotypic (restrictCompact hS'.2.1) (restrictLie hS'.2.1) κ' δ') :
    IsGKIsotypic (restrictCompact hS.2.1) (restrictLie hS.2.1) κ δ := by
  have hS' := isIrreducible_map e.toLinearMap heκ heδ hS
    (fun he => hS.1 (Submodule.map_eq_bot_iff.mp he))
  let a := S.equivMapOfInjective e.toLinearMap e.injective
  refine isotypic_of_surjective (h _ hS') a.toLinearMap ?_ a.surjective
    e.symm.toLinearMap ?_ e.symm.surjective
  · refine ⟨fun k x => Subtype.ext ?_, fun X x => Subtype.ext ?_⟩
    · exact heκ k x
    · exact heδ X x
  · refine ⟨fun k w => e.injective ?_, fun X w => e.injective ?_⟩
    · change e (e.symm (κ' k w)) = e (κ k (e.symm w))
      rw [heκ, e.apply_symm_apply, e.apply_symm_apply]
    · change e (e.symm (δ' X w)) = e (δ X (e.symm w))
      rw [heδ, e.apply_symm_apply, e.apply_symm_apply]

end Transport

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- At a real place the realization is isotypic for any irreducible stable subspace. -/
theorem isRealPlaceIsotypic_restrict
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) {W : Submodule ℂ T.Space}
    (hW : IsIrreducible (T.realization.realPlaceCompactRepresentation v)
      (T.realization.realPlaceLieAction v) W) :
    Archimedean.IsGKIsotypic (restrictCompact hW.2.1) (restrictLie hW.2.1)
      (T.realization.realPlaceCompactRepresentation v) (T.realization.realPlaceLieAction v) := by
  let Q := T.toIrreducibleSubquotient
  exact isotypic_restrict_of_equiv T.toIrreducibleSubquotientEquiv.toLinearEquiv
    (fun k x => (Q.subquotient.realPlaceCompactRepresentation_projection v k x).symm)
    (fun X x => (Q.subquotient.realPlaceLieAction_projection v X x).symm) hW
    (fun _ h => Q.subquotient.isRealPlaceIsotypic_restrict Q.irreducible v h)

/-- At a complex place the realization is isotypic for any irreducible stable subspace. -/
theorem isComplexPlaceIsotypic_restrict
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) {W : Submodule ℂ T.Space}
    (hW : IsIrreducible (T.realization.complexPlaceCompactRepresentation v)
      (T.realization.complexPlaceLieAction v) W) :
    Archimedean.IsGKIsotypic (restrictCompact hW.2.1) (restrictLie hW.2.1)
      (T.realization.complexPlaceCompactRepresentation v)
      (T.realization.complexPlaceLieAction v) := by
  let Q := T.toIrreducibleSubquotient
  exact isotypic_restrict_of_equiv T.toIrreducibleSubquotientEquiv.toLinearEquiv
    (fun k x => (Q.subquotient.complexPlaceCompactRepresentation_projection v k x).symm)
    (fun X x => (Q.subquotient.complexPlaceLieAction_projection v X x).symm) hW
    (fun _ h => Q.subquotient.isComplexPlaceIsotypic_restrict Q.irreducible v h)

end CuspidalOperatorRealization

end Langlands.Automorphic
