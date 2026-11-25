/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralSliceModelComparison
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousIntegralCoefficientComparison

/-!
# Continuous and completed integral constructibility

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(blueprint: lem-weil-pbc-continuous-integral-constructible-comparison)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem fp_iso (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : pbcModules T (pbcAdicCompletion T d)} (e : M ≅ N)
    (hM : IsIntegralStratifiedFinitelyPresented T d M) :
    IsIntegralStratifiedFinitelyPresented T d N := by
  obtain ⟨s, hs⟩ := hM
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hv⟩ := hs i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := hv U f hf
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (s.immersion i) _).mapIso e.symm) ≪≫ eL⟩⟩
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

universe u₁ v₁ w₁ a₁

private theorem localModels_cover_iff_sieve
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasTerminal C] (R : Sheaf J RingCat.{w₁}) {A : Type a₁}
    (P : A → Prop) (G : A → SheafOfModules.{w₁} R) (M : SheafOfModules.{w₁} R) :
    (∃ (I : Type (max u₁ v₁)) (V : I → C), J.CoversTop V ∧
      ∀ i, ∃ a, P a ∧ Nonempty (M.over (V i) ≅ (G a).over (V i))) ↔
    (∃ V : Sieve (⊤_ C), V ∈ J (⊤_ C) ∧
      ∀ (U : C) (f : U ⟶ ⊤_ C), V f →
        ∃ a, P a ∧ Nonempty (M.over U ≅ (G a).over U)) := by
  constructor
  · rintro ⟨I, V, hV, hs⟩
    refine ⟨Sieve.ofObjects V _, hV _, ?_⟩
    rintro U f ⟨i, ⟨g⟩⟩
    obtain ⟨a, ha, ⟨e⟩⟩ := hs i
    exact ⟨a, ha, ⟨((SheafOfModules.overFunctorMap R g).app M).symm ≪≫
      (SheafOfModules.overMap R g).mapIso e ≪≫
        (SheafOfModules.overFunctorMap R g).app (G a)⟩⟩
  · rintro ⟨V, hV, hs⟩
    let I := Σ U : C, {f : U ⟶ ⊤_ C // V f}
    let W : I → C := fun i ↦ i.1
    refine ⟨I, W, ?_, fun i ↦ hs i.1 i.2.val i.2.property⟩
    apply (J.coversTop_iff_of_isTerminal _ terminalIsTerminal W).mpr
    apply J.superset_covering _ hV
    intro U f hf
    exact ⟨⟨U, f, hf⟩, ⟨𝟙 U⟩⟩

end AlgebraicGeometry.ProEtale
