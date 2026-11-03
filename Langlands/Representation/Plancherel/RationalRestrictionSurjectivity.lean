import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Surjectivity of actual unitary unramified restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The map on actual valuation images induced by the actual rational-point map. -/
def rationalValuationImageMap (f : H ⟶ G) :
    rationalDiscreteValuationImage H →* rationalDiscreteValuationImage G :=
  (rationalNormKernelQuotientEquiv G).toMonoidHom.comp
    ((QuotientGroup.map (rationalCommonNormKernel H) (rationalCommonNormKernel G)
      (GroupScheme.rationalPoints.map f) (rationalCommonNormKernel_le_comap f)).comp
        (rationalNormKernelQuotientEquiv H).symm.toMonoidHom)

@[simp]
theorem rationalValuationImageMap_projection (f : H ⟶ G)
    (h : GroupScheme.rationalPoints H) :
    rationalValuationImageMap f (rationalValuationImageProjection H h) =
      rationalValuationImageProjection G (GroupScheme.rationalPoints.map f h) := by
  have he : (rationalNormKernelQuotientEquiv H).symm
      (rationalValuationImageProjection H h) = QuotientGroup.mk h :=
    (rationalNormKernelQuotientEquiv H).symm_apply_eq.mpr
      (rationalNormKernelQuotientEquiv_mk H h).symm
  change rationalNormKernelQuotientEquiv G
    (QuotientGroup.map (rationalCommonNormKernel H) (rationalCommonNormKernel G)
      (GroupScheme.rationalPoints.map f) (rationalCommonNormKernel_le_comap f)
        ((rationalNormKernelQuotientEquiv H).symm
          (rationalValuationImageProjection H h))) = _
  rw [he, QuotientGroup.map_mk]
  exact rationalNormKernelQuotientEquiv_mk G _

/-- On integer coordinates this is precomposition by algebraic-character restriction. -/
theorem rationalValuationImageMap_apply (f : H ⟶ G)
    (a : rationalDiscreteValuationImage H) (chi : GroupScheme.rationalCharacters G) :
    (rationalValuationImageMap f a).val.toAdd chi =
      a.val.toAdd (GroupScheme.characterRestrict f chi) := by
  obtain ⟨h, rfl⟩ := rationalValuationImageProjection_surjective H a
  rw [rationalValuationImageMap_projection]
  exact (rationalCharacterValuation_characterRestrict f chi h).symm

/-- A finite-index algebraic-character restriction range detects integer valuations. -/
theorem rationalValuationImageMap_injective_of_finiteIndex (f : H ⟶ G)
    (hindex : (GroupScheme.characterRestrict f).range.FiniteIndex) :
    Function.Injective (rationalValuationImageMap f) := by
  let := hindex
  intro a b hab
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro chi
  obtain ⟨n, hn, _, psi, hpsi⟩ :=
    AddSubgroup.exists_nsmul_mem_of_index_ne_zero
      (H := (GroupScheme.characterRestrict f).range)
      AddSubgroup.FiniteIndex.index_ne_zero chi
  have hc := congrArg (fun x : rationalDiscreteValuationImage G => x.val.toAdd psi) hab
  simp only [rationalValuationImageMap_apply, hpsi, map_nsmul] at hc
  exact nsmul_right_injective (M := ℤ) hn.ne' hc

/-- The published finite-index restriction theorem applies to every split component. -/
theorem rationalValuationImageMap_injective {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hG : GroupScheme.IsConnectedReductive G)
    (hs : GroupScheme.IsSplitComponent s) :
    Function.Injective (rationalValuationImageMap s) :=
  rationalValuationImageMap_injective_of_finiteIndex s
    (hs.finiteIndex_range_characterRestrict hG)

private theorem exists_circle_character_extension {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (hf : Function.Injective f) (chi : A →* Circle) :
    ∃ psi : B →* Circle, psi.comp f = chi := by
  let : DivisibleBy (Additive Circle) ℤ :=
    Function.Surjective.divisibleBy Circle.expHom Circle.exp_surjective
      (fun x n => Circle.expHom.map_zsmul n x)
  obtain ⟨psi, hpsi⟩ :=
    (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
      f.toAdditive hf chi.toAdditive
  refine ⟨psi.toMultiplicative, ?_⟩
  apply MonoidHom.ext
  intro a
  exact DFunLike.congr_fun hpsi (Additive.ofMul a)

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance rationalRestrictionSurjectivityTargetPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalRestrictionSurjectivitySourcePointTopology :
    TopologicalSpace (GroupScheme.rationalPoints H) :=
  rationalPointTopology F H.X

/-- Injectivity of the actual image map suffices for surjectivity of unitary restriction. -/
theorem rationalUnitaryUnramifiedCharacterRestrict_surjective_of_injective (f : H ⟶ G)
    (hf : Function.Injective (rationalValuationImageMap f)) :
    Function.Surjective (rationalUnitaryUnramifiedCharacterRestrict f) := by
  intro chi
  let eta := (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).symm chi
  obtain ⟨psi, hpsi⟩ :=
    exists_circle_character_extension (rationalValuationImageMap f) hf eta.toMonoidHom
  let psi' : rationalUnitaryImageCharacters G :=
    ⟨psi, continuous_of_discreteTopology⟩
  refine ⟨rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G psi', ?_⟩
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro h
  apply Units.ext
  change (((rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G psi').val
    (GroupScheme.rationalPoints.map f h) : ℂˣ) : ℂ) = (chi.val h : ℂ)
  rw [rationalCanonicalUnitaryImageUnramifiedContinuousEquiv_apply]
  have he : psi (rationalValuationImageProjection G (GroupScheme.rationalPoints.map f h)) =
      eta (rationalValuationImageProjection H h) := by
    rw [← rationalValuationImageMap_projection f h]
    exact DFunLike.congr_fun hpsi (rationalValuationImageProjection H h)
  change (psi (rationalValuationImageProjection G (GroupScheme.rationalPoints.map f h)) : ℂ) = _
  rw [he]
  have hchi := (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).apply_symm_apply chi
  have hv := congrArg (fun z => ((z.val h : ℂˣ) : ℂ)) hchi
  exact hv

/-- Waldspurger I.1: actual unitary unramified restriction to a split component is onto. -/
theorem rationalUnitaryUnramifiedCharacterRestrict_surjective
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom]
    (s : T.toGrp ⟶ G) (hG : GroupScheme.IsConnectedReductive G)
    (hs : GroupScheme.IsSplitComponent s) :
    Function.Surjective (rationalUnitaryUnramifiedCharacterRestrict s) :=
  rationalUnitaryUnramifiedCharacterRestrict_surjective_of_injective s
    (rationalValuationImageMap_injective s hG hs)

end CanonicalTopology

end Langlands.Plancherel
