import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # Root-datum isogenies on the actual extended split-torus lattices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitRootDatum

variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))

include hT in
/-- Actual character pullback preserves finite generation of a split-torus lattice. -/
theorem characterFiniteBaseChange [Module.Finite ℤ (characterLattice T)] :
    Module.Finite ℤ (characterLattice ((CommGroupScheme.baseChange b).obj T)) :=
  Module.Finite.equiv (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv

include hT in
/-- Actual cocharacter pullback preserves finite generation of a split-torus lattice. -/
theorem cocharacterFiniteBaseChange [Module.Finite ℤ (cocharacterLattice T)] :
    Module.Finite ℤ (cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :=
  Module.Finite.equiv (cocharacterLattice.baseChangeEquiv b T hT).toIntLinearEquiv

/-- The actual lattice transport preserves reducedness. -/
instance baseChange_isReduced [P.IsReduced] : (baseChange b T hT P).IsReduced where
  eq_or_eq_neg a c h := by
    have hdep : ¬ LinearIndependent ℤ ![P.root a, P.root c] := by
      intro hind
      apply h
      convert hind.map'
        (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv.toLinearMap
        (LinearMap.ker_eq_bot.mpr (characterLattice.baseChangeEquiv b T hT).injective) using 1
      ext j
      fin_cases j <;> rfl
    rcases RootPairing.IsReduced.eq_or_eq_neg a c hdep with heq | heq
    · exact Or.inl (congrArg (characterLattice.baseChange b T) heq)
    · right
      change characterLattice.baseChange b T (P.root a) =
        -characterLattice.baseChange b T (P.root c)
      simpa only [map_neg] using congrArg (characterLattice.baseChange b T) heq

end SplitRootDatum

namespace RootDatumIsogenyRealization

variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    {J : Type v} {J' : Type w} [Finite J] [Finite J']
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [Module.Finite ℤ (characterLattice ((CommGroupScheme.baseChange b).obj T))]
    [Module.Finite ℤ (cocharacterLattice ((CommGroupScheme.baseChange b).obj T))]
    [Module.Finite ℤ (characterLattice ((CommGroupScheme.baseChange b).obj T'))]
    [Module.Finite ℤ (cocharacterLattice ((CommGroupScheme.baseChange b).obj T'))]
    [P.IsReduced] [P'.IsReduced] {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)

local notation "eX" => (AddEquiv.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance) (characterLattice.baseChangeEquiv b T hT))
local notation "eY" => (AddEquiv.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance) (cocharacterLattice.baseChangeEquiv b T hT))
local notation "eX'" => (AddEquiv.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance) (characterLattice.baseChangeEquiv b T' hT'))
local notation "eY'" => (AddEquiv.toIntLinearEquiv (modM := inferInstance) (modM₂ := inferInstance) (cocharacterLattice.baseChangeEquiv b T' hT'))

/-- Conjugate both lattice maps by actual pullback, retaining every root factor. -/
def rootDatumIsogenyBaseChange :
    Langlands.LinearAlgebra.RootDatumIsogeny p (SplitRootDatum.baseChange b T' hT' P')
      (SplitRootDatum.baseChange b T hT P) where
  characteristicExponent := f.characteristicExponent
  weightMap := (eX).toLinearMap ∘ₗ f.weightMap ∘ₗ (eX').symm.toLinearMap
  coweightMap := (eY').toLinearMap ∘ₗ f.coweightMap ∘ₗ (eY).symm.toLinearMap
  indexEquiv := f.indexEquiv
  weightMap_injective := (eX).injective.comp (f.weightMap_injective.comp (eX').symm.injective)
  coweightMap_injective := (eY').injective.comp (f.coweightMap_injective.comp (eY).symm.injective)
  weight_coweight_transpose := by
    ext ν χ
    obtain ⟨ν₀, hν⟩ := (eY).surjective ν
    obtain ⟨χ₀, hχ⟩ := (eX').surjective χ
    rw [← hν, ← hχ]
    change (SplitRootDatum.baseChange b T hT P).toLinearMap
        (eX (f.weightMap ((eX').symm (eX' χ₀)))) (eY ν₀) =
      (SplitRootDatum.baseChange b T' hT' P').toLinearMap
        (eX' χ₀) (eY' (f.coweightMap ((eY).symm (eY ν₀))))
    simp only [LinearEquiv.symm_apply_apply]
    exact (SplitRootDatum.baseChange_pairing b T hT P _ _).trans
      ((f.pairing_apply χ₀ ν₀).trans (SplitRootDatum.baseChange_pairing b T' hT' P' _ _).symm)
  rootFactor := f.rootFactor
  rootFactor_pow := f.rootFactor_pow
  root_weightMap := by
    intro a
    change eX (f.weightMap ((eX').symm (eX' (P'.root a)))) =
      (f.rootFactor a : ℤ) • eX (P.root (f.indexEquiv a))
    rw [LinearEquiv.symm_apply_apply, f.root_weightMap, map_smul]
  coroot_coweightMap := by
    intro a
    change eY' (f.coweightMap ((eY).symm (eY (P.coroot (f.indexEquiv a))))) =
      (f.rootFactor a : ℤ) • eY' (P'.coroot a)
    rw [LinearEquiv.symm_apply_apply, f.coroot_coweightMap, map_smul]

@[simp]
theorem rootDatumIsogenyBaseChange_weight (χ : characterLattice T') :
    (rootDatumIsogenyBaseChange b hT hT' f).weightMap
        (characterLattice.baseChange b T' χ) =
      characterLattice.baseChange b T (f.weightMap χ) := by
  change eX (f.weightMap ((eX').symm (eX' χ))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
theorem rootDatumIsogenyBaseChange_coweight (ν : cocharacterLattice T) :
    (rootDatumIsogenyBaseChange b hT hT' f).coweightMap
        (cocharacterLattice.baseChange b T ν) =
      cocharacterLattice.baseChange b T' (f.coweightMap ν) := by
  change eY' (f.coweightMap ((eY).symm (eY ν))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- A supplied actual torus map still induces the transported weight map. -/
theorem rootDatumIsogenyBaseChange_torus (t : T ⟶ T')
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T')) :
    (CommGroupScheme.baseChange b).map t ≫ χ =
      (rootDatumIsogenyBaseChange b hT hT' f).weightMap χ := by
  obtain ⟨χ₀, hχ⟩ := (eX').surjective χ
  rw [← hχ]
  change (CommGroupScheme.baseChange b).map t ≫ characterLattice.baseChange b T' χ₀ = _
  rw [← characterLattice.baseChange_precomp, hw]
  exact (rootDatumIsogenyBaseChange_weight b hT hT' f χ₀).symm

end RootDatumIsogenyRealization

end Langlands.GroupScheme
