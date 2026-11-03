import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Torus.Maximal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.WellFounded

/-! # Maximal extensions of actual tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
local notation "S" => Spec (CommRingCat.of k)

/-- A closed torus in an affine group whose coordinate ring has finite Krull
dimension factors through a maximal torus. -/
theorem exists_maximalTorus_extension_of_finiteRingKrullDim
    (G : GroupScheme S) [IsAffineHom G.X.hom]
    [FiniteRingKrullDim Γ(G.X.left, ⊤)]
    {T : CommGroupScheme S} (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (M : CommGroupScheme S) (j : M.toGrp ⟶ G), IsMaximalTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let U : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top G.X.left⟩
  have hprime (M : CommGroupScheme S) (j : M.toGrp ⟶ G)
      (hM : IsTorus M.toGrp) (hj : IsClosedSubgroup j) :
      (j.hom.hom.left.ker.ideal U).IsPrime := by
    let : IsIntegral M.toGrp.X.left := hM.isIntegral
    let : IsClosedImmersion j.hom.hom.left := hj
    rw [Scheme.Hom.ker_apply]
    change (RingHom.ker j.hom.hom.left.appTop.hom).IsPrime
    exact RingHom.ker_isPrime _
  let kernels : Set (PrimeSpectrum Γ(G.X.left, ⊤)) :=
    {P | ∃ (M : CommGroupScheme S) (j : M.toGrp ⟶ G),
      IsTorus M.toGrp ∧ IsClosedSubgroup j ∧
      (∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i) ∧
      j.hom.hom.left.ker.ideal U = P.asIdeal}
  have hne : kernels.Nonempty :=
    ⟨⟨i.hom.hom.left.ker.ideal U, hprime T i hT hi⟩,
      T, i, hT, hi, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  have hwf : WellFounded
      ((· < ·) : PrimeSpectrum Γ(G.X.left, ⊤) → PrimeSpectrum Γ(G.X.left, ⊤) → Prop) :=
    SetRel.IsWellFounded.of_finiteDimensional
      {(a, b) : PrimeSpectrum Γ(G.X.left, ⊤) × PrimeSpectrum Γ(G.X.left, ⊤) | a < b}
  obtain ⟨P, hP, hmin⟩ := hwf.has_min kernels hne
  obtain ⟨M, j, hM, hj, ⟨f, hf⟩, hP⟩ := hP
  refine ⟨M, j, ⟨hM, hj, ?_⟩, f, hf⟩
  intro M' j' a hM' hj' ha
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion j'.hom.hom.left := hj'
  have hs : a.hom.hom.left ≫ j'.hom.hom.left = j.hom.hom.left :=
    congrArg (fun z => z.hom.hom.left) ha
  let P' : PrimeSpectrum Γ(G.X.left, ⊤) :=
    ⟨j'.hom.hom.left.ker.ideal U, hprime M' j' hM' hj'⟩
  have hmem : P' ∈ kernels := by
    refine ⟨M', j', hM', hj', ⟨f ≫ a, ?_⟩, rfl⟩
    rw [Category.assoc, ha, hf]
  have hle : P' ≤ P := by
    change j'.hom.hom.left.ker.ideal U ≤ P.asIdeal
    rw [← hP, ← hs]
    exact Scheme.Hom.le_ker_comp _ _ U
  have heq : P' = P := eq_of_le_of_not_lt hle (hmin P' hmem)
  have hker : j.hom.hom.left.ker = j'.hom.hom.left.ker := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    exact hP.trans (congrArg PrimeSpectrum.asIdeal heq).symm
  have : IsIso a.hom.hom.left :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ hs hker
  have : IsIso a.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso a.hom.hom.left from inferInstance)
  have : IsIso a.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp
      (show IsIso a.hom.hom from inferInstance)
  exact (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp
    (show IsIso a.hom from inferInstance)

/-- A chosen maximal torus through which the given closed torus factors, with
its maximality and factorization witnesses. -/
def maximalTorusExtensionOfFiniteRingKrullDim
    (G : GroupScheme S) [IsAffineHom G.X.hom]
    [FiniteRingKrullDim Γ(G.X.left, ⊤)]
    {T : CommGroupScheme S} (i : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    Σ M : CommGroupScheme S, {j : M.toGrp ⟶ G // IsMaximalTorus j ∧
      ∃ f : T.toGrp ⟶ M.toGrp, f ≫ j = i} :=
  let h := exists_maximalTorus_extension_of_finiteRingKrullDim G i hT hi
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
