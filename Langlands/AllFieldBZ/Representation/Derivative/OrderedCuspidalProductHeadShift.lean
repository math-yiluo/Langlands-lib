import Langlands.AllFieldBZ.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductTwistOne
import Langlands.AllFieldBZ.Representation.Induction.SingleBlock
import Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift

/-!
# All-field port of `Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductHeadShift
open Langlands.Derivative.OrderedCuspidalProductHeadShift hiding headShift_false irreducible_support_of_injective
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- A nonzero representation embedded in the rank-transported carrier lift of a
supercuspidal representation `A` is irreducible and has the singleton support
`{[A]}`. -/
theorem irreducible_support_of_injective {d m : ℕ} (hd : 0 < d) (h : d = m) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d))
      (X : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) [Nontrivial X]
      (g : X ⟶ (generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} A.obj)),
      Function.Injective (SmoothRep.hom g) →
      X.IsIrreducible ∧
        T.IsSupercuspidalSupport X
          {(⟨d, hd, A.isoClass⟩ : Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T)} := by
  subst h
  let := T.topology
  intro A X _ g hg
  let L := SmoothRep.universeLift.{uF} A.obj
  have hirrL : L.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff A.obj).mpr A.property.1
  let g' : X.representation.IntertwiningMap L.representation := SmoothRep.hom g
  have hsurj : Function.Surjective g' := by
    let := hirrL
    rcases Representation.IsIrreducible.surjective_or_eq_zero g' with hs | h0
    · exact hs
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : X)
      apply hx
      apply hg
      change g' x = g' 0
      rw [h0, map_zero]
      rfl
  let e : X.representation.Equiv L.representation := g'.ofBijective ⟨hg, hsurj⟩
  have hirr : X.IsIrreducible := (isIrreducible_iff_of_equiv e).mpr hirrL
  refine ⟨hirr, ?_⟩
  let ρ1 : Fin 1 → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T := fun _ => ⟨d, hd, A.isoClass⟩
  have hsum : ∑ i, (ρ1 i).rank = d := by simp [ρ1]
  let AA : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ1 i).rank) := fun _ => A
  let B := T.cuspidalShape ρ1 hsum
  let e₀ := T.singleBlockNormalizedProductEquiv B rfl
    (fun i => (AA i).obj.representation) (fun i => (AA i).obj.isSmooth) (0 : Fin 1)
  let e₁ : ((T.cuspidalProductInduced ρ1 hsum AA).representation).Equiv L.representation :=
    e₀.trans (Representation.Equiv.mk (SmoothRep.universeLiftEquiv.{uF} A.obj).toLinearEquiv
      (fun g => by
        have hg : (GeneralLinear.reindex (R := F.Carrier)
            (finCongr (show d = d from B.singleBlock_size rfl (0 : Fin 1)))).symm g = g := by
          ext i j
          rfl
        ext v
        exact congrArg (fun x => ULift.up.{uF} (A.obj.representation x v)) hg))
  have hsub : SmoothRep.IsSubquotient X (T.cuspidalProductInduced ρ1 hsum AA) :=
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom (e₁.trans e.symm).toIntertwiningMap,
      (e₁.trans e.symm).toLinearEquiv.surjective⟩
  exact ⟨1, ρ1, by simp [ρ1], hsum, AA, fun _ => rfl, hirr, hsub⟩

/-- Case 2 of the proof of BZ77 Theorem 4.11. Let `W` be a mirabolic
representation embedded in the restriction of `A_1 × ⋯ × A_r`, of level
`k > 0`. If `W^(k)` is nonzero and embeds in the transported lift of the block
`A_{i₀}` (so `A_{i₀}` has rank `N + 1 - k`), and no block `A_j` with `j ≠ i₀`
is isomorphic to `ν A_{i₀}`, a contradiction follows. -/
theorem headShift_false :
    letI := T.topology
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {N : ℕ}
      (B : BlockShape (N + 1))
      (A : ∀ i : Fin B.length, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
      (i0 : Fin B.length),
      (∀ j, j ≠ i0 →
        (⟨B.size j, (A j).isoClass⟩ :
            Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
          ⟨B.size i0, T.supercuspidalClassRealPowerTwist (B.size i0) 1 (A i0).isoClass⟩) →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic N F.Carrier))
        (f : W ⟶ (generalLinearRestriction.{uF, max uF uV} T N).obj
          ((T.normalizedProductInductionFunctor.{uF, uV} B).obj (fun i => (A i).obj))),
        Function.Injective (SmoothRep.hom f) →
      ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), level T ψ W = k →
      ∀ (hsz : B.size i0 = N + 1 - k)
        (g : (mirabolicDerivativeOfOrder T ψ N k hk).obj W ⟶
          (generalLinearRankCast T hsz).obj (SmoothRep.universeLift.{uF} (A i0).obj)),
        Function.Injective (SmoothRep.hom g) →
        Nontrivial ((mirabolicDerivativeOfOrder T ψ N k hk).obj W) → False := by
  let := T.topology
  intro ψ N B A i0 hA0 W f hf k hk hlev hsz g hg hW
  let σ := (mirabolicDerivativeOfOrder T ψ N k hk).obj W
  obtain ⟨hirr, hsupp⟩ :=
    irreducible_support_of_injective F T (B.positive i0) hsz (A i0) σ g hg
  let ρ : Fin B.length → Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T :=
    fun i => ⟨B.size i, B.positive i, (A i).isoClass⟩
  have hρ : ∑ i, (ρ i).rank = N + 1 := B.sum_eq
  have hle := Classification.cuspidalProductMirabolicSupportShift F T ψ N B.length ρ hρ A
    (fun _ => rfl) W f hf k hk hlev σ
    ⟨hirr, Representation.IntertwiningMap.id σ.representation, fun _ _ h => h⟩ _ hsupp
  rw [Multiset.map_singleton, Multiset.singleton_le, Multiset.mem_coe, List.mem_ofFn] at hle
  obtain ⟨j, hj⟩ := hle
  by_cases hji : j = i0
  · subst hji
    exact OrderedCuspidalProductTwistOne.twist_one_ne_self T (ρ j) hj.symm
  · apply hA0 j hji
    have h1 := congrArg Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.rank hj
    have h2 := congrArg (fun c : Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData.CuspidalDatum.{uV, uF} T =>
      (⟨c.rank, c.cls⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d))) hj
    exact h2

end Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductHeadShift
