import Langlands.Global.AdelicEisensteinWeylSeparationStatement
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.SubtorusIntertwiningRoots
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone

/-! # Weyl separation from the leading chamber -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Global.AdelicGroupPoints Langlands.Plancherel RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- A nonidentity Weyl element preserving positivity on roots trivial on the
split component sends a regular parameter to a vector with a negative
ambient root pairing beyond the original threshold. -/
theorem exists_ambientRoot_pairing_lt_neg_of_regular
    (hG : IsConnectedReductive G) (w : relativeWeylGroup r.data.i) (hw : w ≠ 1)
    (hpos : ∀ α ∈ positiveRelativeRoots r.data.i r.data.ν, r.data.f ≫ α = 0 →
      schemeWeylCharacterAction r.data.i w α ∈ positiveRelativeRoots r.data.i r.data.ν)
    (R : ℝ) (lam : ComplexCharacterParameter F P) (hreg : r.IsRegularParameter hA hT R lam) :
    ∃ β ∈ positiveRelativeRoots r.data.i r.data.ν,
      relativeWeylInvariantForm r.data.i hT
        (relativeWeylRealCharacterAction r.data.i w
          (weylCharacterRestrictionLift hA hT r.data.f r.data.i
            (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))))
        ((1 : ℝ) ⊗ₜ[ℤ] β) < -R := by
  obtain ⟨_, _, _, cs, hcs⟩ :=
    relativeWeylCoxeter F G hG r.data.T r.data.i r.isCompatible.maximalSplit r.data.ν
      r.isCompatible.generic
  have hI : (relativeInversionSet r.data.i r.data.ν w).Nonempty := by
    by_contra h
    have hem := Set.not_nonempty_iff_eq_empty.mp h
    exact hw (cs.length_eq_zero_iff.mp (by rw [hcs.2.2.2.1, hem, Set.ncard_empty]))
  obtain ⟨α, hα, hβ⟩ := hI
  have hαpos := hα.1
  have hαn0 : r.data.f ≫ α ≠ 0 := by
    intro hα0
    have hpositive := (hpos α hαpos hα0).2
    have hnegative := hβ.2
    rw [map_neg, LinearMap.neg_apply] at hnegative
    omega
  let y := realParameterRestriction (a ≫ l) (parameterRealPart F P lam)
  let x := weylCharacterRestrictionLift hA hT r.data.f r.data.i y
  let B := relativeWeylInvariantForm r.data.i hT
  let v := relativeWeylRealCharacterAction r.data.i w x
  have hpair : R < B x ((1 : ℝ) ⊗ₜ[ℤ] α) :=
    (weylInducedCharacterForm_root_inequality_iff hA hT r.data.f r.data.i y α R).mpr
      (hreg (r.data.f ≫ α) ⟨hαn0, α, hαpos, rfl⟩)
  have hform := relativeWeylInvariantForm_invariant r.data.i hT w x ((1 : ℝ) ⊗ₜ[ℤ] α)
  rw [relativeWeylRealCharacterAction_tmul] at hform
  change B v ((1 : ℝ) ⊗ₜ[ℤ] schemeWeylCharacterAction r.data.i w α) =
    B x ((1 : ℝ) ⊗ₜ[ℤ] α) at hform
  refine ⟨_, hβ, ?_⟩
  change B v ((1 : ℝ) ⊗ₜ[ℤ] (-schemeWeylCharacterAction r.data.i w α)) < -R
  rw [TensorProduct.tmul_neg, map_neg, hform]
  exact neg_lt_neg hpair

omit [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left] in
private theorem maps_positiveRoot_of_restrict_eq_zero
    (w : relativeWeylGroup r.data.i)
    (hpos : ∀ α ∈ r.data.J,
      schemeWeylCharacterAction r.data.i w α ∈ positiveRelativeRoots r.data.i r.data.ν)
    {α : characterLattice r.data.T} (hα : α ∈ positiveRelativeRoots r.data.i r.data.ν)
    (hα0 : r.data.f ≫ α = 0) :
    schemeWeylCharacterAction r.data.i w α ∈ positiveRelativeRoots r.data.i r.data.ν := by
  have hzero : latticePairing r.data.T α (cocharacterMapInt r.data.f r.splitComponentCocharacter) =
      0 := by
    rw [← RelativeRoot.latticePairing_restrict_cocharacterMapInt, hα0, map_zero,
      LinearMap.zero_apply]
  have hcl := (r.isStandard_splitComponentCocharacter.pairing_eq_zero_iff_mem_closure
    r.data.i r.data.ν hα).mp hzero
  have hnonneg : ∀ δ ∈ AddSubmonoid.closure r.data.J,
      0 ≤ latticePairing r.data.T (schemeWeylCharacterAction r.data.i w δ) r.data.ν := by
    intro δ hδ
    induction hδ using AddSubmonoid.closure_induction with
    | mem x hx => exact (hpos x hx).2.le
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, LinearMap.add_apply]
      exact add_nonneg hx hy
  have hroot : schemeWeylCharacterAction r.data.i w α ∈ relativeRoots r.data.i :=
    relativeWeylLatticeAction_mapsTo_relativeRoots r.data.i w hα.1
  exact ⟨hroot, lt_of_le_of_ne (hnonneg α hcl) (r.isCompatible.generic _ hroot).symm⟩

/-- A single regularity threshold excludes a finite family of shifted
nonidentity Weyl translates from the ambient closed positive chamber. -/
theorem exists_regular_bound_for_ambient_chamber_separation [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) {S : Set (Vstar r.data.T)} (hS : S.Finite) :
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ w : relativeWeylGroup r.data.i, w ≠ 1 →
        (∀ α ∈ r.data.J, schemeWeylCharacterAction r.data.i w α ∈
          positiveRelativeRoots r.data.i r.data.ν) →
        ∀ shift ∈ S, ∃ β ∈ simpleRelativeRoots r.data.i r.data.ν,
          relativeWeylInvariantForm r.data.i hT
            (relativeWeylRealCharacterAction r.data.i w
              (weylCharacterRestrictionLift hA hT r.data.f r.data.i
                (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))) + shift)
            ((1 : ℝ) ⊗ₜ[ℤ] β) < 0 := by
  let B := relativeWeylInvariantForm r.data.i hT
  let rootPair (z : Vstar r.data.T × characterLattice r.data.T) : ℝ :=
    B z.1 ((1 : ℝ) ⊗ₜ[ℤ] z.2)
  have hfinite := hS.prod (hT.finite_positiveRelativeRoots r.data.i r.data.ν)
  obtain ⟨R, hR⟩ := (hfinite.image rootPair).bddAbove
  refine ⟨R, fun lam hlam w hw hpos shift hshift => ?_⟩
  obtain ⟨α, hα, hneg⟩ := r.exists_ambientRoot_pairing_lt_neg_of_regular hA hT
    hG w hw (fun β hβ hβ0 => r.maps_positiveRoot_of_restrict_eq_zero w hpos hβ hβ0) R lam hlam
  let x := relativeWeylRealCharacterAction r.data.i w
    (weylCharacterRestrictionLift hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)))
  have hshiftR : B shift ((1 : ℝ) ⊗ₜ[ℤ] α) ≤ R :=
    hR ⟨(shift, α), ⟨hshift, hα⟩, rfl⟩
  have hlt : B (x + shift) ((1 : ℝ) ⊗ₜ[ℤ] α) < 0 := by
    rw [map_add, LinearMap.add_apply]
    change B x ((1 : ℝ) ⊗ₜ[ℤ] α) < -R at hneg
    linarith
  change ∃ β ∈ simpleRelativeRoots r.data.i r.data.ν, B (x + shift) ((1 : ℝ) ⊗ₜ[ℤ] β) < 0
  by_contra! hall
  have hn : 0 ≤ B (x + shift) ((1 : ℝ) ⊗ₜ[ℤ] α) := by
    refine positiveRelativeRoots_induction r.data.i r.data.ν hall ?_ hα
    intro β₁ _ β₂ _ hβ₁ hβ₂
    rw [TensorProduct.tmul_add, map_add]
    exact add_nonneg hβ₁ hβ₂
  exact (not_lt_of_ge hn) hlt

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Global

/-- Shifted Weyl chamber separation for the actual parabolic presentations. -/
theorem eisensteinAmbientWeylSeparation : EisensteinAmbientWeylSeparationStatement.{u} := by
  intro F _ G P M A _ _ p l a r _ _ _ hA hT hG S hS
  exact r.exists_regular_bound_for_ambient_chamber_separation hA hT hG hS

end Langlands.Global
