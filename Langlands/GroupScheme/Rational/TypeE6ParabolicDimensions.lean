import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Reductive.IsogenyRootIndex
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.CartanE6ParabolicRootCounts
import Langlands.LinearAlgebra.FiniteCartanExceptionalColumns
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv
import Langlands.LinearAlgebra.SubmoduleFinrank

/-! # Actual Lie dimensions of standard parabolics in type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open Langlands.RootReflectionCoefficients
open scoped BigOperators DirectSum

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

private local instance affineSource {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : SplitPinning G)

/-- The codimension of a parabolic from a cocharacter of the pinned maximal
split torus is the number of negative root pairings. -/
theorem dimension_parabolic_add_card_negative (ν : cocharacterLattice p.torus) :
    let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
    haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
    Lie.dimension (Dynamic.Affine.parabolicScheme χ) +
      Nat.card {r : p.rootIndex // p.rootDatum.root' r ν < 0} = Lie.dimension G := by
  classical
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  let : Finite p.rootIndex := p.finiteRootIndex
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : FiniteDimensional k (Additive (lieKernel G k)) := Lie.finiteDimensional_lieKernel G
  let b := AutomorphicAction.conjugation p.inclusion
  let W := RelativeRoot.actionWeightSpace b
  have hweight (x : characterLattice p.torus) : W x = weightSpace p.inclusion x :=
    RelativeRoot.actionWeightSpace_conjugation p.inclusion x
  let P : Set (characterLattice p.torus) := {a | 0 ≤ latticePairing p.torus a ν}
  let N : Set (characterLattice p.torus) := {a | latticePairing p.torus a ν < 0}
  let U := ⨆ a ∈ P, W a
  let V := ⨆ a ∈ N, W a
  have hU : RelativeRoot.tangentSubmodule (Dynamic.parabolic χ) = U := by
    rw [RelativeRoot.tangentSubmodule_parabolic_eq_semigroupWeightSpan
      p.isSplitTorus p.inclusion ν]
    exact iSup_subtype
  have hI := RelativeRoot.isInternal_actionWeightSpace b p.isSplitTorus
  have hpN : Disjoint P N := Set.disjoint_left.mpr fun a h₁ h₂ =>
    not_lt_of_ge (show 0 ≤ latticePairing p.torus a ν from h₁)
      (show latticePairing p.torus a ν < 0 from h₂)
  have hd : Disjoint U V := hI.submodule_iSupIndep.disjoint_biSup_biSup hpN
  have htop : U ⊔ V = ⊤ := by
    apply top_unique
    rw [← hI.submodule_iSup_eq_top]
    refine iSup_le fun a => ?_
    rcases le_or_gt 0 (latticePairing p.torus a ν) with ha | ha
    · exact (le_iSup_of_le a (le_iSup (fun _ : a ∈ P => W a) ha)).trans le_sup_left
    · exact (le_iSup_of_le a (le_iSup (fun _ : a ∈ N => W a) ha)).trans le_sup_right
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [htop, hd.eq_bot, finrank_top, finrank_bot, add_zero] at hsum
  let J := {r : p.rootIndex // p.rootDatum.root' r ν < 0}
  let f : J → characterLattice p.torus := fun r => p.rootDatum.root r.val
  let R : J → Submodule k (Additive (lieKernel G k)) := fun r => W (f r)
  have hg (r : p.rootIndex) : latticePairing p.torus (p.rootDatum.root r) ν = p.rootDatum.root' r ν := by
    change _ = p.rootDatum.toLinearMap (p.rootDatum.root r) ν
    rw [p.isRootDatum.1]
  have hV : V = ⨆ r : J, R r := by
    apply le_antisymm
    · refine iSup_le fun a => iSup_le fun ha => ?_
      change latticePairing p.torus a ν < 0 at ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        simp only [map_zero, LinearMap.zero_apply, lt_self_iff_false] at ha
      by_cases hab : weightSpace p.inclusion a = ⊥
      · rw [hweight, hab]
        exact bot_le
      · obtain ⟨r, rfl⟩ := p.isRootDatum.2.1 ▸ (show a ∈ roots p.inclusion from ⟨ha0, hab⟩)
        exact le_iSup R ⟨r, (hg r) ▸ ha⟩
    · refine iSup_le fun r => ?_
      have hr : f r ∈ N := by
        change latticePairing p.torus (p.rootDatum.root r.val) ν < 0
        rw [hg]
        exact r.property
      exact le_iSup_of_le (f r) (le_iSup (fun _ : f r ∈ N => W (f r)) hr)
  let : Fintype J := Fintype.ofFinite J
  have hinj : Function.Injective f := fun _ _ h => Subtype.ext (p.rootDatum.root.injective h)
  have hdimR (r : J) : Module.finrank k (R r) = 1 := by
    obtain ⟨e⟩ := splitRootLieLine k G p.isConnectedReductive p.torus p.isSplitTorus
      p.inclusion p.isMaximalTorus (f r) (p.isRootDatum.2.1 ▸ Set.mem_range_self r.val)
    change Module.finrank k (W (f r)) = 1
    rw [hweight, ← e.finrank_eq, Module.finrank_self]
  have hdimV : Module.finrank k V = Nat.card J := by
    have h := Langlands.Plancherel.finrank_biSup_eq_sum
      (hI.submodule_iSupIndep.comp hinj) (Finset.univ : Finset J)
    change Module.finrank k ↥(⨆ j ∈ (Finset.univ : Finset J), R j) =
      ∑ j, Module.finrank k (R j) at h
    have hu : (⨆ j ∈ (Finset.univ : Finset J), R j) = ⨆ j, R j := by
      apply le_antisymm
      · exact iSup_le fun j => iSup_le fun _ => le_iSup R j
      · exact iSup_le fun j => le_iSup_of_le j
          (le_iSup (fun _ : j ∈ (Finset.univ : Finset J) => R j) (Finset.mem_univ j))
    rw [hu] at h
    rw [hV, Nat.card_eq_fintype_card]
    simpa [hdimR] using h
  have hdimU : Module.finrank k U = Lie.dimension (Dynamic.Affine.parabolicScheme χ) := by
    rw [← hU]
    exact RelativeRoot.finrank_tangentSubmodule_eq_of_isRepresentedBy _
      (Dynamic.Affine.parabolicHom χ) (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
  change Lie.dimension (Dynamic.Affine.parabolicScheme χ) + Nat.card J = Lie.dimension G
  rw [← hdimU, ← hdimV]
  exact hsum.symm

end SplitPinning

open CartanE6Root Langlands.LinearAlgebra.FiniteCartanMatrix

/-- In split simply connected type E6 the ambient Lie dimension is 78. Each
omitted set is realized by an actual standard parabolic with codimension given
by the signed root count for that set. -/
def TypeE6ParabolicDimensionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : SplitPinning G),
    IsSimplyConnected G → ∀ e : p.base.support ≃ Fin 6,
    (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) →
    Lie.dimension G = 78 ∧ ∀ s : Finset (Fin 6),
      ∃ ν : cocharacterLattice p.torus,
        (∀ a : p.base.support, p.rootDatum.root' a.val ν = if e a ∈ s then 3 else 0) ∧
        let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
        haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
        IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) ∧
        Lie.dimension (Dynamic.Affine.parabolicScheme χ) + parabolicCodimension s = 78

theorem typeE6ParabolicDimensions : TypeE6ParabolicDimensionsStatement.{u} := by
  classical
  intro k _ G _ _ p hsc e hE
  let P := p.rootDatum
  let a : Fin 6 → p.rootIndex := fun i => (e.symm i).val
  let : Finite p.rootIndex := p.finiteRootIndex
  let : P.IsReduced := p.isReduced
  have hcart (i j : Fin 6) : P.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    simpa only [a, e.apply_symm_apply] using hE (e.symm i) (e.symm j)
  obtain ⟨f, hf⟩ := exists_signedRootEquiv P p.base e hcart
  have hcard : Nat.card p.rootIndex = 72 := by
    rw [← Nat.card_congr f, Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  have hspan : P.corootSpan ℤ = ⊤ := splitSimplyConnectedCorootSpan k G hsc p.torus
    p.isSplitTorus p.inclusion p.isMaximalTorus p.rootIndex P p.isRootDatum p.isReduced
  have hd : Lie.dimension G = 78 := by
    change Module.finrank k (Additive (lieKernel G k)) = _
    rw [p.isRootDatum.finrank_lie_eq_torus_add_card p.isConnectedReductive p.isSplitTorus
      p.isMaximalTorus, p.isSplitTorus.finrank_lieKernel_eq_cocharacter, hcard]
    have h := Module.finrank_eq_card_basis
      ((Langlands.RootDatumSimpleCorootEquiv.simpleCorootBasis p.base hspan).reindex e)
    rw [h, Fintype.card_fin]
  refine ⟨hd, fun s => ?_⟩
  let column := E6_columnMatrix
  let ν : cocharacterLattice p.torus := ∑ j ∈ s, ∑ i, column i j • P.coroot (a i)
  have hν (v : Fin 6) : P.root' (a v) ν = (if v ∈ s then 3 else 0) := by
    change P.toLinearMap (P.root (a v)) ν = _
    have hc (j : Fin 6) : ∑ i, column i j * CartanMatrix.E 6 v i = (if v = j then 3 else 0) := by
      have h := congrFun (congrFun E6_columnMatrix_mul v) j
      simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, mul_ite] using h
    simp only [ν, map_sum, map_smul, RootPairing.root_coroot_eq_pairing, smul_eq_mul, hcart, hc]
    simp [Finset.sum_ite_eq]
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  refine ⟨ν, fun i => ?_, ?_, ?_⟩
  · simpa only [a, e.symm_apply_apply] using hν (e i)
  · exact (parabolicDynamic k G p.isConnectedReductive _ (Dynamic.Affine.parabolicHom χ)
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)).mpr
      ⟨χ, (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2⟩
  · have hsign (r : Bool × Fin 36) : P.root' (f r) ν < 0 ↔
        (∑ i ∈ s, signedCoefficients r i) < 0 := by
      change P.toLinearMap (P.root (f r)) ν < 0 ↔ _
      rw [hf]
      have hh : P.toLinearMap (combination P a (signedCoefficients r)) ν =
          3 * ∑ i ∈ s, signedCoefficients r i := by
        simp only [combination, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
        change (∑ i, signedCoefficients r i * P.root' (a i) ν) = _
        have hs : ((Finset.univ : Finset (Fin 6)).filter fun i => i ∈ s) = s := by
          ext i
          simp
        simp only [hν, mul_ite, mul_zero, ← Finset.sum_filter, hs, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [hh]
      omega
    let ε : {r : Bool × Fin 36 // (∑ i ∈ s, signedCoefficients r i) < 0} ≃
        {r : p.rootIndex // P.root' r ν < 0} :=
      f.subtypeEquiv (fun r => (hsign r).symm)
    have hcount : Nat.card {i : p.rootIndex // P.root' i ν < 0} = parabolicCodimension s := by
      rw [← Nat.card_congr ε, Nat.card_eq_fintype_card]
      exact Fintype.card_subtype _
    rw [← hcount, ← hd]
    exact p.dimension_parabolic_add_card_negative ν

end Langlands.GroupScheme
