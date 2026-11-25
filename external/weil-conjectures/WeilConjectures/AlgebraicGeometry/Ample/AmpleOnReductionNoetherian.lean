/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.RingTheory.Noetherian.Nilpotent
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Ample.AmpleSquareZeroThickening

/-! # Ampleness on a Noetherian reduction

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS
(blueprint: lem-sc-ample-on-reduction-noetherian).

The invertibility of the pullback `i^*L` (the node's parenthetical) is the first clause of
the landed `Scheme.Modules.invertible_pullback_tensor`
(lem-weil-pbc-invertible-pullback-tensor); it is not restated here.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- The kernel is locally contained in the nilradical because its support is all of `X`.
On a finite affine cover, Noetherianity makes each section ideal finitely generated,
so each has a zero power. The maximum of these exponents kills the ideal on the cover,
and ideal-sheaf extensionality gives global vanishing. This includes the empty cover.
Source: Stacks Project, Lemma 09MS, first paragraph; Lemma 01Y9, its affine proof. -/
private theorem exists_ker_pow_eq_bot {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsLocallyNoetherian X] [CompactSpace X]
    (hi : IsHomeomorph i.base) : ∃ n : ℕ, i.ker ^ n = ⊥ := by
  classical
  let C := X.affineCover.finiteSubcover
  have : ∀ a, IsAffine (C.X a) := by
    intro a
    dsimp [C]
    rw [X.affineCover.finiteSubcover_X]
    infer_instance
  let U : C.I₀ → X.affineOpens := fun a ↦
    ⟨(C.f a).opensRange, isAffineOpen_opensRange (C.f a)⟩
  have hU : ⨆ a, (U a).1 = ⊤ := C.iSup_opensRange
  have hs : i.ker.support = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨z, hz⟩ := hi.surjective x
    exact i.range_subset_ker_support ⟨z, hz⟩
  have hle : i.ker ≤ X.nilradical := by
    have h := Scheme.IdealSheafData.le_radical i.ker
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, hs,
      Scheme.IdealSheafData.vanishingIdeal_top] at h
    exact h
  have hn : ∀ a : C.I₀, ∃ n : ℕ, (i.ker.ideal (U a)) ^ n = ⊥ := by
    intro a
    have : IsNoetherianRing Γ(X, (U a).1) :=
      IsLocallyNoetherian.component_noetherian (U a)
    apply (Ideal.FG.isNilpotent_iff_le_nilradical
      (IsNoetherian.noetherian (i.ker.ideal (U a)))).mpr
    exact hle (U a)
  choose n hn using hn
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  intro a
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot]
  apply le_bot_iff.mp
  exact (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ a))).trans (hn a).le

/-- On an affine open of `X`, the kernel of the composite is the inverse image of the
kernel of `j`. Surjectivity of the section map of `k` identifies the latter with the
image of the former. Its square is therefore zero if the composite kernel's square
lies in the kernel of `k`. The inverse images of affine opens cover `Y`.
Source: Stacks Project, Lemma 09MS, first paragraph, the square-zero transition ideals. -/
private theorem ker_square_eq_bot_of_comp {Z Y X : Scheme.{u}}
    (j : Z ⟶ Y) (k : Y ⟶ X) [IsClosedImmersion j] [IsClosedImmersion k]
    (h : (j ≫ k).ker ^ 2 ≤ k.ker) : j.ker ^ 2 = ⊥ := by
  let U : X.affineOpens → Y.affineOpens := fun V ↦ ⟨k ⁻¹ᵁ V.1, V.2.preimage k⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (k.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))
  intro V
  have hc : (j ≫ k).ker.ideal V =
      (j.ker.ideal (U V)).comap (k.app V.1).hom := by
    simp only [Scheme.Hom.ker_apply, Scheme.Hom.comp_app, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    rfl
  have hm : ((j ≫ k).ker.ideal V).map (k.app V.1).hom = j.ker.ideal (U V) := by
    rw [hc]
    exact Ideal.map_comap_of_surjective _ (k.app_surjective V.1 V.2) _
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot]
  rw [← hm, ← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).mpr
  simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
    using h V

/-- Induct on an exponent `n + 2` killing the ideal. At `n = 0`, use square-zero
lifting. In the successor case factor through the subscheme defined by the square
of the ideal. The first immersion has square-zero kernel, while the second has
nilpotency exponent at most `n + 2`, since `n + 3 ≤ 2 * (n + 2)`. Lift first along the
square-zero immersion, transport via composition of tensor pullbacks, and apply the
induction hypothesis to the second immersion.
Source: Stacks Project, Lemma 09MS, first paragraph, reduction to the square-zero case. -/
private theorem isAmple_of_ker_pow_eq_bot (n : ℕ) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    [CompactSpace Z] [CompactSpace X]
    (L : X.Modules) [L.IsInvertible] (hn : i.ker ^ (n + 2) = ⊥) :
    @Scheme.Modules.IsAmple Z ((Scheme.Modules.tensorPullback i).obj L)
        ((Scheme.Modules.invertible_pullback_tensor i).1 L).2 →
      Scheme.Modules.IsAmple X L := by
  induction n generalizing X Z with
  | zero =>
    exact Scheme.Modules.isAmple_of_isAmple_tensorPullback_of_square_zero i L hn
  | succ n ih =>
    intro hL
    let K := i.ker ^ 2
    let Y := K.subscheme
    let k : Y ⟶ X := K.subschemeι
    have : IsClosedImmersion k := inferInstance
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian k
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
    have hk : k.ker = i.ker ^ 2 := K.ker_subschemeι
    have hki : k.ker ≤ i.ker := by
      rw [hk]
      intro U
      simpa using (Ideal.pow_le_self (n := 2) (by decide) (I := i.ker.ideal U))
    let j : Z ⟶ Y := IsClosedImmersion.lift k i hki
    have hjk : j ≫ k = i := IsClosedImmersion.lift_fac k i hki
    have : IsClosedImmersion (j ≫ k) := hjk.symm ▸ inferInstance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp_isClosedImmersion j k
    have hj : j.ker ^ 2 = ⊥ := ker_square_eq_bot_of_comp j k (by rw [hjk, hk])
    let M := (Scheme.Modules.tensorPullback k).obj L
    have : M.IsInvertible := ((Scheme.Modules.invertible_pullback_tensor k).1 L).2
    have : ((Scheme.Modules.tensorPullback j).obj M).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor j).1 M).2
    have : ((Scheme.Modules.tensorPullback i).obj L).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor i).1 L).2
    obtain ⟨e⟩ := Scheme.Modules.nonempty_tensorPullbackComp j k
    rw [hjk] at e
    let eL : (Scheme.Modules.tensorPullback i).obj L ≅
        (Scheme.Modules.tensorPullback j).obj M := e.app L
    have hM : Scheme.Modules.IsAmple Y M :=
      Scheme.Modules.isAmple_of_isAmple_tensorPullback_of_square_zero j M hj
        ((Scheme.Modules.isAmple_iff_of_iso eL).mp hL)
    apply ih k L ?_ hM
    rw [hk, ← pow_mul]
    apply le_bot_iff.mp
    have hp : i.ker ^ (2 * (n + 2)) ≤ i.ker ^ (n + 1 + 2) := by
      intro U
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      apply Ideal.pow_le_pow_right
      omega
    exact hp.trans hn.le

/-- Ampleness of an invertible module is unchanged on a Noetherian closed subscheme
with the same underlying topological space.
Source: Stacks Project, Cohomology of Schemes, Lemma 09MS
(blueprint: lem-sc-ample-on-reduction-noetherian).
Proof: the forward implication follows from affine pullback along a closed immersion.
For the converse, the ideal sheaf is nilpotent, by the finitely generated ideal
radical-power lemma on a finite affine cover. Induct on its nilpotency exponent:
factor the immersion through the subscheme defined by the square of its ideal.
The first factor has square-zero kernel; the second has a smaller nilpotency bound.
Composition of tensor pullbacks and invariance of ampleness under module isomorphism
allow square-zero lifting followed by the induction hypothesis.
-/
theorem isAmple_iff_of_isClosedImmersion_of_isHomeomorph {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    [CompactSpace Z] [CompactSpace X]
    (hi : IsHomeomorph i.base) (L : X.Modules) [L.IsInvertible] :
    letI : ((Scheme.Modules.tensorPullback i).obj L).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor i).1 L).2
    AlgebraicGeometry.Scheme.Modules.IsAmple Z ((Scheme.Modules.tensorPullback i).obj L) ↔
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  constructor
  · intro hL
    obtain ⟨n, hn⟩ := exists_ker_pow_eq_bot i hi
    apply isAmple_of_ker_pow_eq_bot n i L ?_ hL
    apply le_bot_iff.mp
    have hp : i.ker ^ (n + 2) ≤ i.ker ^ n := by
      intro U
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact Ideal.pow_le_pow_right (by omega)
    exact hp.trans hn.le
  · exact Scheme.Modules.isAmple_tensorPullback_of_isAffineHom i L

end AlgebraicGeometry
