import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Torus.WeylImageFiniteStatement
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Set

/-! # Coroot uniqueness from finite normalizer image -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.LinearAlgebra

/-- Two integral reflections along the same vector, whose product has finite order,
have the same defining functional. -/
theorem eq_functional_of_finiteOrder_reflections
    {M : Type*} [AddCommGroup M] (x : M) (f g : M →ₗ[ℤ] ℤ)
    (s t : M ≃ₗ[ℤ] M) (hf : f x = 2) (hg : g x = 2)
    (hs : ∀ y, s y = y - f y • x) (ht : ∀ y, t y = y - g y • x)
    (hst : IsOfFinOrder (s * t)) : f = g := by
  let p := s * t
  have hp (y : M) : p y = y + (g y - f y) • x := by
    change s (t y) = _
    rw [ht, map_sub, map_smul, hs, hs, hf]
    module
  have hpx : p x = x := by
    rw [hp, hf, hg, sub_self, zero_smul, add_zero]
  have hpowx (n : ℕ) : (p ^ n) x = x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hpx, ih]
  have hpow (n : ℕ) (y : M) :
      (p ^ n) y = y + (n : ℤ) • ((g y - f y) • x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, hp, map_add, map_smul, hpowx, ih]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
  obtain ⟨n, hn, hnp⟩ := hst.exists_pow_eq_one
  have hn0 : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  ext y
  have he := hpow n y
  change ((s * t) ^ n) y = _ at he
  rw [hnp] at he
  have hz : (n : ℤ) • ((g y - f y) • x) = 0 := by
    have := congrArg (fun z : M => z - y) he
    simpa using this.symm
  have hscalar := congrArg f hz
  simp only [map_smul, hf, map_zero, smul_eq_mul] at hscalar
  have hdiff : g y - f y = 0 := by
    have := (mul_eq_zero.mp hscalar).resolve_left hn0
    exact (mul_eq_zero.mp this).resolve_right (by norm_num)
  exact (sub_eq_zero.mp hdiff).symm

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  {J : Type v} {J' : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T) (cocharacterLattice T)}

/-- The root index equivalence of two supplied actual root data is determined by their
common root range. No coroot comparison is needed for this construction. -/
def IsRootDatumOf.rootIndexEquiv (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i Q) : J ≃ J' :=
  (Equiv.ofInjective P.root P.root.injective).trans
    ((Set.equivOfEq (hP.2.1.trans hQ.2.1.symm)).trans
      (Equiv.ofInjective Q.root Q.root.injective).symm)

@[simp]
theorem IsRootDatumOf.rootIndexEquiv_root (hP : IsRootDatumOf i P)
    (hQ : IsRootDatumOf i Q) (j : J) :
    Q.root (hP.rootIndexEquiv i hQ j) = P.root j := by
  change Q.root ((Equiv.ofInjective Q.root Q.root.injective).symm _) = _
  exact congrArg Subtype.val ((Equiv.ofInjective Q.root Q.root.injective).apply_symm_apply _)

variable [Mono i.hom.hom.left]

/-- A finite full normalizer image identifies the coroot of each common root in any two
supplied actual root data, without a root-spanning premise. -/
theorem IsRootDatumOf.coroot_eq_of_finite_weylImage
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i Q) [Finite (weylImage i)]
    {j : J} {j' : J'} (hroot : P.root j = Q.root j') :
    P.coroot j = Q.coroot j' := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
  obtain ⟨m, τ, hm, hτ⟩ := hQ.2.2 j'
  let n' : normalizerPoints i := ⟨n, σ, hn⟩
  let m' : normalizerPoints i := ⟨m, τ, hm⟩
  have hs : weylAction i n' = P.reflection j := by
    ext χ
    rw [weylAction_eq i (n := n') (σ := σ) hn χ]
    change characterAut σ χ = _
    rw [hσ]
  have ht : weylAction i m' = Q.reflection j' := by
    ext χ
    rw [weylAction_eq i (n := m') (σ := τ) hm χ]
    change characterAut τ χ = _
    rw [hτ]
  let a : weylImage i := ⟨weylAction i n', n', rfl⟩
  let b : weylImage i := ⟨weylAction i m', m', rfl⟩
  have horder : IsOfFinOrder (P.reflection j * Q.reflection j') := by
    have h := (weylImage i).subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i n' * weylAction i m') at h
    rwa [hs, ht] at h
  let f := (latticePairing T).flip (P.coroot j)
  let g := (latticePairing T).flip (Q.coroot j')
  have hf : f (P.root j) = 2 := by
    change latticePairing T (P.root j) (P.coroot j) = 2
    rw [← hP.1]
    exact P.root_coroot_two j
  have hg : g (P.root j) = 2 := by
    change latticePairing T (P.root j) (Q.coroot j') = 2
    rw [hroot, ← hQ.1]
    exact Q.root_coroot_two j'
  have heq := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections
    (P.root j) f g (P.reflection j) (Q.reflection j') hf hg
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - P.toLinearMap χ (P.coroot j) • P.root j = _
      rw [hP.1]
      rfl)
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - Q.toLinearMap χ (Q.coroot j') • Q.root j' = _
      rw [hQ.1, ← hroot]
      rfl) horder
  apply P.flip.toPerfPair.injective
  ext χ
  change P.toLinearMap χ (P.coroot j) = P.toLinearMap χ (Q.coroot j')
  rw [hP.1]
  exact LinearMap.congr_fun heq χ

/-- The root-range equivalence also matches coroots when the full normalizer image is finite. -/
theorem IsRootDatumOf.rootIndexEquiv_coroot (hP : IsRootDatumOf i P)
    (hQ : IsRootDatumOf i Q) [Finite (weylImage i)] (j : J) :
    Q.coroot (hP.rootIndexEquiv i hQ j) = P.coroot j :=
  (hP.coroot_eq_of_finite_weylImage i hQ (hP.rootIndexEquiv_root i hQ j).symm).symm

/-- General finite normalizer-image geometry suffices for the published reductive
root-datum uniqueness target. The finiteness proposition remains an explicit premise. -/
theorem rootDatumUniqueness_of_weylImageFinite
    (hfinite : SplitTorusWeylImageFiniteStatement.{u}) : RootDatumUniquenessStatement.{u} := by
  intro k _ G hG T hT i hi J J' P Q hP hQ
  have := hG.isAffineHom
  have := hG.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Finite (weylImage i) := hfinite k G T hT i hi.2.1
  exact ⟨hP.rootIndexEquiv i hQ, funext (hP.rootIndexEquiv_root i hQ),
    funext (hP.rootIndexEquiv_coroot i hQ)⟩

end Langlands.GroupScheme
