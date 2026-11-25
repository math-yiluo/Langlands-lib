/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionCount
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorMonodromyHom

/-!
# Nondegeneracy and reduction of the pairing between torsors and torsion line bundles

Let `X` be a smooth proper connected curve over an algebraically closed field `k`, with a
geometric point `s` and fundamental group `G = π₁(X, s)`, and let `l` be a prime invertible in
`k`. For a `ℤ / lⁿ`-torsor `t` on `X`, the character
`AlgebraicGeometry.Scheme.EtaleTorsor.picPairing t : Pic(X)[lⁿ] ⟶ ℤ / lⁿ` is

* nondegenerate: if it vanishes, `t` has a section
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_picPairing_eq_zero`). Otherwise the
  monodromy of `t` is `lᵃ` times a surjective character, `a < n`, i.e. `t` is `lᵃ` times a
  torsor `t'` with connected total space; the cup product with `t'` is surjective onto
  `H²(X, μ_{lⁿ}) ≅ ℤ / lⁿ`, so that with `t`, which is `lᵃ` times it, does not vanish;
* compatible with reduction: if the monodromy of `t` is the reduction of that of a
  `ℤ / lⁿ⁺¹`-torsor `t'`, the character of `t` on `l y` is the reduction of that of `t'` on `y`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.picPairing_zsmul_of_monodromy`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

omit [ConnectedSpace X] in
/-- If the character `Pic(X)[m] ⟶ ℤ / m` attached to a torsor vanishes, so does the cup product
with its class. -/
lemma cupMu_eq_zero_of_picPairing_eq_zero [GeometricallyIntegral (X ↘ Spec (.of k))]
    [Nonempty X] {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) (h : t.picPairing hm = 0)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) : t.cupMu x = 0 := by
  apply (bijective_sheafHTwoTrace (X := X) m hm).1
  have := DFunLike.congr_fun h (kummerTorsionEquiv m hm x)
  rwa [picPairing_apply, AddEquiv.symm_apply_apply, AddMonoidHom.zero_apply, ← map_zero
    (sheafHTwoTrace (X := X) m hm)] at this

include s G in
/-- **Nondegeneracy.** Suppose that `π₁(X, s)` has exactly `l ^ (r k)` continuous characters
with values in `ℤ / lᵏ` for `k ≤ n`. A `ℤ / lⁿ`-torsor whose character
`Pic(X)[lⁿ] ⟶ ℤ / lⁿ` vanishes has a section. -/
theorem exists_section_of_picPairing_eq_zero [GeometricallyIntegral (X ↘ Spec (.of k))]
    [Nonempty X] {l : ℕ} [Fact l.Prime] {n r : ℕ}
    (hcard : ∀ k ≤ n, Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ k)))) =
      l ^ (r * k)) [NeZero (l ^ n)] (hm : ((l ^ n : ℕ) : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) X) (h : t.picPairing hm = 0) :
    ∃ σ : X ⟶ t.P, σ ≫ t.π = 𝟙 X := by
  by_contra ht
  obtain ⟨a, ha, t', hs, hχ⟩ := exists_monodromy_eq_pow_smul s G hcard t ht
  have : ConnectedSpace t'.P := connectedSpace_of_surjective_monodromy s G t' fun c ↦ by
    obtain ⟨g, hg⟩ := hs c.down
    exact ⟨g, ULift.ext hg⟩
  obtain ⟨f, hf, hv⟩ := exists_hom_of_monodromy s G ((l ^ a) • AddMonoidHom.id _) t' t
    fun g ↦ (hχ g).symm
  have hc : t'.vadd 1 ≫ f = f ≫ t.vadd ((l ^ a) • 1) := hv 1
  have hdvd := dvd_of_forall_nsmul_cupMu_eq_zero hm t' (l ^ a) fun x ↦ by
    rw [← map_nsmul, ← cupMu_eq_cupMu_nsmul t t' f hf _ hc]
    exact cupMu_eq_zero_of_picPairing_eq_zero hm t h x
  exact absurd ((Nat.pow_dvd_pow_iff_le_right (Fact.out : l.Prime).one_lt).1 hdvd) (by omega)

include s G in
/-- **Compatibility with reduction.** Let `t` be a `ℤ / lⁿ`-torsor and `t'` a `ℤ / lⁿ⁺¹`-torsor
whose monodromy reduces to that of `t`. Then the character of `t` on `l y` is the reduction of
the character of `t'` on `y`, for `y ∈ Pic(X)[lⁿ⁺¹]`. -/
theorem picPairing_zsmul_of_monodromy {l n : ℕ} [Fact l.Prime]
    [NeZero (l ^ n)] [NeZero (l ^ (n + 1))] (hm : ((l ^ n : ℕ) : k) ≠ 0)
    (hm' : ((l ^ (n + 1) : ℕ) : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) X)
    (t' : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ (n + 1)))) X)
    (h : ∀ g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      (t'.monodromy s G g).toAdd.down = (t.monodromy s G g).toAdd.down)
    (y : AddSubgroup.torsionBy (Additive X.Pic) ((l ^ (n + 1) : ℕ) : ℤ))
    (hy : (l : ℤ) • (y : Additive X.Pic) ∈ AddSubgroup.torsionBy (Additive X.Pic)
      ((l ^ n : ℕ) : ℤ)) :
    t.picPairing hm ⟨_, hy⟩ = ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
      (t'.picPairing hm' y) := by
  let φ : ULift.{u + 1} (ZMod (l ^ (n + 1))) →+ ULift.{u + 1} (ZMod (l ^ n)) :=
    (ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))).toAddMonoidHom.uliftMap
  obtain ⟨f, hf, hv⟩ := exists_hom_of_monodromy s G φ t' t fun g ↦ ULift.ext (h g)
  have hc : t'.vadd 1 ≫ f = f ≫ t.vadd (1 • 1) := by
    rw [hv 1, one_nsmul]
    congr 2
    exact ULift.ext (map_one (ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) _))
  exact picPairing_nsmul (pow_succ l n) hm hm' t t' f hf hc y hy

end AlgebraicGeometry.Scheme.EtaleTorsor
