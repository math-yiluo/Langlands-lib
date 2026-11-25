import Langlands.GaloisCohomology.CompactSupport.TateModified.OrderTwo
import Langlands.GaloisCohomology.Field.CartierDual
import Langlands.GaloisCohomology.Field.KummerSequence
import Langlands.Cohomology.Profinite.Cup.Pairing
import Langlands.GaloisCohomology.Global.BrauerSequence.Existence

/-!
# Local duality at the real places

Let `L/K` be an extension of fields whose Galois group is `{1, c}` with `c ≠ 1`, and let
`inv : H²(Gal(L/K), Lˣ) → ℚ/ℤ` be a homomorphism taking the value `1/2` on the class of the
`2`-cocycle supported at `(c, c)` with value `t` for every `t ≠ 1` with `t² = 1`. Suppose that `c`
acts on the roots of unity of `L` by inversion and that `μ_k(L) ≅ ℤ/k` for every `k > 0`. Then for
every finite discrete module `M` with Cartier dual `M' = Hom(M, Lˣ)`, the cup product followed by
`inv` (`orderTwoDualityPairing`) gives perfect pairings

* `Ĥ⁰(Gal(L/K), M) × H²(Gal(L/K), M') → ℚ/ℤ` (`orderTwoDualityPairingZeroTwo`),
* `H¹(Gal(L/K), M) × H¹(Gal(L/K), M') → ℚ/ℤ`,
* `H²(Gal(L/K), M) × Ĥ⁰(Gal(L/K), M') → ℚ/ℤ` (`orderTwoDualityPairingTwoZero`),

each with its flip (`orderTwoLocalDuality`). Here `Ĥ⁰` is Tate's modified group `H⁰/N`
(`cohomologyTateZero`).

The proof identifies each pairing with the pairing `tatePair` of a finite group with an involution
and its dual involution (`Involution.tatePair_bijective`): `H¹`, `H²` and `Ĥ⁰` of a group of order
two are the groups `ker(σ)/im(τ)` of `σ = −c, c` (`OrderTwo.h1EquivOfOrderTwo`,
`OrderTwo.h2EquivOfOrderTwo`, `OrderTwo.cohomZeroEquivContinuous`), the Cartier dual is
`Hom(M, ℚ/ℤ)` with `c` acting as the dual involution (`cartierDualEquivQZ`, `cartierDualToQZ_act`),
and the cup product of explicit cocycles is the cocycle supported at `(c, c)` whose value is the
evaluation (`cupPairing_cocycleOne`, `cupPairing_cocycleTwo_zero`, `cupPairing_zero_cocycleTwo`).

At a real place `w` of a number field `K`, with `K̄_w` the algebraic closure of the completion,
complex conjugation `closureConj`, and the real invariant of the local Brauer group
(`realInvariantHom`, as `realInvariantQZ`), the three conditions hold
(`realInvariantQZ_cocycleTwo`, `closureConj_unitsModule_of_torsion`,
`nonempty_rootsOfUnityModule_addEquiv_zmod`), which gives local duality for `Gal(K̄_w/K_w) ≅
Gal(ℂ/ℝ)` (`realLocalDuality`).
-/

noncomputable section

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology
open CategoryTheory MonoidalCategory Involution OrderTwo

universe u

section Neg

variable {M : Type*} [AddCommGroup M]

/-- The dual of `−σ` is `−` the dual of `σ`. -/
theorem Involution.dualInv_neg (σ : M →+ M) (f : M →+ QZ) : dualInv (-σ) f = -dualInv σ f := by
  ext x
  simp

end Neg

section Transfer

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K))
  {n : ℕ} [NeZero n] (hMn : ∀ m : M, n • m = 0) (e : rootsOfUnityModule K L n ≃+ ZMod n)

/-- For `M` killed by `n`, an element of the Cartier dual `Hom(M, Lˣ)` as a homomorphism
`M → μ_n(L)`. -/
def cartierDualRoots : cartierDual K L M →+ (M →+ rootsOfUnityModule K L n) :=
  (uliftIntLinearEquivAddHom M (rootsOfUnityModule K L n)).toAddMonoidHom.comp
    (cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).inv.hom.toLinearMap.toAddMonoidHom

omit [NeZero n] in
/-- `cartierDualRoots` followed by `μ_n(L) → Lˣ` is evaluation. -/
theorem rootsOfUnityToUnits_cartierDualRoots (φ : cartierDual K L M) (m : M) :
    (rootsOfUnityToUnits K L n).hom (cartierDualRoots M hMn φ m) =
      (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m := by
  have h := cartierDualIsoHomRootsOfUnityOfNsmul_hom_apply M n hMn
    ((cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).inv.hom φ) m
  have hi := congrArg (fun f => (f.hom φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).inv_hom_id
  exact h.symm.trans hi

/-- For `M` killed by `n` and an isomorphism `e : μ_n(L) ≅ ℤ/n`, an element of the Cartier dual as
a homomorphism `M → ℚ/ℤ`. -/
def cartierDualToQZ : cartierDual K L M →+ (M →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp e.toAddMonoidHom)).comp (cartierDualRoots M hMn)

omit [NeZero n] in
theorem cartierDualToQZ_apply (φ : cartierDual K L M) (m : M) :
    cartierDualToQZ M hMn e φ m = zmodToQZ n (e (cartierDualRoots M hMn φ m)) :=
  rfl

/-- `cartierDualToQZ φ m` vanishes exactly when `φ m` does. -/
theorem cartierDualToQZ_apply_eq_zero_iff (φ : cartierDual K L M) (m : M) :
    cartierDualToQZ M hMn e φ m = 0 ↔ (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m = 0 := by
  rw [cartierDualToQZ_apply, ← rootsOfUnityToUnits_cartierDualRoots M hMn,
    ← map_zero (zmodToQZ n), (zmodToQZ_injective (n := n)).eq_iff, ← map_zero e,
    e.injective.eq_iff, ← map_zero (rootsOfUnityToUnits K L n).hom,
    (rootsOfUnityToUnits_injective (K := K) (L := L) (n := n)).eq_iff]

theorem cartierDualToQZ_injective : Function.Injective (cartierDualToQZ M hMn e) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  apply LinearMap.ext
  intro m
  exact (cartierDualToQZ_apply_eq_zero_iff M hMn e φ m).1 (DFunLike.congr_fun hφ m)

theorem cartierDualToQZ_surjective : Function.Surjective (cartierDualToQZ M hMn e) := by
  intro f
  have hf : ∀ m, n • f m = 0 := fun m => by rw [← map_nsmul, hMn, map_zero]
  let ψ : M →ₗ[ULift.{u} ℤ] rootsOfUnityModule K L n :=
    (uliftIntLinearEquivAddHom M (rootsOfUnityModule K L n)).symm
      (e.symm.toAddMonoidHom.comp (zmodOfQZ f hf))
  refine ⟨(cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).hom.hom
    (show (Rep.ihom M).obj (rootsOfUnityModule K L n) from ψ), ?_⟩
  ext m
  rw [cartierDualToQZ_apply]
  have hi := congrArg (fun g => (g.hom (show (Rep.ihom M).obj (rootsOfUnityModule K L n) from ψ) :
      M →ₗ[ULift.{u} ℤ] rootsOfUnityModule K L n) m)
    (cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).hom_inv_id
  have h : cartierDualRoots M hMn ((cartierDualIsoHomRootsOfUnityOfNsmul K L M n hMn).hom.hom
      (show (Rep.ihom M).obj (rootsOfUnityModule K L n) from ψ)) m = ψ m := hi
  rw [h]
  change zmodToQZ n (e (e.symm (zmodOfQZ f hf m))) = f m
  rw [e.apply_symm_apply, zmodToQZ_zmodOfQZ]

/-- For `M` killed by `n` and `μ_n(L) ≅ ℤ/n`, the Cartier dual is `Hom(M, ℚ/ℤ)`. -/
def cartierDualEquivQZ : cartierDual K L M ≃+ (M →+ QZ) :=
  AddEquiv.ofBijective (cartierDualToQZ M hMn e)
    ⟨cartierDualToQZ_injective M hMn e, cartierDualToQZ_surjective M hMn e⟩

omit [NeZero n] in
/-- If `c` is an involution acting on the `n`-torsion of `Lˣ` by inversion, `cartierDualToQZ`
carries the action of `c` on the Cartier dual to the dual involution of `c` on `M`. -/
theorem cartierDualToQZ_act {c : Gal(L/K)} (hinv : c⁻¹ = c)
    (hconj : ∀ ζ : unitsModule K L, n • ζ = 0 → (unitsModule K L).ρ c ζ = -ζ)
    (φ : cartierDual K L M) :
    cartierDualToQZ M hMn e ((cartierDual K L M).ρ c φ) =
      dualInv (act M c) (cartierDualToQZ M hMn e φ) := by
  ext m
  rw [dualInv_apply, cartierDualToQZ_apply, cartierDualToQZ_apply, ← map_neg, ← map_neg]
  congr 2
  apply rootsOfUnityToUnits_injective (K := K) (L := L) (n := n)
  rw [map_neg, rootsOfUnityToUnits_cartierDualRoots, rootsOfUnityToUnits_cartierDualRoots,
    cartierDual_ρ_apply, hinv]
  apply hconj
  rw [← map_nsmul, hMn, map_zero]

end Transfer

/-- An element of `ℚ/ℤ` of order two is `1/2`. -/
theorem QZ.eq_mk_half_of_two_nsmul {q : QZ} (hq : 2 • q = 0) (hq0 : q ≠ 0) :
    q = QZ.mk (1 / 2) := by
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div (by norm_num) hq
  rw [hm] at hq0 ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    apply hq0
    rw [mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero]
  · rw [add_nsmul, one_nsmul, mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero, zero_add]
    norm_num

section Congr

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] {c : G} (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

/-- Equal values give equal classes of `cocycleTwo`. -/
theorem cohomologyπ_cocycleTwo_congr (A : Rep.{u} k G) [IsSmoothRep A]
    {a b : A} (ha : A.ρ c a = a) (hb : A.ρ c b = b) (hab : a = b) :
    cohomologyπ A 2 (cocycleTwo A hG hc a ha) = cohomologyπ A 2 (cocycleTwo A hG hc b hb) := by
  subst hab
  rfl

end Congr

section Cup

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DiscreteTopology Gal(L/K)]
  (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [IsSmoothRep M] [Finite M]
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)

/-- The cochain of the cup product of two cocycles under the Cartier pairing. -/
theorem cochainOf_cupCartier {p q : ℕ} (h : p + q = 2) (x : ProfiniteCohomology.cocycles M p)
    (y : ProfiniteCohomology.cocycles (cartierDual K L M) q) (s : Fin 2 → Gal(L/K)) :
    cochainOf _ (cocycleι _ 2 (HomologicalComplex.cyclesMap (coeffCochainsMap (cartierPairing K L M)) 2
        (cupCocycles h x y))) s =
      ((((cartierDual K L M).ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf _ (cocycleι _ q y) fun j : Fin q => s ⟨p + j, by omega⟩)) :
        M →ₗ[ULift.{u} ℤ] unitsModule K L) (cochainOf M (cocycleι M p x) fun i : Fin p => s ⟨i, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, cartierPairing_tmul]

/-- The cup product of the `1`-cocycles of `α` and `β` is the `2`-cocycle supported at `(c, c)` with
value `(c β)(α)`. -/
theorem cupPairing_cocycleOne (α : M) (hα : α + M.ρ c α = 0) (β : cartierDual K L M)
    (hβ : β + (cartierDual K L M).ρ c β = 0) :
    ∃ ht, cupPairing (cartierPairing K L M) (show 1 + 1 = 2 from rfl)
        (cohomologyπ M 1 (cocycleOne M hG hc α hα))
        (cohomologyπ _ 1 (cocycleOne (cartierDual K L M) hG hc β hβ)) =
      cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc
        ((((cartierDual K L M).ρ c β) : M →ₗ[ULift.{u} ℤ] unitsModule K L) α) ht) := by
  set z := HomologicalComplex.cyclesMap (coeffCochainsMap (cartierPairing K L M)) 2
    (cupCocycles (show 1 + 1 = 2 from rfl) (cocycleOne M hG hc α hα)
      (cocycleOne (cartierDual K L M) hG hc β hβ)) with hz
  have hval : ∀ g h : Gal(L/K), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((((cartierDual K L M).ρ g) (cochainOne (cartierDual K L M) β ![h])) :
        M →ₗ[ULift.{u} ℤ] unitsModule K L) (cochainOne M α ![g]) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleOne, cochainOf_cocycleOne]
    have e1 : (fun j : Fin 1 => (![g, h] : Fin 2 → Gal(L/K)) ⟨1 + j, by omega⟩) = ![h] := by
      funext j; fin_cases j; rfl
    have e2 : (fun i : Fin 1 => (![g, h] : Fin 2 → Gal(L/K)) ⟨i, by omega⟩) = ![g] := by
      funext i; fin_cases i; rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(L/K)) ⟨1, by omega⟩ = g := by
      simp [Fin.partialProd]
    rw [e1, e2, e3]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (unitsModule K L) hG hc z
    (fun g => by rw [hval, cochainOne_one, map_zero])
    (fun g => by rw [hval, cochainOne_one, map_zero, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((((cartierDual K L M).ρ c β) : M →ₗ[ULift.{u} ℤ] unitsModule K L) α) := by
    rw [hval, cochainOne_c _ hc, cochainOne_c _ hc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

/-- The cup product of the `2`-cocycle of `a` with a class of `H⁰` of the Cartier dual. -/
theorem cupPairing_cocycleTwo_zero (a : M) (ha : M.ρ c a = a)
    (φ : (cartierDual K L M).ρ.invariants) :
    ∃ ht, cupPairing (cartierPairing K L M) (show 2 + 0 = 2 from rfl)
        (cohomologyπ M 2 (cocycleTwo M hG hc a ha)) ((zeroIso (cartierDual K L M)).inv.hom φ) =
      cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc
        (((φ : cartierDual K L M) : M →ₗ[ULift.{u} ℤ] unitsModule K L) a) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv (cartierDual K L M) φ
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (coeffCochainsMap (cartierPairing K L M)) 2
    (cupCocycles (show 2 + 0 = 2 from rfl) (cocycleTwo M hG hc a ha) z0) with hz
  have hval : ∀ g h : Gal(L/K), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      (((φ : cartierDual K L M) : M →ₗ[ULift.{u} ℤ] unitsModule K L) (cochainTwo M c a ![g, h])) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c, φ.2]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (unitsModule K L) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left M hc, map_zero])
    (fun g => by rw [hval, cochainTwo_one_right M hc, map_zero])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      (((φ : cartierDual K L M) : M →ₗ[ULift.{u} ℤ] unitsModule K L) a) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

/-- The cup product of a class of `H⁰` with the `2`-cocycle of `φ` of the Cartier dual. -/
theorem cupPairing_zero_cocycleTwo (a : M.ρ.invariants) (φ : cartierDual K L M)
    (hφ : (cartierDual K L M).ρ c φ = φ) :
    ∃ ht, cupPairing (cartierPairing K L M) (show 0 + 2 = 2 from rfl)
        ((zeroIso M).inv.hom a) (cohomologyπ _ 2 (cocycleTwo (cartierDual K L M) hG hc φ hφ)) =
      cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc
        ((φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) (a : M)) ht) := by
  obtain ⟨z0, hz0, hz0c⟩ := exists_cocycle_zeroIso_inv M a
  rw [← hz0]
  set z := HomologicalComplex.cyclesMap (coeffCochainsMap (cartierPairing K L M)) 2
    (cupCocycles (show 0 + 2 = 2 from rfl) z0 (cocycleTwo (cartierDual K L M) hG hc φ hφ)) with hz
  have hval : ∀ g h : Gal(L/K), cochainOf _ (cocycleι _ 2 z) ![g, h] =
      ((cochainTwo (cartierDual K L M) c φ ![g, h] : M →ₗ[ULift.{u} ℤ] unitsModule K L) (a : M)) := by
    intro g h
    rw [hz, cochainOf_cupCartier, cochainOf_cocycleTwo, hz0c]
    have e1 : (fun j : Fin 2 => (![g, h] : Fin 2 → Gal(L/K)) ⟨0 + j, by omega⟩) = ![g, h] := by
      funext j; fin_cases j <;> rfl
    have e3 : Fin.partialProd (![g, h] : Fin 2 → Gal(L/K)) ⟨0, by omega⟩ = 1 := by
      simp [Fin.partialProd]
    rw [e1, e3, map_one, Module.End.one_apply]
  obtain ⟨ht, hzt⟩ := exists_eq_cocycleTwo_of_normalized (unitsModule K L) hG hc z
    (fun g => by rw [hval, cochainTwo_one_left _ hc, LinearMap.zero_apply])
    (fun g => by rw [hval, cochainTwo_one_right _ hc, LinearMap.zero_apply])
  have hcc : cochainOf _ (cocycleι _ 2 z) ![c, c] =
      ((φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) (a : M)) := by
    rw [hval, cochainTwo_cc]
  refine ⟨hcc ▸ ht, ?_⟩
  rw [cupPairing_cohomologyπ, ← hz]
  exact (congrArg (cohomologyπ _ 2).hom hzt).trans (cohomologyπ_cocycleTwo_congr hG hc _ _ _ hcc)

end Cup

section Pairing

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DiscreteTopology Gal(L/K)]
  (inv : cohomology (unitsModule K L) 2 →+ QZ)

/-- The pairing `H^r(M) × H^s(M') → ℚ/ℤ`, `r + s = 2`, `M' = Hom(M, Lˣ)`: the cup product with the
Cartier pairing followed by `inv`. -/
def orderTwoDualityPairing (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [IsSmoothRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) : cohomology M r →+ cohomology (cartierDual K L M) s →+ QZ :=
  (AddMonoidHom.compHom inv).comp (bilinAddHom (cupPairing (cartierPairing K L M) h))

theorem orderTwoDualityPairing_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [IsSmoothRep M]
    [Finite M] {r s : ℕ} (h : r + s = 2) (x : cohomology M r)
    (y : cohomology (cartierDual K L M) s) :
    orderTwoDualityPairing inv M h x y = inv (cupPairing (cartierPairing K L M) h x y) :=
  rfl

end Pairing

section Invariant

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DiscreteTopology Gal(L/K)]
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)
  (inv : cohomology (unitsModule K L) 2 →+ QZ)
  (hinv : ∀ (t : unitsModule K L) (ht : (unitsModule K L).ρ c t = t), 2 • t = 0 → t ≠ 0 →
    inv (cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc t ht)) = QZ.mk (1 / 2))

include hinv in
/-- The value of `inv` on the class of `cocycleTwo t` for `t` of order at most two: any `q` of order
at most two that vanishes exactly when `t` does. -/
theorem inv_cocycleTwo_eq (t : unitsModule K L) (ht : (unitsModule K L).ρ c t = t)
    (h2t : 2 • t = 0) (q : QZ) (hq : 2 • q = 0) (hqt : q = 0 ↔ t = 0) :
    inv (cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc t ht)) = q := by
  by_cases ht0 : t = 0
  · have hz : cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc t ht) = 0 := by
      rw [cohomologyπ_cocycleTwo_eq_zero_iff]
      exact ⟨0, by rw [ht0, map_zero, add_zero]⟩
    rw [hz, map_zero, hqt.2 ht0]
  · rw [QZ.eq_mk_half_of_two_nsmul hq (fun h => ht0 (hqt.1 h))]
    exact hinv t ht h2t ht0

include hinv in
theorem inv_cocycleTwo_eq_cartierDualToQZ (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) {n : ℕ} [NeZero n]
    (hMn : ∀ m : M, n • m = 0) (e : rootsOfUnityModule K L n ≃+ ZMod n) (φ : cartierDual K L M)
    (m : M) (hq : 2 • cartierDualToQZ M hMn e φ m = 0) (t : unitsModule K L)
    (htφ : t = (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m ∨
      t = -(φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m)
    (ht : (unitsModule K L).ρ c t = t) :
    inv (cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc t ht)) =
      cartierDualToQZ M hMn e φ m := by
  have h2φ : 2 • (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m = 0 := by
    rw [← map_nsmul, ← cartierDualToQZ_apply_eq_zero_iff M hMn e, map_nsmul]
    exact hq
  have ht0 : t = 0 ↔ (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) m = 0 := by
    rcases htφ with rfl | rfl
    · rfl
    · exact neg_eq_zero
  refine inv_cocycleTwo_eq hG hc inv hinv t ht ?_ _ hq ?_
  · rcases htφ with rfl | rfl
    · exact h2φ
    · rw [two_nsmul] at h2φ ⊢
      rw [← neg_add, h2φ, neg_zero]
  · rw [ht0]
    exact cartierDualToQZ_apply_eq_zero_iff M hMn e φ m

end Invariant

section Generic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DiscreteTopology Gal(L/K)]
  [Fintype Gal(L/K)] (inv : cohomology (unitsModule K L) 2 →+ QZ)
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [IsSmoothRep M] [Finite M]

include hG hc in
theorem orderTwoDualityPairing_two_zero_eq_zero (x : cohomology M 2)
    (y : cohomology (cartierDual K L M) 0) (hy : y ∈ normClasses (cartierDual K L M)) :
    orderTwoDualityPairing inv M (show 2 + 0 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ y).1 hy
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective M 2 x
  obtain ⟨a, ha, e⟩ := exists_cohomologyπ_eq_cocycleTwo M hG hc z
  rw [e, orderTwoDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_zero M hG hc a ha ⟨_, hb⟩
  rw [hcup]
  convert map_zero inv
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(b : M →ₗ[ULift.{u} ℤ] unitsModule K L) a, ?_⟩
  change ((((cartierDual K L M).ρ.norm b) : M →ₗ[ULift.{u} ℤ] unitsModule K L) a) = _
  rw [norm_apply _ hG hc, LinearMap.add_apply, cartierDual_ρ_apply, inv_eq_self hG hc, ha]

include hG hc in
theorem orderTwoDualityPairing_zero_two_eq_zero (x : cohomology M 0) (hx : x ∈ normClasses M)
    (y : cohomology (cartierDual K L M) 2) :
    orderTwoDualityPairing inv M (show 0 + 2 = 2 from rfl) x y = 0 := by
  obtain ⟨b, hb, rfl⟩ := (mem_normClasses_iff _ x).1 hx
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 y
  obtain ⟨φ, hφ, e⟩ := exists_cohomologyπ_eq_cocycleTwo _ hG hc z
  rw [e, orderTwoDualityPairing_apply]
  obtain ⟨ht, hcup⟩ := cupPairing_zero_cocycleTwo M hG hc ⟨_, hb⟩ φ hφ
  rw [hcup]
  convert map_zero inv
  rw [cohomologyπ_cocycleTwo_eq_zero_iff]
  refine ⟨(φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) b, ?_⟩
  have hφb : (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) (M.ρ c b) =
      (unitsModule K L).ρ c ((φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) b) := by
    conv_lhs => rw [← hφ]
    rw [cartierDual_ρ_apply, inv_eq_self hG hc, ← Module.End.mul_apply, ← map_mul,
      mul_self_eq_one hG hc, map_one, Module.End.one_apply]
  change (φ : M →ₗ[ULift.{u} ℤ] unitsModule K L) (M.ρ.norm b) = _
  rw [norm_apply _ hG hc, map_add, hφb]

/-- The pairing `H²(M) × Ĥ⁰(M') → ℚ/ℤ`. -/
def orderTwoDualityPairingTwoZero :
    cohomology M 2 →+ cohomologyTateZero (cartierDual K L M) →+ QZ where
  toFun x := QuotientAddGroup.lift (normClasses (cartierDual K L M)).toAddSubgroup
    (orderTwoDualityPairing inv M (show 2 + 0 = 2 from rfl) x)
    (fun y hy => orderTwoDualityPairing_two_zero_eq_zero inv hG hc M x y hy)
  map_zero' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun (map_zero (orderTwoDualityPairing inv M (show 2 + 0 = 2 from rfl))) y
  map_add' x x' := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact DFunLike.congr_fun
      (map_add (orderTwoDualityPairing inv M (show 2 + 0 = 2 from rfl)) x x') y

theorem orderTwoDualityPairingTwoZero_mk (x : cohomology M 2)
    (y : cohomology (cartierDual K L M) 0) :
    orderTwoDualityPairingTwoZero inv hG hc M x (Submodule.Quotient.mk y) =
      orderTwoDualityPairing inv M (show 2 + 0 = 2 from rfl) x y :=
  rfl

/-- The pairing `Ĥ⁰(M) × H²(M') → ℚ/ℤ`. -/
def orderTwoDualityPairingZeroTwo :
    cohomologyTateZero M →+ cohomology (cartierDual K L M) 2 →+ QZ :=
  QuotientAddGroup.lift (normClasses M).toAddSubgroup
    (orderTwoDualityPairing inv M (show 0 + 2 = 2 from rfl))
    (fun x hx => by
      ext y
      exact orderTwoDualityPairing_zero_two_eq_zero inv hG hc M x hx y)

theorem orderTwoDualityPairingZeroTwo_mk (x : cohomology M 0)
    (y : cohomology (cartierDual K L M) 2) :
    orderTwoDualityPairingZeroTwo inv hG hc M (Submodule.Quotient.mk x) y =
      orderTwoDualityPairing inv M (show 0 + 2 = 2 from rfl) x y :=
  rfl

end Generic

section Duality

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DiscreteTopology Gal(L/K)]
  [Fintype Gal(L/K)] (inv : cohomology (unitsModule K L) 2 →+ QZ)
  {c : Gal(L/K)} (hG : ∀ g : Gal(L/K), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hinv : ∀ (t : unitsModule K L) (ht : (unitsModule K L).ρ c t = t), 2 • t = 0 → t ≠ 0 →
    inv (cohomologyπ _ 2 (cocycleTwo (unitsModule K L) hG hc t ht)) = QZ.mk (1 / 2))
  (hconj : ∀ ζ : unitsModule K L, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (unitsModule K L).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (rootsOfUnityModule K L k ≃+ ZMod k))
  (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) [IsSmoothRep M] [Finite M]

include hinv hconj hroots in
theorem orderTwoDualityPairingTwoZero_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomology M 2)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomologyTateZero (cartierDual K L M)),
      ∀ x y, orderTwoDualityPairingTwoZero inv hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual K L M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc)
      (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual K L M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual K L M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨h2EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he0).trans
    (cohomZeroEquivContinuous (cartierDual K L M) hG hc), fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk,
    orderTwoDualityPairingTwoZero_mk, orderTwoDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleTwo_zero M hG hc (a : M) ((mem_fixedSub_act M).1 a.2)
    ⟨_, mem_invariants_of_fixed (cartierDual K L M) hG
      ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)⟩
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e (T.symm f) = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e (T.symm f) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (inv_cocycleTwo_eq_cartierDualToQZ hG hc inv hinv M hMn e (T.symm f) a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]

include hinv hconj hroots in
theorem orderTwoDualityPairingZeroTwo_eq_tatePair :
    ∃ (e : tateQuot (act M c) ≃+ cohomologyTateZero M)
      (e' : tateQuot (dualInv (act M c)) ≃+ cohomology (cartierDual K L M) 2),
      ∀ x y, orderTwoDualityPairingZeroTwo inv hG hc M (e x) (e' y) = tatePair (act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual K L M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc)
      (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he0 : ∀ f, T.symm (dualInv (act M c) f) = act (cartierDual K L M) c (T.symm f) := fun f => by
    apply T.injective
    rw [T.apply_symm_apply]
    change _ = T ((cartierDual K L M).ρ c (T.symm f))
    rw [hact, T.apply_symm_apply]
  refine ⟨cohomZeroEquivContinuous M hG hc, (tateQuotCongr T.symm he0).trans
    (h2EquivOfOrderTwo (cartierDual K L M) hG hc), fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h2Equiv_mk, h0Equiv_mk,
    orderTwoDualityPairingZeroTwo_mk, orderTwoDualityPairing_apply, tatePair_mk]
  obtain ⟨ht, hcup⟩ := cupPairing_zero_cocycleTwo M hG hc
    ⟨_, mem_invariants_of_fixed M hG ((mem_fixedSub_act M).1 a.2)⟩
    ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual K L M)
    ((mem_fixedSub_act _).1 (fixedSubCongr T.symm he0 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e
      ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual K L M) = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e
      ((fixedSubCongr T.symm he0 f : fixedSub _) : cartierDual K L M) a = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (act M c) a f
  refine (inv_cocycleTwo_eq_cartierDualToQZ hG hc inv hinv M hMn e _ a hq _
    (Or.inl rfl) ht).trans ?_
  rw [hTf]

omit [Fintype Gal(L/K)] in
include hinv hconj hroots in
theorem orderTwoDualityPairing_one_eq_tatePair :
    ∃ (e : tateQuot (-act M c) ≃+ cohomology M 1)
      (e' : tateQuot (dualInv (-act M c)) ≃+ cohomology (cartierDual K L M) 1),
      ∀ x y, orderTwoDualityPairing inv M (show 1 + 1 = 2 from rfl) (e x) (e' y) =
        tatePair (-act M c) x y := by
  have : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  have hMn : ∀ m : M, Nat.card M • m = 0 := fun m => card_nsmul_eq_zero'
  obtain ⟨e⟩ := hroots (Nat.card M) Nat.card_pos
  set T := cartierDualEquivQZ M hMn e with hT
  have hact : ∀ φ, T ((cartierDual K L M).ρ c φ) = dualInv (act M c) (T φ) := fun φ =>
    cartierDualToQZ_act M hMn e (OrderTwo.inv_eq_self hG hc)
      (fun ζ hζ => hconj ζ ⟨_, Nat.card_pos, hζ⟩) φ
  have he1 : ∀ f, T.symm (dualInv (-act M c) f) = (-act (cartierDual K L M) c) (T.symm f) :=
    fun f => by
      apply T.injective
      rw [T.apply_symm_apply, AddMonoidHom.neg_apply, map_neg, Involution.dualInv_neg]
      change _ = -T ((cartierDual K L M).ρ c (T.symm f))
      rw [hact, T.apply_symm_apply]
  refine ⟨h1EquivOfOrderTwo M hG hc, (tateQuotCongr T.symm he1).trans
    (h1EquivOfOrderTwo (cartierDual K L M) hG hc), fun x y => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddEquiv.trans_apply, tateQuotCongr_mk, h1Equiv_mk, h1Equiv_mk,
    orderTwoDualityPairing_apply, tatePair_mk]
  set β : cartierDual K L M := ((fixedSubCongr T.symm he1 f : fixedSub _) : cartierDual K L M)
    with hβdef
  obtain ⟨ht, hcup⟩ := cupPairing_cocycleOne M hG hc (α : M) ((mem_fixedSub_neg_act M).1 α.2)
    β ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  rw [hcup]
  have hTf : cartierDualToQZ M hMn e β = f := T.apply_symm_apply f
  have hq : 2 • cartierDualToQZ M hMn e β α = 0 := by
    rw [hTf]
    exact two_nsmul_fixedPair (-act M c) α f
  have hβ : (cartierDual K L M).ρ c β = -β :=
    eq_neg_of_add_eq_zero_right ((mem_fixedSub_neg_act _).1 (fixedSubCongr T.symm he1 f).2)
  refine (inv_cocycleTwo_eq_cartierDualToQZ hG hc inv hinv M hMn e β α hq _
    (Or.inr (by rw [hβ]; rfl)) ht).trans ?_
  rw [hTf]

include hinv hconj hroots in
/-- Local duality for a Galois group of order two: the three pairings `Ĥ⁰ × H²`, `H¹ × H¹` and
`H² × Ĥ⁰` with values in `ℚ/ℤ` are perfect. -/
theorem orderTwoLocalDuality :
    (Function.Bijective (orderTwoDualityPairingZeroTwo inv hG hc M) ∧
      Function.Bijective (orderTwoDualityPairingZeroTwo inv hG hc M).flip) ∧
    (Function.Bijective (orderTwoDualityPairing inv M (show 1 + 1 = 2 from rfl)) ∧
      Function.Bijective (orderTwoDualityPairing inv M (show 1 + 1 = 2 from rfl)).flip) ∧
    (Function.Bijective (orderTwoDualityPairingTwoZero inv hG hc M) ∧
      Function.Bijective (orderTwoDualityPairingTwoZero inv hG hc M).flip) := by
  obtain ⟨e₀, e₀', h₀⟩ := orderTwoDualityPairingZeroTwo_eq_tatePair inv hG hc hinv hconj hroots M
  obtain ⟨e₁, e₁', h₁⟩ := orderTwoDualityPairing_one_eq_tatePair inv hG hc hinv hconj hroots M
  obtain ⟨e₂, e₂', h₂⟩ := orderTwoDualityPairingTwoZero_eq_tatePair inv hG hc hinv hconj hroots M
  exact ⟨⟨bijective_of_pairing_eq_addEquiv _ _ e₀ e₀' (AddEquiv.refl QZ) h₀ tatePair_bijective,
      bijective_flip_of_pairing_eq_addEquiv _ _ e₀ e₀' (AddEquiv.refl QZ) h₀
        tatePair_flip_bijective⟩,
    ⟨bijective_of_pairing_eq_addEquiv _ _ e₁ e₁' (AddEquiv.refl QZ) h₁ tatePair_bijective,
      bijective_flip_of_pairing_eq_addEquiv _ _ e₁ e₁' (AddEquiv.refl QZ) h₁
        tatePair_flip_bijective⟩,
    ⟨bijective_of_pairing_eq_addEquiv _ _ e₂ e₂' (AddEquiv.refl QZ) h₂ tatePair_bijective,
      bijective_flip_of_pairing_eq_addEquiv _ _ e₂ e₂' (AddEquiv.refl QZ) h₂
        tatePair_flip_bijective⟩⟩

end Duality

section RealPlace

open NumberField

variable {K : Type u} [Field K] [NumberField K] (w : InfinitePlace K)

/-- The invariant `H²(Gal(K̄_w/K_w), K̄_wˣ) → ℚ/ℤ` at an infinite place (`realInvariantHom`) with
values in `QZ`. -/
def realInvariantQZ : RealBrauerGroup w →+ QZ :=
  QZ.toRationalModIntegers.symm.toAddMonoidHom.comp (realInvariantHom w)

/-- At a real place, the conjugation inverts the roots of unity of `K̄_w`. -/
theorem closureConj_apply_of_pow_eq_one (hw : w.IsReal) (ζ : (AlgebraicClosure w.Completion)ˣ)
    {k : ℕ} (hk : 0 < k) (hζ : ζ ^ k = 1) :
    closureConj w hw (ζ : AlgebraicClosure w.Completion) =
      ((ζ⁻¹ : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion) := by
  apply (closureToComplex w).injective
  rw [closureToComplex_closureConj, Units.val_inv_eq_inv_val, map_inv₀]
  have hz : (closureToComplex w (ζ : AlgebraicClosure w.Completion)) ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, map_one]
  have hn : ‖closureToComplex w (ζ : AlgebraicClosure w.Completion)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hz hk.ne'
  have hmul : closureToComplex w (ζ : AlgebraicClosure w.Completion) *
      (starRingEnd ℂ) (closureToComplex w (ζ : AlgebraicClosure w.Completion)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  exact eq_inv_of_mul_eq_one_right hmul

/-- At a real place, the conjugation acts on the torsion of `K̄_wˣ` by inversion. -/
theorem closureConj_unitsModule_of_torsion (hw : w.IsReal)
    (ζ : unitsModule w.Completion (AlgebraicClosure w.Completion))
    (hζ : ∃ k : ℕ, 0 < k ∧ k • ζ = 0) :
    (unitsModule w.Completion (AlgebraicClosure w.Completion)).ρ (closureConj w hw) ζ = -ζ := by
  obtain ⟨k, hk, hkζ⟩ := hζ
  apply Additive.toMul.injective
  apply Units.ext
  have hpow : (Additive.toMul ζ : (AlgebraicClosure w.Completion)ˣ) ^ k = 1 :=
    congrArg (Additive.toMul (α := (AlgebraicClosure w.Completion)ˣ)) hkζ
  exact closureConj_apply_of_pow_eq_one w hw _ hk hpow

/-- The roots of unity of order dividing `k > 0` in `K̄_w` form a group isomorphic to `ℤ/k`. -/
theorem nonempty_rootsOfUnityModule_addEquiv_zmod (k : ℕ) (hk : 0 < k) :
    Nonempty (rootsOfUnityModule w.Completion (AlgebraicClosure w.Completion) k ≃+ ZMod k) := by
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero (k : w.Completion) := ⟨Nat.cast_ne_zero.2 hk.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure w.Completion) k
  have hcard : Nat.card (rootsOfUnity k (AlgebraicClosure w.Completion)) = k :=
    hζ.card_rootsOfUnity
  have : IsAddCyclic (Additive (rootsOfUnity k (AlgebraicClosure w.Completion))) :=
    isAddCyclic_additive_iff.2 inferInstance
  exact ⟨addEquivOfAddCyclicCardEq (G := Additive (rootsOfUnity k (AlgebraicClosure w.Completion)))
    (G' := ZMod k) (by rw [Nat.card_zmod]; exact (Nat.card_congr Additive.ofMul.symm).trans hcard)⟩

/-- At a real place, the invariant of the class of the `2`-cocycle supported at `(c, c)` with value
`t ≠ 1`, `t² = 1`, is `1/2`: `t = −1` is not a norm `m · c(m)`. -/
theorem realInvariantQZ_cocycleTwo (hw : w.IsReal)
    (t : unitsModule w.Completion (AlgebraicClosure w.Completion))
    (ht : (unitsModule w.Completion (AlgebraicClosure w.Completion)).ρ (closureConj w hw) t = t)
    (h2t : 2 • t = 0) (ht0 : t ≠ 0) :
    realInvariantQZ w (cohomologyπ _ 2 (cocycleTwo _ (eq_one_or_eq_closureConj w hw)
      (closureConj_ne_one w hw) t ht)) = QZ.mk (1 / 2) := by
  have hu : ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) :
      AlgebraicClosure w.Completion) = -1 := by
    have hsq : ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) :
        AlgebraicClosure w.Completion) * (Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) = 1 := by
      have h2 : (Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) *
            (Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) = 1 :=
        congrArg (Additive.toMul (α := (AlgebraicClosure w.Completion)ˣ))
          ((two_nsmul t).symm.trans h2t)
      rw [← Units.val_mul, h2, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (Additive.toMul.injective (Units.ext (h.trans Units.val_one.symm))) ht0
    · exact h
  have hfix : closureConj w hw ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) :
      AlgebraicClosure w.Completion) = (Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) := by
    rw [hu, map_neg, map_one]
  have hy : cohomologyπ _ 2 (cocycleTwo _ (eq_one_or_eq_closureConj w hw)
      (closureConj_ne_one w hw) t ht) ≠ 0 := by
    rw [Ne, cohomologyπ_cocycleTwo_eq_zero_iff]
    rintro ⟨m, hm⟩
    have hpos := (exists_mul_closureConj_iff w hw (Additive.toMul t) hfix).1
      ⟨Additive.toMul m, congrArg (fun s : unitsModule w.Completion (AlgebraicClosure w.Completion) =>
        ((Additive.toMul s : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) hm⟩
    rw [hu, map_neg, map_one] at hpos
    norm_num at hpos
  change QZ.toRationalModIntegers.symm (realInvariant w _) = _
  unfold realInvariant
  split_ifs with h
  · exact absurd h hy
  · rfl

variable [Fintype Gal(AlgebraicClosure w.Completion/w.Completion)]

/-- **Local duality at a real place.** For a finite discrete module `M` of `Gal(K̄_w/K_w)` with
Cartier dual `M' = Hom(M, K̄_wˣ)`, the cup product followed by the real invariant gives perfect
pairings `Ĥ⁰(M) × H²(M') → ℚ/ℤ`, `H¹(M) × H¹(M') → ℚ/ℤ` and `H²(M) × Ĥ⁰(M') → ℚ/ℤ`. -/
theorem realLocalDuality (hw : w.IsReal)
    (M : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion)) [IsSmoothRep M]
    [Finite M] :
    (Function.Bijective (orderTwoDualityPairingZeroTwo (realInvariantQZ w)
        (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw) M) ∧
      Function.Bijective (orderTwoDualityPairingZeroTwo (realInvariantQZ w)
        (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw) M).flip) ∧
    (Function.Bijective (orderTwoDualityPairing (realInvariantQZ w) M (show 1 + 1 = 2 from rfl)) ∧
      Function.Bijective
        (orderTwoDualityPairing (realInvariantQZ w) M (show 1 + 1 = 2 from rfl)).flip) ∧
    (Function.Bijective (orderTwoDualityPairingTwoZero (realInvariantQZ w)
        (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw) M) ∧
      Function.Bijective (orderTwoDualityPairingTwoZero (realInvariantQZ w)
        (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw) M).flip) :=
  orderTwoLocalDuality (realInvariantQZ w) (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)
    (realInvariantQZ_cocycleTwo w hw) (closureConj_unitsModule_of_torsion w hw)
    (nonempty_rootsOfUnityModule_addEquiv_zmod w) M

end RealPlace

end Langlands.GaloisCohomology
