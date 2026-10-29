import Langlands.Representation.Induction.PermutationInvariants
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.GroupTheory.PGroup
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Restriction of equivariant maps to invariants

Let `K` be a normal subgroup of a group `G`, `ρ` a representation of `G` over a commutative ring
`R` and `σ` a representation of `G ⧸ K`. A `G`-equivariant map from `ρ` to the inflation
`σ.comp (QuotientGroup.mk' K)` is the same as a `G ⧸ K`-equivariant map from the
`K`-coinvariants of `ρ` (`homCoinvariantsEquiv`). Restricting it to the `K`-invariants of `ρ`
(`invariantsRestriction`) is this map on coinvariants composed with the map
`invariantsToCoinvariants` from invariants to coinvariants (`invariantsRestriction_eq_comp`). So
if `invariantsToCoinvariants` is bijective, restriction to `K`-invariants is a linear
equivalence (`invariantsRestrictionEquiv`).

For subgroups `H ≤ K`, the `K`-coinvariants of the permutation representation on `G ⧸ H` are the
permutation representation of `G ⧸ K` on itself (`permutationCoinvariantsEquiv`), with no
finiteness hypothesis. The fibres of `G ⧸ H → G ⧸ K` have as cardinality (`Nat.card`) the index
of `H` in `K` (`card_quotientMapOfLE_fiber`). If this index is finite, then under the
identifications of invariants (the published `permutationInvariantsLinearEquiv`) and
coinvariants with functions on `G ⧸ K`, `invariantsToCoinvariants` is multiplication by the index
(`permutationCoinvariantsLinearEquiv_invariantsToCoinvariants`), hence bijective when the index
is a unit of `R` (`bijective_invariantsToCoinvariants_permutation`). If `K` is compact and its
quotients by open normal subgroups are `p`-groups (the fields `compactSpace` and `isPGroup` of the
published `Langlands.Cohomology.IsProPSubgroup`) and `H` is open, this index is a power of `p`
(`exists_index_subgroupOf_eq_pow`), so it is a unit when `p` is (`isUnit_index_subgroupOf`).

For `H` open, the published compact induction of a trivial representation from `H` is the
permutation representation on `G ⧸ H` (`Langlands.Induction.permutationEquiv`), and the results
transfer to it (`compactInducedCoinvariantsEquiv`,
`bijective_invariantsToCoinvariants_compactInduced`, `compactInducedInvariantsRestrictionEquiv`).

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312: "We may replace `C^j_m(ẽ)` by
`C^j_m(ẽ)^{H_p}` in (4.10.2)", where (4.10.2), printed p.311, is a sum of the modules
`Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`. Our reading of this step is that the
target is a representation of `S(ẽ) ⧸ H_p`, so the `Hom` only sees the `H_p`-coinvariants of
`C^j_m(ẽ)`, and the `H_p`-invariants may replace them because the indices involved are powers of
`p`, invertible in `𝒪/ℓ^m𝒪`. This module proves that algebraic mechanism under the explicit
hypotheses above. It does not treat Harris's modules `C^j_m(ẽ)`, which are direct limits of free
modules, or direct limits at all; the definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uM uI uV uW uX uY

section Fibres

variable {G : Type uG} [Group G] {H K : Subgroup G} (hHK : H ≤ K)

/-- The fibre of `G ⧸ H → G ⧸ K` over `q` is in bijection with `K ⧸ (H.subgroupOf K)`, through
the second component of Mathlib's `Subgroup.quotientEquivProdOfLE`. -/
def quotientMapOfLEFiberEquiv (q : G ⧸ K) :
    (Subgroup.quotientMapOfLE hHK ⁻¹' {q}) ≃ K ⧸ H.subgroupOf K where
  toFun x := (Subgroup.quotientEquivProdOfLE hHK x.1).2
  invFun b := ⟨(Subgroup.quotientEquivProdOfLE hHK).symm (q, b),
    congrArg Prod.fst ((Subgroup.quotientEquivProdOfLE hHK).apply_symm_apply (q, b))⟩
  left_inv x := Subtype.ext <| by
    change (Subgroup.quotientEquivProdOfLE hHK).symm (q, _) = x.1
    have h : ((Subgroup.quotientEquivProdOfLE hHK x.1).1 : G ⧸ K) = q := x.2
    exact (congrArg (Subgroup.quotientEquivProdOfLE hHK).symm
      (Prod.ext h.symm rfl : (q, (Subgroup.quotientEquivProdOfLE hHK x.1).2) =
        Subgroup.quotientEquivProdOfLE hHK x.1)).trans
      ((Subgroup.quotientEquivProdOfLE hHK).symm_apply_apply x.1)
  right_inv b := congrArg Prod.snd ((Subgroup.quotientEquivProdOfLE hHK).apply_symm_apply (q, b))

/-- Every fibre of `G ⧸ H → G ⧸ K` has cardinality the index of `H` in `K`. -/
theorem card_quotientMapOfLE_fiber (q : G ⧸ K) :
    Nat.card (Subgroup.quotientMapOfLE hHK ⁻¹' {q}) = (H.subgroupOf K).index :=
  Nat.card_congr (quotientMapOfLEFiberEquiv hHK q)

variable [K.Normal]

/-- For `K` normal, `G ⧸ H → G ⧸ K` is constant on the orbits of `K`. -/
theorem quotientMapOfLE_smul_of_mem (k : K) (x : G ⧸ H) :
    Subgroup.quotientMapOfLE hHK ((k : G) • x) = Subgroup.quotientMapOfLE hHK x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, Subgroup.quotientMapOfLE_apply_mk,
    Subgroup.quotientMapOfLE_apply_mk]
  refine QuotientGroup.eq.mpr ?_
  rw [mul_inv_rev]
  exact ‹K.Normal›.conj_mem' _ (K.inv_mem k.2) g

/-- `G ⧸ H → G ⧸ K` is `G`-equivariant: `g ∈ G` acts on the group `G ⧸ K` by left
multiplication by its class. -/
theorem quotientMapOfLE_smul (g : G) (x : G ⧸ H) :
    Subgroup.quotientMapOfLE hHK (g • x) =
      (QuotientGroup.mk g : G ⧸ K) • Subgroup.quotientMapOfLE hHK x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

end Fibres

section Coinvariants

variable {R : Type uR} {G : Type uG} {M : Type uM}
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M]
variable {H K : Subgroup G} (hHK : H ≤ K) [K.Normal]

variable (R M)

/-- The pushforward of finitely supported functions along `G ⧸ H → G ⧸ K`, which is invariant
under `K` and hence defined on the `K`-coinvariants of the permutation representation. -/
def permutationCoinvariantsToQuotient :
    Representation.Coinvariants ((permutation R G (G ⧸ H) M).comp K.subtype) →ₗ[R]
      (G ⧸ K →₀ M) :=
  Representation.Coinvariants.lift _ (Finsupp.lmapDomain M R (Subgroup.quotientMapOfLE hHK))
    fun k => Finsupp.lhom_ext fun x m => by
      change Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK)
          (permutation R G (G ⧸ H) M (k : G) (Finsupp.single x m)) =
        Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK) (Finsupp.single x m)
      rw [permutation_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
        quotientMapOfLE_smul_of_mem]

/-- A finitely supported function `ψ` on `G ⧸ K` as the class in the `K`-coinvariants of the
function on `G ⧸ H` with value `ψ q` at `q.out H` for each `q`, where `q.out` is the
representative of `q` chosen by `Quotient.out`. -/
def quotientToPermutationCoinvariants :
    (G ⧸ K →₀ M) →ₗ[R]
      Representation.Coinvariants ((permutation R G (G ⧸ H) M).comp K.subtype) :=
  Representation.Coinvariants.mk _ ∘ₗ
    Finsupp.lmapDomain M R (fun q : G ⧸ K => (QuotientGroup.mk q.out : G ⧸ H))

variable {R M}

/-- On the class of `φ`, `permutationCoinvariantsToQuotient` is the pushforward of `φ`. -/
theorem permutationCoinvariantsToQuotient_mk (φ : G ⧸ H →₀ M) :
    permutationCoinvariantsToQuotient R M hHK (Representation.Coinvariants.mk _ φ) =
      Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK) φ :=
  rfl

/-- The `K`-coinvariants of the permutation representation on `G ⧸ H` are the finitely
supported functions on `G ⧸ K`. -/
def permutationCoinvariantsLinearEquiv :
    Representation.Coinvariants ((permutation R G (G ⧸ H) M).comp K.subtype) ≃ₗ[R]
      (G ⧸ K →₀ M) where
  __ := permutationCoinvariantsToQuotient R M hHK
  invFun := quotientToPermutationCoinvariants R M
  left_inv c := by
    induction c using Representation.Coinvariants.induction_on with
    | h φ =>
      induction φ using Finsupp.induction_linear with
      | zero => simp
      | add φ ψ hφ hψ =>
        change quotientToPermutationCoinvariants R M
            (permutationCoinvariantsToQuotient R M hHK (Representation.Coinvariants.mk _ φ +
              Representation.Coinvariants.mk _ ψ)) = _
        rw [map_add, map_add]
        exact (congrArg₂ (· + ·) hφ hψ).trans (map_add _ φ ψ).symm
      | single x m =>
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
        change Representation.Coinvariants.mk _ (Finsupp.mapDomain _
          (Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK)
            (Finsupp.single (QuotientGroup.mk g : G ⧸ H) m))) = _
        rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Subgroup.quotientMapOfLE_apply_mk,
          hk]
        have hc : g * (k : G) * g⁻¹ ∈ K := ‹K.Normal›.conj_mem _ k.2 g
        have h : Finsupp.single (QuotientGroup.mk (g * (k : G)) : G ⧸ H) m =
            ((permutation R G (G ⧸ H) M).comp K.subtype) ⟨g * (k : G) * g⁻¹, hc⟩
              (Finsupp.single (QuotientGroup.mk g) m) := by
          change _ = permutation R G (G ⧸ H) M (g * (k : G) * g⁻¹) _
          rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]
        rw [h, Representation.Coinvariants.mk_self_apply]
  right_inv ψ := by
    change Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK)
      (Finsupp.mapDomain (fun q : G ⧸ K => (QuotientGroup.mk q.out : G ⧸ H)) ψ) = ψ
    rw [← Finsupp.mapDomain_comp]
    have h : (Subgroup.quotientMapOfLE hHK ∘ fun q : G ⧸ K => (QuotientGroup.mk q.out : G ⧸ H)) =
        id := funext fun q => QuotientGroup.out_eq' q
    rw [h, Finsupp.mapDomain_id]

variable (R M)

/-- The `K`-coinvariants of the permutation representation on `G ⧸ H`, as a representation of
`G ⧸ K`, are the permutation representation of `G ⧸ K` on itself with coefficients `M`. -/
def permutationCoinvariantsEquiv :
    ((permutation R G (G ⧸ H) M).quotientToCoinvariants K).Equiv
      (permutation R (G ⧸ K) (G ⧸ K) M) :=
  .mk (permutationCoinvariantsLinearEquiv hHK) fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine Representation.Coinvariants.hom_ext (Finsupp.lhom_ext fun x m => ?_)
    change Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK)
        (permutation R G (G ⧸ H) M g (Finsupp.single x m)) =
      permutation R (G ⧸ K) (G ⧸ K) M (QuotientGroup.mk g)
        (Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK) (Finsupp.single x m))
    rw [permutation_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single, permutation_single,
      quotientMapOfLE_smul]

variable (I : Type uI)

/-- With coefficients `I →₀ R`, the `K`-coinvariants of the permutation representation on
`G ⧸ H` are the free `R[G ⧸ K]`-module of rank `I`. -/
def permutationCoinvariantsFreeEquiv :
    ((permutation R G (G ⧸ H) (I →₀ R)).quotientToCoinvariants K).Equiv
      (Representation.free R (G ⧸ K) I) :=
  (permutationCoinvariantsEquiv R (I →₀ R) hHK).trans
    (permutationFinsuppEquiv R (G ⧸ K) (G ⧸ K) I)

end Coinvariants

section InvariantsToCoinvariants

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable (ρ : Representation R G V) (K : Subgroup G) [K.Normal]

/-- The map from the `K`-invariants to the `K`-coinvariants of a representation of `G`: the
inclusion followed by the projection, as a map of representations of `G ⧸ K`. -/
def invariantsToCoinvariants :
    (ρ.quotientToInvariants K).IntertwiningMap (ρ.quotientToCoinvariants K) where
  toLinearMap := Representation.Coinvariants.mk _ ∘ₗ
    (Representation.invariants (ρ.comp K.subtype)).subtype
  isIntertwining' q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

/-- `invariantsToCoinvariants` sends an invariant vector to its class. -/
theorem invariantsToCoinvariants_apply (v : Representation.invariants (ρ.comp K.subtype)) :
    invariantsToCoinvariants ρ K v = Representation.Coinvariants.mk _ v.1 :=
  rfl

variable {ρ}
variable {σ : Representation R G W}

/-- An equivalence of representations of `G` induces an equivalence of the `K`-coinvariants as
representations of `G ⧸ K`. -/
def coinvariantsEquivOfEquiv (e : ρ.Equiv σ) :
    (ρ.quotientToCoinvariants K).Equiv (σ.quotientToCoinvariants K) :=
  .mk
    { toFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _ ∘ₗ
          e.toLinearMap) fun k => LinearMap.ext fun v => by
            change Representation.Coinvariants.mk _ (e.toIntertwiningMap (ρ (k : G) v)) =
              Representation.Coinvariants.mk _ (e.toIntertwiningMap v)
            rw [Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap]
            exact Representation.Coinvariants.mk_self_apply (σ.comp K.subtype) k (e v)
      invFun := Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _ ∘ₗ
          e.symm.toLinearMap) fun k => LinearMap.ext fun v => by
            change Representation.Coinvariants.mk _ (e.symm.toIntertwiningMap (σ (k : G) v)) =
              Representation.Coinvariants.mk _ (e.symm.toIntertwiningMap v)
            rw [Representation.IntertwiningMap.isIntertwining σ ρ e.symm.toIntertwiningMap]
            exact Representation.Coinvariants.mk_self_apply (ρ.comp K.subtype) k (e.symm v)
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv c := by
        induction c using Representation.Coinvariants.induction_on with
        | h v => exact congrArg (Representation.Coinvariants.mk _) (e.symm_apply_apply v)
      right_inv c := by
        induction c using Representation.Coinvariants.induction_on with
        | h v => exact congrArg (Representation.Coinvariants.mk _) (e.apply_symm_apply v) }
    fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      refine Representation.Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
      change Representation.Coinvariants.mk _ (e.toIntertwiningMap (ρ g v)) =
        Representation.Coinvariants.mk _ (σ g (e.toIntertwiningMap v))
      rw [Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap]

/-- `invariantsToCoinvariants` commutes with the maps induced by an equivalence. -/
theorem invariantsToCoinvariants_equiv (e : ρ.Equiv σ)
    (v : Representation.invariants (ρ.comp K.subtype)) :
    invariantsToCoinvariants σ K (invariantsEquivOfEquiv K e v) =
      coinvariantsEquivOfEquiv K e (invariantsToCoinvariants ρ K v) :=
  rfl

/-- If `invariantsToCoinvariants` is bijective for `σ`, it is bijective for every
representation equivalent to `σ`. -/
theorem bijective_invariantsToCoinvariants_of_equiv (e : ρ.Equiv σ)
    (h : Function.Bijective (invariantsToCoinvariants σ K)) :
    Function.Bijective (invariantsToCoinvariants ρ K) := by
  have : (invariantsToCoinvariants ρ K : _ → _) =
      (coinvariantsEquivOfEquiv K e).symm ∘ invariantsToCoinvariants σ K ∘
        invariantsEquivOfEquiv K e := funext fun v => by
    change _ = (coinvariantsEquivOfEquiv K e).symm
      (coinvariantsEquivOfEquiv K e (invariantsToCoinvariants ρ K v))
    exact ((coinvariantsEquivOfEquiv K e).symm_apply_apply _).symm
  rw [this]
  exact (coinvariantsEquivOfEquiv K e).symm.bijective.comp
    (h.comp (invariantsEquivOfEquiv K e).bijective)

end InvariantsToCoinvariants

section PermutationNorm

variable {R : Type uR} {G : Type uG} {M : Type uM}
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M]
variable {H K : Subgroup G} (hHK : H ≤ K) [K.Normal] [(H.subgroupOf K).FiniteIndex]

/-- Under the identifications of the `K`-invariants (`permutationInvariantsLinearEquiv`) and of
the `K`-coinvariants (`permutationCoinvariantsLinearEquiv`) of the permutation representation
on `G ⧸ H` with the finitely supported functions on `G ⧸ K`, `invariantsToCoinvariants` is
multiplication by the index of `H` in `K`. -/
theorem permutationCoinvariantsLinearEquiv_invariantsToCoinvariants (ψ : G ⧸ K →₀ M) :
    permutationCoinvariantsLinearEquiv hHK
        (invariantsToCoinvariants (permutation R G (G ⧸ H) M) K (pullbackInvariant R hHK ψ)) =
      (H.subgroupOf K).index • ψ := by
  classical
  change Finsupp.mapDomain (Subgroup.quotientMapOfLE hHK) (pullbackInvariant R hHK ψ).1 = _
  refine Finsupp.ext fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hq : (QuotientGroup.mk g : G ⧸ K) =
      Subgroup.quotientMapOfLE hHK (QuotientGroup.mk g : G ⧸ H) := rfl
  rw [hq, Finsupp.mapDomain_apply_eq_sum, Finsupp.smul_apply]
  set c := ψ (Subgroup.quotientMapOfLE hHK (QuotientGroup.mk g : G ⧸ H))
  have hval : ∀ i ∈ (pullbackInvariant R hHK ψ).1.support.filter
      (fun i => Subgroup.quotientMapOfLE hHK i =
        Subgroup.quotientMapOfLE hHK (QuotientGroup.mk g : G ⧸ H)),
      (pullbackInvariant R hHK ψ).1 i = c := fun i hi =>
    congrArg ψ (Finset.mem_filter.mp hi).2
  rw [Finset.sum_congr rfl hval, Finset.sum_const]
  by_cases hc : c = 0
  · rw [hc, smul_zero, smul_zero]
  · congr 1
    have hfin := quotientMapOfLE_fiber_finite hHK
      (Subgroup.quotientMapOfLE hHK (QuotientGroup.mk g : G ⧸ H))
    rw [← card_quotientMapOfLE_fiber hHK, Nat.card_eq_card_finite_toFinset hfin]
    congr 1
    ext i
    rw [Finset.mem_filter, Finsupp.mem_support_iff, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change ψ (Subgroup.quotientMapOfLE hHK i) ≠ 0
      rwa [h]

include hHK in
/-- If the index of `H` in `K` is a unit of `R`, then `invariantsToCoinvariants` is bijective for
the permutation representation on `G ⧸ H`. -/
theorem bijective_invariantsToCoinvariants_permutation
    (h : IsUnit ((H.subgroupOf K).index : R)) :
    Function.Bijective (invariantsToCoinvariants (permutation R G (G ⧸ H) M) K) := by
  have key : (invariantsToCoinvariants (permutation R G (G ⧸ H) M) K : _ → _) =
      (permutationCoinvariantsLinearEquiv (M := M) hHK).symm ∘
        (fun ψ : G ⧸ K →₀ M => ((H.subgroupOf K).index : R) • ψ) ∘
          permutationInvariantsLinearEquiv R M hHK := funext fun v => by
    change _ = (permutationCoinvariantsLinearEquiv hHK).symm
      (((H.subgroupOf K).index : R) • permutationInvariantsLinearEquiv R M hHK v)
    rw [Nat.cast_smul_eq_nsmul R,
      ← permutationCoinvariantsLinearEquiv_invariantsToCoinvariants (R := R) (M := M) hHK,
      LinearEquiv.symm_apply_apply]
    exact congrArg _ ((permutationInvariantsLinearEquiv R M hHK).symm_apply_apply v).symm
  rw [key]
  exact (permutationCoinvariantsLinearEquiv hHK).symm.bijective.comp
    (h.smul_bijective.comp (permutationInvariantsLinearEquiv R M hHK).bijective)

end PermutationNorm

section Restriction

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable (ρ : Representation R G V) (K : Subgroup G) [K.Normal]
variable (σ : Representation R (G ⧸ K) W)

/-- `G`-equivariant maps from `V` to a representation of `G ⧸ K` inflated to `G` are the
`G ⧸ K`-equivariant maps from the `K`-coinvariants of `V`. -/
def homCoinvariantsEquiv :
    ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K)) ≃ₗ[R]
      (ρ.quotientToCoinvariants K).IntertwiningMap σ where
  toFun f :=
    { toLinearMap := Representation.Coinvariants.lift _ f.toLinearMap fun k =>
        LinearMap.ext fun v => by
          change f (ρ (k : G) v) = f v
          rw [Representation.IntertwiningMap.isIntertwining _ _ f]
          change σ (QuotientGroup.mk (k : G)) (f v) = f v
          rw [(QuotientGroup.eq_one_iff (k : G)).mpr k.2, map_one]
          rfl
      isIntertwining' q := by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        refine Representation.Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
        exact Representation.IntertwiningMap.isIntertwining _ _ f g v }
  invFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ Representation.Coinvariants.mk _
      isIntertwining' g := LinearMap.ext fun v =>
        Representation.IntertwiningMap.isIntertwining _ _ f (QuotientGroup.mk g)
          (Representation.Coinvariants.mk _ v) }
  map_add' _ _ := Representation.IntertwiningMap.ext <| Representation.Coinvariants.hom_ext rfl
  map_smul' _ _ := Representation.IntertwiningMap.ext <| Representation.Coinvariants.hom_ext rfl
  left_inv _ := rfl
  right_inv f := Representation.IntertwiningMap.ext <|
    Representation.Coinvariants.hom_ext rfl

/-- The restriction of a `G`-equivariant map from `V` to a representation of `G ⧸ K` inflated to
`G` to the `K`-invariants of `V`, as a `G ⧸ K`-equivariant map. -/
def invariantsRestriction :
    ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K)) →ₗ[R]
      (ρ.quotientToInvariants K).IntertwiningMap σ where
  toFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ (Representation.invariants (ρ.comp K.subtype)).subtype
      isIntertwining' q := by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact LinearMap.ext fun v => Representation.IntertwiningMap.isIntertwining _ _ f g v.1 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ρ K σ}

/-- `invariantsRestriction f` is `f` on invariant vectors. -/
theorem invariantsRestriction_apply (f : ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K)))
    (v : Representation.invariants (ρ.comp K.subtype)) :
    invariantsRestriction ρ K σ f v = f v.1 :=
  rfl

/-- The restriction to invariants factors through the coinvariants: it is the map on coinvariants
corresponding to `f`, composed with `invariantsToCoinvariants`. -/
theorem invariantsRestriction_eq_comp (f : ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K))) :
    invariantsRestriction ρ K σ f =
      (homCoinvariantsEquiv ρ K σ f).comp (invariantsToCoinvariants ρ K) :=
  Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

/-- Precomposition with an equivalence of representations, as a linear equivalence of spaces of
equivariant maps. -/
def precompEquiv {G' : Type uG} [Group G'] {X : Type uX} {Y : Type uY} {Z : Type uW}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    {α : Representation R G' X} {β : Representation R G' Y} (τ : Representation R G' Z)
    (e : α.Equiv β) : β.IntertwiningMap τ ≃ₗ[R] α.IntertwiningMap τ where
  toFun f := f.comp e.toIntertwiningMap
  invFun f := f.comp e.symm.toIntertwiningMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Representation.IntertwiningMap.ext <| LinearMap.ext fun y =>
    congrArg f (e.apply_symm_apply y)
  right_inv f := Representation.IntertwiningMap.ext <| LinearMap.ext fun x =>
    congrArg f (e.symm_apply_apply x)

variable (ρ K σ)

/-- If `invariantsToCoinvariants` is bijective, restriction to the `K`-invariants is a linear
equivalence between the `G`-equivariant maps from `V` to the inflation of `W` and the
`G ⧸ K`-equivariant maps from the `K`-invariants of `V` to `W`. -/
def invariantsRestrictionEquiv (h : Function.Bijective (invariantsToCoinvariants ρ K)) :
    ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K)) ≃ₗ[R]
      (ρ.quotientToInvariants K).IntertwiningMap σ :=
  (homCoinvariantsEquiv ρ K σ).trans
    (precompEquiv σ ((invariantsToCoinvariants ρ K).ofBijective h))

variable {ρ K σ}

/-- `invariantsRestrictionEquiv` is `invariantsRestriction`. -/
theorem invariantsRestrictionEquiv_apply (h : Function.Bijective (invariantsToCoinvariants ρ K))
    (f : ρ.IntertwiningMap (σ.comp (QuotientGroup.mk' K))) :
    invariantsRestrictionEquiv ρ K σ h f = invariantsRestriction ρ K σ f :=
  Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

end Restriction

section ProP

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Let `K` be a compact subgroup whose quotients by open normal subgroups are `p`-groups (the
fields `compactSpace` and `isPGroup` of a pro-`p` subgroup). Then every open subgroup `H` of `G`
has index a power of `p` in `K`. -/
theorem exists_index_subgroupOf_eq_pow {p : ℕ} (hp : p.Prime) {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) [CompactSpace K]
    (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup)) :
    ∃ n : ℕ, (H.subgroupOf K).index = p ^ n := by
  have hU : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) := Subgroup.subgroupOf_isOpen K H hH
  have := Subgroup.quotient_finite_of_isOpen (H.subgroupOf K) hU
  have : (H.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcl : IsClosed (((H.subgroupOf K).normalCore : Subgroup K) : Set K) :=
    Subgroup.normalCore_isClosed _ (Subgroup.isClosed_of_isOpen _ hU)
  let N : OpenNormalSubgroup K :=
    { toSubgroup := (H.subgroupOf K).normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl }
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hK N)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp
    ((congr_arg _ ((H.subgroupOf K).normalCore.index_eq_card.trans hn)).mp
      (Subgroup.index_dvd_of_le (H.subgroupOf K).normalCore_le))
  exact ⟨k, hk⟩

/-- Under the hypotheses of `exists_index_subgroupOf_eq_pow`, if `p` is a unit of `R` then so is
the index of `H` in `K`. -/
theorem isUnit_index_subgroupOf {R : Type uR} [CommRing R] {p : ℕ} (hp : p.Prime)
    (hR : IsUnit (p : R)) {H K : Subgroup G} (hH : IsOpen (H : Set G)) [CompactSpace K]
    (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup)) :
    IsUnit ((H.subgroupOf K).index : R) := by
  obtain ⟨n, hn⟩ := exists_index_subgroupOf_eq_pow hp hH hK
  rw [hn, Nat.cast_pow]
  exact hR.pow n

end ProP

section CompactInduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
variable {H K : Subgroup G} (hH : IsOpen (H : Set G)) (hHK : H ≤ K) [K.Normal]

/-- The `K`-coinvariants of the compact induction from an open subgroup `H ≤ K` of the trivial
representation on `M` are the permutation representation of `G ⧸ K` on itself. -/
def compactInducedCoinvariantsEquiv :
    ((compactInduced H (Representation.trivial R H M)).quotientToCoinvariants K).Equiv
      (permutation R (G ⧸ K) (G ⧸ K) M) :=
  (coinvariantsEquivOfEquiv K (permutationEquiv R M H hH)).trans
    (permutationCoinvariantsEquiv R M hHK)

variable [(H.subgroupOf K).FiniteIndex] {R M}

include hH hHK in
/-- If the index of `H` in `K` is a unit of `R`, `invariantsToCoinvariants` is bijective for the
compact induction from `H` of a trivial representation. -/
theorem bijective_invariantsToCoinvariants_compactInduced
    (h : IsUnit ((H.subgroupOf K).index : R)) :
    Function.Bijective
      (invariantsToCoinvariants (compactInduced H (Representation.trivial R H M)) K) :=
  bijective_invariantsToCoinvariants_of_equiv K (permutationEquiv R M H hH)
    (bijective_invariantsToCoinvariants_permutation hHK h)

variable {W : Type uW} [AddCommGroup W] [Module R W] (σ : Representation R (G ⧸ K) W)

/-- For `H ≤ K` open with `K` normal and the index of `H` in `K` a unit of `R`, restriction to
`K`-invariants identifies the `G`-equivariant maps from the compact induction of a trivial
representation to the inflation of a representation `σ` of `G ⧸ K` with the `G ⧸ K`-equivariant
maps from its `K`-invariants to `σ`. -/
def compactInducedInvariantsRestrictionEquiv (h : IsUnit ((H.subgroupOf K).index : R)) :
    (compactInduced H (Representation.trivial R H M)).IntertwiningMap
        (σ.comp (QuotientGroup.mk' K)) ≃ₗ[R]
      ((compactInduced H (Representation.trivial R H M)).quotientToInvariants K).IntertwiningMap
        σ :=
  invariantsRestrictionEquiv _ K σ (bijective_invariantsToCoinvariants_compactInduced hH hHK h)

end CompactInduction

end Langlands.Induction
