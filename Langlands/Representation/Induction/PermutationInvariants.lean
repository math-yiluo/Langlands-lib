import Langlands.Representation.Induction.PermutationModule

/-!
# Invariants of permutation modules under normal subgroups

Let `H ≤ K` be subgroups of a group `G` with `K` normal and `H` of finite index in `K`. A
`K`-invariant finitely supported function on `G ⧸ H` is constant on the fibres of
`G ⧸ H → G ⧸ K` (`invariantValue`), and every finitely supported function on `G ⧸ K` pulls back
to a `K`-invariant finitely supported function on `G ⧸ H`, since these fibres are finite
(`pullbackInvariant`). Hence the `K`-invariants of the permutation
representation `permutation R G (G ⧸ H) M`, as a representation of `G ⧸ K`, are the permutation
representation of `G ⧸ K` on itself with coefficients `M` (`permutationInvariantsEquiv`). With
coefficients `I →₀ R` they are the free `R[G ⧸ K]`-module of rank `I`
(`permutationInvariantsFreeEquiv`, `permutationInvariants_free`). For `H` normal, this says that
the `K`-invariants of the free `R[G ⧸ H]`-module of rank `I` are the free `R[G ⧸ K]`-module of
rank `I` (`freeInvariantsEquiv`, `freeInvariants_free`).

For a topological group `G` and an open subgroup `H`, the published compact induction of the
trivial representation on `M` is the permutation representation on `G ⧸ H`
(`Langlands.Induction.permutationEquiv`). Its `K`-invariants are therefore the permutation
representation of `G ⧸ K` (`compactInducedInvariantsEquiv`), and with coefficients `I →₀ R` a free
`R[G ⧸ K]`-module (`compactInducedInvariants_free`). If `K` is compact, then `H` has finite index
in `K` (`finiteIndex_subgroupOf_of_isCompact`).

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312: "Since `C^j_m(ẽ)^{H_p}` and
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules". This module proves the
algebraic step that invariants of a free `R[G ⧸ H]`-module under a normal subgroup `K ⊇ H`, in
which `H` has finite index, are a free `R[G ⧸ K]`-module. It does not prove that Harris's modules
are free; the definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uM uI uV uW

section Fibres

variable {G : Type uG} [Group G] {H K : Subgroup G} (hHK : H ≤ K)

/-- If `H ≤ K` and `H` has finite index in `K`, the fibres of `G ⧸ H → G ⧸ K` are finite: the
fibre over `g K` is the image of `K ⧸ H` under `k H ↦ g k H`. -/
theorem quotientMapOfLE_fiber_finite [(H.subgroupOf K).FiniteIndex] (q : G ⧸ K) :
    (Subgroup.quotientMapOfLE hHK ⁻¹' {q}).Finite := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine (Set.finite_range fun k : K ⧸ H.subgroupOf K =>
    Quotient.liftOn' k (fun k => (QuotientGroup.mk (g * k) : G ⧸ H)) fun a b hab => ?_).subset ?_
  · have h : ((a⁻¹ * b : K) : G) ∈ H :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
    refine QuotientGroup.eq.mpr ?_
    simpa [mul_assoc] using h
  · intro p hp
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
    have hp' : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk g := hp
    have hy : g⁻¹ * y ∈ K := QuotientGroup.eq.mp hp'.symm
    refine ⟨QuotientGroup.mk ⟨g⁻¹ * y, hy⟩, ?_⟩
    change (QuotientGroup.mk (g * (g⁻¹ * y)) : G ⧸ H) = QuotientGroup.mk y
    rw [mul_inv_cancel_left]

end Fibres

section EquivInvariants

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W} (K : Subgroup G)

/-- An equivalence of representations maps `K`-invariant vectors to `K`-invariant vectors. -/
theorem equiv_apply_mem_invariants (e : ρ.Equiv σ) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp K.subtype)) :
    e v ∈ Representation.invariants (σ.comp K.subtype) :=
  (Representation.mem_invariants _ _).mpr fun k => by
    have h := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (k : G)) v
    have hk : ρ k v = v := (Representation.mem_invariants _ _).mp hv k
    change e (ρ k v) = σ k (e v) at h
    change σ k (e v) = e v
    rw [← h, hk]

variable [K.Normal]

/-- An equivalence of representations of `G` restricts to the invariants of a normal subgroup
`K`, as an equivalence of representations of `G ⧸ K`. -/
def invariantsEquivOfEquiv (e : ρ.Equiv σ) :
    (ρ.quotientToInvariants K).Equiv (σ.quotientToInvariants K) :=
  .mk
    { toFun := fun v => ⟨e v.1, equiv_apply_mem_invariants K e v.2⟩
      map_add' := fun v w => Subtype.ext (map_add e v.1 w.1)
      map_smul' := fun r v => Subtype.ext (map_smul e r v.1)
      invFun := fun w => ⟨e.symm w.1, equiv_apply_mem_invariants K e.symm w.2⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
    fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      refine LinearMap.ext fun v => Subtype.ext ?_
      change e (ρ g v.1) = σ g (e v.1)
      exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v.1

end EquivInvariants

section AsModule

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- An equivalence of representations, as an isomorphism of modules over the group algebra. The
Library's `Langlands.representationAsModuleEquiv` is the same construction for commutative rings,
groups and additive groups; this version needs only commutative semirings, monoids and additive
commutative monoids. -/
def asModuleLinearEquiv (e : ρ.Equiv σ) : ρ.asModule ≃ₗ[MonoidAlgebra R G] σ.asModule :=
  LinearEquiv.ofLinearMap
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap)
    (LinearMap.ext fun w => e.apply_symm_apply w)
    (LinearMap.ext fun v => e.symm_apply_apply v)

end AsModule

section Invariants

variable {R : Type uR} {G : Type uG} {M : Type uM}
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M]
variable {H K : Subgroup G} (hHK : H ≤ K) [K.Normal]

/-- The value of a `K`-invariant finitely supported function on `G ⧸ H` at the coset `g K`: its
value at `g H`, which depends only on `g K`. -/
def invariantValue (φ : Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype))
    (q : G ⧸ K) : M :=
  Quotient.liftOn' q (fun g => φ.1 (QuotientGroup.mk g)) fun a b hab => by
    have hc : b * a⁻¹ ∈ K := ‹K.Normal›.mem_comm (QuotientGroup.leftRel_apply.mp hab)
    have h : permutation R G (G ⧸ H) M (b * a⁻¹) φ.1 (QuotientGroup.mk b) =
        φ.1 (QuotientGroup.mk b) :=
      congrArg (fun ψ : G ⧸ H →₀ M => ψ (QuotientGroup.mk b))
        ((Representation.mem_invariants _ _).mp φ.2 ⟨b * a⁻¹, hc⟩)
    rwa [permutation_apply, MulAction.Quotient.smul_mk, smul_eq_mul, mul_inv_rev, inv_inv,
      inv_mul_cancel_right] at h

/-- The value of `invariantValue φ` at `g K` is the value of `φ` at `g H`. -/
theorem invariantValue_mk
    (φ : Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype)) (g : G) :
    invariantValue φ (QuotientGroup.mk g) = φ.1 (QuotientGroup.mk g) :=
  rfl

include hHK in
/-- The support of `invariantValue φ` is the image of the support of `φ` in `G ⧸ K`. -/
theorem invariantValue_support_finite
    (φ : Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype)) :
    (Function.support (invariantValue φ)).Finite := by
  refine (φ.1.support.finite_toSet.image (Subgroup.quotientMapOfLE hHK)).subset ?_
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk g, Finsupp.mem_support_iff.mpr hq, rfl⟩

variable (R M)

/-- A `K`-invariant finitely supported function on `G ⧸ H` as a finitely supported function on
`G ⧸ K`. -/
def invariantsToQuotient :
    Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype) →ₗ[R] (G ⧸ K →₀ M) where
  toFun φ := Finsupp.ofSupportFinite (invariantValue φ) (invariantValue_support_finite hHK φ)
  map_add' _ _ := Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl
  map_smul' _ _ := Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl

variable {R M}

variable [(H.subgroupOf K).FiniteIndex]

omit [K.Normal] in
/-- A finitely supported function on `G ⧸ K` composed with `G ⧸ H → G ⧸ K` has finite support,
since the fibres are finite. -/
theorem comp_quotientMapOfLE_support_finite (ψ : G ⧸ K →₀ M) :
    (Function.support (ψ ∘ Subgroup.quotientMapOfLE hHK)).Finite :=
  (ψ.support.finite_toSet.preimage' fun q _ => quotientMapOfLE_fiber_finite hHK q).subset
    fun _ hp => Finsupp.mem_support_iff.mpr hp

variable (R)

/-- A finitely supported function on `G ⧸ K`, pulled back to a `K`-invariant finitely supported
function on `G ⧸ H`. -/
def pullbackInvariant (ψ : G ⧸ K →₀ M) :
    Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype) :=
  ⟨Finsupp.ofSupportFinite (ψ ∘ Subgroup.quotientMapOfLE hHK)
      (comp_quotientMapOfLE_support_finite hHK ψ),
    (Representation.mem_invariants _ _).mpr fun k => Finsupp.ext fun p => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
      change permutation R G (G ⧸ H) M (k : G)
          (Finsupp.ofSupportFinite (ψ ∘ Subgroup.quotientMapOfLE hHK)
            (comp_quotientMapOfLE_support_finite hHK ψ)) (QuotientGroup.mk y) =
        ψ (QuotientGroup.mk y)
      rw [permutation_apply, MulAction.Quotient.smul_mk, smul_eq_mul]
      change ψ (QuotientGroup.mk ((k : G)⁻¹ * y)) = ψ (QuotientGroup.mk y)
      refine congrArg ψ (QuotientGroup.eq.mpr ?_)
      rw [mul_inv_rev, inv_inv]
      exact ‹K.Normal›.conj_mem' _ k.2 y⟩

/-- The value of `pullbackInvariant R hHK ψ` at `g H` is the value of `ψ` at `g K`. -/
theorem pullbackInvariant_mk (ψ : G ⧸ K →₀ M) (g : G) :
    (pullbackInvariant R hHK ψ).1 (QuotientGroup.mk g) = ψ (QuotientGroup.mk g) :=
  rfl

variable (M)

/-- The `K`-invariant finitely supported functions on `G ⧸ H` are the finitely supported functions
on `G ⧸ K`. -/
def permutationInvariantsLinearEquiv :
    Representation.invariants ((permutation R G (G ⧸ H) M).comp K.subtype) ≃ₗ[R] (G ⧸ K →₀ M) where
  __ := invariantsToQuotient R M hHK
  invFun := pullbackInvariant R hHK
  left_inv _ := Subtype.ext <| Finsupp.ext fun p => Quotient.inductionOn' p fun _ => rfl
  right_inv _ := Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl

/-- The `K`-invariants of the permutation representation on `G ⧸ H`, as a representation of
`G ⧸ K`, are the permutation representation of `G ⧸ K` on itself with coefficients `M`. -/
def permutationInvariantsEquiv :
    ((permutation R G (G ⧸ H) M).quotientToInvariants K).Equiv
      (permutation R (G ⧸ K) (G ⧸ K) M) :=
  .mk (permutationInvariantsLinearEquiv R M hHK) fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine LinearMap.ext fun φ => Finsupp.ext fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    change permutation R G (G ⧸ H) M g φ.1 (QuotientGroup.mk y) =
      permutation R (G ⧸ K) (G ⧸ K) M (QuotientGroup.mk g)
        (permutationInvariantsLinearEquiv R M hHK φ) (QuotientGroup.mk y)
    rw [permutation_apply, permutation_apply, MulAction.Quotient.smul_mk]
    simp only [smul_eq_mul]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

variable (I : Type uI)

/-- With coefficients `I →₀ R`, the `K`-invariants of the permutation representation on `G ⧸ H`
are the free `R[G ⧸ K]`-module of rank `I`. -/
def permutationInvariantsFreeEquiv :
    ((permutation R G (G ⧸ H) (I →₀ R)).quotientToInvariants K).Equiv
      (Representation.free R (G ⧸ K) I) :=
  (permutationInvariantsEquiv R (I →₀ R) hHK).trans
    (permutationFinsuppEquiv R (G ⧸ K) (G ⧸ K) I)

include hHK in
/-- With coefficients `I →₀ R`, the `K`-invariants of the permutation representation on `G ⧸ H`
form a free module over the group algebra `R[G ⧸ K]`. -/
theorem permutationInvariants_free :
    Module.Free (MonoidAlgebra R (G ⧸ K))
      ((permutation R G (G ⧸ H) (I →₀ R)).quotientToInvariants K).asModule :=
  have := Representation.free_asModule_free R (G ⧸ K) I
  Module.Free.of_equiv (asModuleLinearEquiv (permutationInvariantsFreeEquiv R hHK I)).symm

variable [H.Normal]

/-- For `H` normal, the free `R[G ⧸ H]`-module of rank `I`, as a representation of `G`, is the
permutation representation on `G ⧸ H` with coefficients `I →₀ R`. -/
def freeCompEquiv :
    Representation.Equiv ((Representation.free R (G ⧸ H) I).comp (QuotientGroup.mk' H))
      (permutation R G (G ⧸ H) (I →₀ R)) :=
  .mk (permutationFinsuppEquiv R G (G ⧸ H) I).symm.toLinearEquiv fun g => by
    rw [← finsupp_ofMulAction_quotient]
    exact (permutationFinsuppEquiv R G (G ⧸ H) I).symm.toIntertwiningMap.isIntertwining' g

/-- For `H ≤ K` normal with `H` of finite index in `K`, the `K`-invariants of the free
`R[G ⧸ H]`-module of rank `I` are the free `R[G ⧸ K]`-module of rank `I`. -/
def freeInvariantsEquiv :
    (Representation.quotientToInvariants
      ((Representation.free R (G ⧸ H) I).comp (QuotientGroup.mk' H)) K).Equiv
      (Representation.free R (G ⧸ K) I) :=
  (invariantsEquivOfEquiv K (freeCompEquiv R I)).trans (permutationInvariantsFreeEquiv R hHK I)

include hHK in
/-- For `H ≤ K` normal with `H` of finite index in `K`, the `K`-invariants of a free
`R[G ⧸ H]`-module form a free `R[G ⧸ K]`-module. -/
theorem freeInvariants_free :
    Module.Free (MonoidAlgebra R (G ⧸ K))
      (Representation.quotientToInvariants
        ((Representation.free R (G ⧸ H) I).comp (QuotientGroup.mk' H)) K).asModule := by
  have := Representation.free_asModule_free R (G ⧸ K) I
  let e := asModuleLinearEquiv (freeInvariantsEquiv R hHK I)
  exact Module.Free.of_equiv e.symm

end Invariants

section CompactInduction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup `H` has finite index in every compact subgroup `K`. -/
theorem finiteIndex_subgroupOf_of_isCompact {H K : Subgroup G} (hH : IsOpen (H : Set G))
    (hK : IsCompact (K : Set G)) : (H.subgroupOf K).FiniteIndex :=
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have := Subgroup.quotient_finite_of_isOpen (H.subgroupOf K) (Subgroup.subgroupOf_isOpen K H hH)
  Subgroup.finiteIndex_of_finite_quotient

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
variable {H K : Subgroup G} (hH : IsOpen (H : Set G)) (hHK : H ≤ K) [K.Normal]
variable [(H.subgroupOf K).FiniteIndex]

/-- For an open subgroup `H ≤ K` with `K` normal and `H` of finite index in `K`, the
`K`-invariants of the compact induction from `H` of the trivial representation on `M` are the
permutation representation of `G ⧸ K` on itself with coefficients `M`. -/
def compactInducedInvariantsEquiv :
    ((compactInduced H (Representation.trivial R H M)).quotientToInvariants K).Equiv
      (permutation R (G ⧸ K) (G ⧸ K) M) :=
  (invariantsEquivOfEquiv K (permutationEquiv R M H hH)).trans
    (permutationInvariantsEquiv R M hHK)

variable (I : Type uI)

/-- With coefficients `I →₀ R`, the `K`-invariants of the compact induction from `H` of the
trivial representation are the free `R[G ⧸ K]`-module of rank `I`. -/
def compactInducedInvariantsFreeEquiv :
    ((compactInduced H (Representation.trivial R H (I →₀ R))).quotientToInvariants K).Equiv
      (Representation.free R (G ⧸ K) I) :=
  (invariantsEquivOfEquiv K (permutationEquiv R (I →₀ R) H hH)).trans
    (permutationInvariantsFreeEquiv R hHK I)

include hH hHK in
/-- With coefficients `I →₀ R`, the `K`-invariants of the compact induction from `H` of the
trivial representation form a free module over the group algebra `R[G ⧸ K]`. -/
theorem compactInducedInvariants_free :
    Module.Free (MonoidAlgebra R (G ⧸ K))
      ((compactInduced H (Representation.trivial R H (I →₀ R))).quotientToInvariants K).asModule :=
  have := Representation.free_asModule_free R (G ⧸ K) I
  Module.Free.of_equiv (asModuleLinearEquiv (compactInducedInvariantsFreeEquiv R hH hHK I)).symm

end CompactInduction

end Langlands.Induction
