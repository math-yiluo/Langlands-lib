import Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit
import Langlands.Cohomology.DivisibleSystem.FreeReduction
import Langlands.Representation.LocallyConstant.CompactAction
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# The regular representation of a profinite group as a direct limit of free modules

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ.
39-2 (1999), §2, printed p.306: "Taking the direct limit as `H` shrinks to the identity, we obtain
an `ℓ`-divisible system of complexes `C_m^•` of projective `ℤ/ℓ^mℤ[S(e)]`-modules"; proof of
Proposition 4.10, printed pp.311-312: "Recall that `C^j(ẽ)` has been chosen to be a direct limit
of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open subgroups of
`S(ẽ)`." and "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."

The Library module `FreeQuotientLimit` formalizes such coefficient modules as the predicate
`IsFreeLimit`, with its consequences for the Hom inverse systems. This module supplies an actual
instance of the interface: the smooth regular representation of a profinite group, together with
its `ℓ`-adic reduction system.

For a topological group `G` and an `R`-module `M`, `regularRepresentation R M` is the
representation of `G` on the locally constant functions `G → M` by left translation,
`(g • f)(x) = f(g⁻¹ x)`; it is the Library's `diagonalRepresentation` of the trivial
representation on `M`. It is smooth when `G` is compact (the Library's
`diagonalRepresentation_isSmooth`), but for a noncompact `G` it need not be smooth: smoothness asks
for an open subgroup fixing each function, while local constancy is a condition on each function
alone. No smoothness is asserted for it in general; the constructions on it below for an arbitrary
topological group `G` are algebraic, and smoothness enters only through compactness of `G`.

Results:

* `IsFreeOnInvariants.of_equiv`, `IsFreeLimit.of_equiv`: both predicates transfer along
  equivalences of representations;
* `regularInvariantsEquiv`: for `G` compact and `H` open and normal, the `H`-invariants of
  `regularRepresentation R M`, as a representation of the finite group `G ⧸ H`, are the
  permutation representation of `G ⧸ H` on itself with coefficients `M` (an `H`-invariant
  locally constant function is a function on `G ⧸ H`);
* `isFreeOnInvariants_regular`, `isFreeLimit_regular`: with coefficients `I →₀ k` these
  invariants are free `k[G ⧸ H]`-modules, and for `G` compact and totally disconnected
  (profinite) the representation is `IsFreeLimit` over the family of all open normal subgroups
  (`openNormalSubgroup_shrink`);
* `regularReduction`, `regularReductionComplex_exact`, `cokernelRegularIso`: for `ℓ : ℕ`, the
  cokernel of multiplication by `ℓ ^ m` on `regularRep R G I` (coefficients `I →₀ R`) is, through
  reduction of the values, the regular representation with coefficients `I →₀ R ⧸ (ℓ ^ m)`; `mono_powSMul_regular`: multiplication by `ℓ` is a monomorphism when `ℓ` is a
  non-zero-divisor in `R`;
* `isFreeLimit_cokernel_powSMul_regular`, `isFreeLimit_reductionSystem_regular`: for `G`
  profinite, every level `m` of the Library's reduction system `m ↦ L / ℓ ^ m L` of
  `L = regularRep R G I` is a direct limit of free `(R ⧸ (ℓ ^ m))[G ⧸ N]`-modules over the open
  normal subgroups `N`;
* for `K` open and normal, the Hom-system statements of `FreeQuotientLimit` for this reduction
  system: surjective transitions and the Mittag-Leffler condition for `m ↦ Hom((T m)^K, W m)`
  (`regular_invariants_homSystem_map_surjective`, `isMittagLeffler_regular_invariants_homSystem`)
  and, for `K` pro-`p` with `p` invertible in `R`, bijectivity of `invariantsToCoinvariants`
  (`bijective_invariantsToCoinvariants_reductionSystem_regular`) and the same statements for
  `m ↦ Hom(T m, Inf (W m))` with the hypothesis of `mapLeftExact` derived
  (`regular_homSystem_map_surjective`, `isMittagLeffler_regular_homSystem`).

For a profinite group `G`, the regular representation is smooth and is the simplest direct limit
of free modules over the quotient group algebras: its `N`-invariants are `⊕_I k[G ⧸ N]`. Harris's complexes `C_m^•` and
modules `C^j_m(ẽ)` are not constructed here, and it is not claimed that they are regular
representations. The definitions, statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Induction

open Langlands.CompactAction.LocallyConstantModule

universe uR uk uG uM uI uV uι

section Transport

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V W : Type uV} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}
  {k : Type uk} [CommRing k] [Algebra R k]

/-- Freeness of the invariants transfers along an equivalence of representations. -/
theorem IsFreeOnInvariants.of_equiv (e : ρ.Equiv σ) {H : Subgroup G} [H.Normal]
    (h : IsFreeOnInvariants σ k H) : IsFreeOnInvariants ρ k H := by
  obtain ⟨I, ⟨e'⟩⟩ := h
  exact ⟨I, ⟨(invariantsEquivOfEquiv H e).trans e'⟩⟩

/-- Being a direct limit of free modules transfers along an equivalence of representations. -/
theorem IsFreeLimit.of_equiv (e : ρ.Equiv σ) {ι : Type uι} {H : ι → Subgroup G}
    [∀ i, (H i).Normal] (h : IsFreeLimit σ k H) : IsFreeLimit ρ k H where
  directed := h.directed
  exhaustive v := by
    obtain ⟨i, hi⟩ := h.exhaustive (e v)
    refine ⟨i, ?_⟩
    have := equiv_apply_mem_invariants (H i) e.symm hi
    simpa using this
  free i := (h.free i).of_equiv e

end Transport

section Regular

variable (R : Type uR) [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : Type uM) [AddCommGroup M] [Module R M]

/-- The regular representation of `G` on locally constant functions with coefficients `M`: `G`
acts on the locally constant functions `G → M` by left translation, `(g • f)(x) = f(g⁻¹ x)`. It is
the Library's `diagonalRepresentation` of the trivial representation on `M`, for `G` acting on
itself by left multiplication. It is smooth when `G` is compact (`diagonalRepresentation_isSmooth`)
but need not be smooth for a noncompact topological group `G`; no smoothness is asserted here. -/
abbrev regularRepresentation : Representation R G (LocallyConstant G M) :=
  diagonalRepresentation (X := G) (Representation.trivial R G M)

theorem regularRepresentation_apply (g : G) (f : LocallyConstant G M) (x : G) :
    regularRepresentation R M g f x = f (g⁻¹ * x) :=
  rfl

variable {R M} (H : Subgroup G) [H.Normal]

/-- A locally constant function invariant under left translation by a normal subgroup `H` is
invariant under right translation by `H`. -/
theorem regular_invariant_apply_mul {f : LocallyConstant G M}
    (hf : f ∈ Representation.invariants ((regularRepresentation R M).comp H.subtype))
    (x : G) {h : G} (hh : h ∈ H) : f (x * h) = f x := by
  have hh' : x * h * x⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance h hh x
  have := congrArg (fun φ : LocallyConstant G M => φ x) (hf ⟨(x * h * x⁻¹)⁻¹, H.inv_mem hh'⟩)
  change f ((x * h * x⁻¹)⁻¹⁻¹ * x) = f x at this
  rwa [inv_inv, mul_assoc, inv_mul_cancel, mul_one] at this

/-- An `H`-invariant locally constant function, as a function on `G ⧸ H`. -/
def regularInvariantsDescend
    (f : Representation.invariants ((regularRepresentation R M).comp H.subtype)) :
    G ⧸ H → M :=
  fun q => Quotient.liftOn' q (fun x => f.1 x) fun x y hxy => by
    have h := regular_invariant_apply_mul H f.2 x (QuotientGroup.leftRel_apply.mp hxy)
    rw [mul_inv_cancel_left] at h
    exact h.symm

theorem regularInvariantsDescend_mk
    (f : Representation.invariants ((regularRepresentation R M).comp H.subtype)) (x : G) :
    regularInvariantsDescend H f (QuotientGroup.mk x) = f.1 x :=
  rfl

variable {H} (hH : IsOpen (H : Set G))

include hH in
/-- A function on `G ⧸ H`, for `H` open and normal, pulled back to an `H`-invariant locally
constant function on `G`. -/
def regularInvariantsPullback (φ : G ⧸ H → M) :
    Representation.invariants ((regularRepresentation R M).comp H.subtype) :=
  haveI := QuotientGroup.discreteTopology hH
  ⟨⟨fun x => φ (QuotientGroup.mk x),
    (IsLocallyConstant.of_discrete φ).comp_continuous continuous_quot_mk⟩,
    fun h => by
      refine LocallyConstant.ext fun x => ?_
      rw [MonoidHom.comp_apply, diagonalRepresentation_apply, Representation.trivial_apply]
      change φ (QuotientGroup.mk ((h : G)⁻¹ * x)) = φ (QuotientGroup.mk x)
      refine congrArg φ (QuotientGroup.eq.mpr ?_)
      have : x⁻¹ * (h : G) * x ∈ H := by
        simpa using Subgroup.Normal.conj_mem inferInstance _ h.2 x⁻¹
      simpa [mul_assoc] using this⟩

theorem regularInvariantsPullback_apply (φ : G ⧸ H → M) (x : G) :
    (regularInvariantsPullback (R := R) hH φ).1 x = φ (QuotientGroup.mk x) :=
  rfl

variable [CompactSpace G]

include hH in
/-- For an open normal subgroup `H` of a compact group `G`, the `H`-invariants of the regular
representation with coefficients `M`, as a representation of the finite group `G ⧸ H`,
are the permutation representation of `G ⧸ H` on itself with coefficients `M`. -/
def regularInvariantsEquiv :
    ((regularRepresentation R M).quotientToInvariants H).Equiv
      (permutation R (G ⧸ H) (G ⧸ H) M) :=
  haveI := Subgroup.quotient_finite_of_isOpen H hH
  haveI := Fintype.ofFinite (G ⧸ H)
  .mk
    { toFun := fun f => Finsupp.equivFunOnFinite.symm (regularInvariantsDescend H f)
      map_add' := fun f g => Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl
      map_smul' := fun r f => Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl
      invFun := fun φ => regularInvariantsPullback hH φ
      left_inv := fun f => Subtype.ext (LocallyConstant.ext fun _ => rfl)
      right_inv := fun φ => Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl }
    fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      refine LinearMap.ext fun f => Finsupp.ext fun q => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [LinearMap.comp_apply, LinearMap.comp_apply, permutation_apply]
      change f.1 (g⁻¹ * y) = regularInvariantsDescend H f
        ((QuotientGroup.mk g : G ⧸ H)⁻¹ • QuotientGroup.mk y)
      rw [smul_eq_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl

variable (k : Type uk) [CommRing k] [Algebra R k]

include hH in
/-- For an open normal subgroup `H` of a compact group `G` and an index type `I`, the
`H`-invariants of the regular representation with coefficients `I →₀ k` are a free
`k[G ⧸ H]`-module. -/
theorem isFreeOnInvariants_regular (I : Type uI) :
    IsFreeOnInvariants (regularRepresentation R (I →₀ k)) k H :=
  ⟨ULift.{max uG uk} I, ⟨(regularInvariantsEquiv hH).trans
    (permutationCongr R (G ⧸ H) (G ⧸ H) (Finsupp.domLCongr Equiv.ulift.symm))⟩⟩

end Regular

section Profinite

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  (k : Type uk) [CommRing k] [Algebra R k] (I : Type uI)

/-- The open normal subgroups of a profinite group shrink to the identity. -/
theorem openNormalSubgroup_shrink :
    ∀ U ∈ nhds (1 : G), ∃ N : OpenNormalSubgroup G, ((N.toSubgroup : Subgroup G) : Set G) ⊆ U :=
  fun U hU => by
    obtain ⟨V, hVU, hVo, h1⟩ := mem_nhds_iff.mp hU
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1
    exact ⟨N, hN.trans hVU⟩

/-- **The smooth regular representation of a profinite group is a direct limit of free
modules.** For a compact totally disconnected group `G`, the locally constant functions
`G → (I →₀ k)` with left translation are the direct limit of the free `k[G ⧸ N]`-modules of their
`N`-invariants, as `N` runs over the open normal subgroups of `G`. -/
theorem isFreeLimit_regular :
    IsFreeLimit (regularRepresentation R (I →₀ k)) k
      (fun N : OpenNormalSubgroup G => N.toSubgroup) :=
  IsFreeLimit.of_isSmooth _ (fun N => N.isOpen') (openNormalSubgroup_shrink G)
    (diagonalRepresentation_isSmooth _ fun _ => ⟨⊤, fun _ => rfl⟩)
    (fun N => isFreeOnInvariants_regular N.isOpen' k I)

end Profinite

end Langlands.Induction

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Langlands.Induction
open Langlands.CompactAction.LocallyConstantModule

section Reduction

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (ℓ : ℕ) (I : Type uI)

/-- The regular representation of `G` on locally constant functions with coefficients `I →₀ R`,
as an object of `Rep R G`. It is smooth when `G` is compact; no smoothness is asserted for a
general topological group `G`. -/
abbrev regularRep : Rep.{max uG uI uR} R G :=
  Rep.of (regularRepresentation R (I →₀ R))

variable (m : ℕ)

/-- Reduction modulo `ℓ ^ m` of the coefficients, `I →₀ R → I →₀ R ⧸ (ℓ ^ m)`. -/
abbrev finsuppReduction : (I →₀ R) →ₗ[R] (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}) :=
  Finsupp.mapRange.linearMap (Ideal.Quotient.mkₐ R (Ideal.span {((ℓ : R) ^ m)})).toLinearMap

/-- Reduction modulo `ℓ ^ m` of the values, as a morphism from the regular representation with
coefficients `I →₀ R` to the one with coefficients `I →₀ R ⧸ (ℓ ^ m)`. -/
def regularReduction :
    regularRep R G I ⟶ Rep.of (regularRepresentation R (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)})) :=
  Rep.ofHom ⟨LocallyConstant.mapₗ R (finsuppReduction R ℓ I m), fun _ =>
    LinearMap.ext fun _ => LocallyConstant.ext fun _ => rfl⟩

theorem regularReduction_hom_apply (f : LocallyConstant G (I →₀ R)) (x : G) :
    (regularReduction R G ℓ I m).hom f x = finsuppReduction R ℓ I m (f x) :=
  rfl

/-- Reduction of the values is surjective: a locally constant function with values in
`I →₀ R ⧸ (ℓ ^ m)` lifts through a choice of preimages of its values. -/
theorem regularReduction_surjective : Function.Surjective (regularReduction R G ℓ I m).hom := by
  have hq : Function.Surjective (finsuppReduction R ℓ I m) :=
    Finsupp.mapRange_surjective _ (map_zero _) (Ideal.Quotient.mkₐ_surjective R _)
  intro f
  exact ⟨f.map (Function.surjInv hq), LocallyConstant.ext fun x => Function.surjInv_eq hq (f x)⟩

/-- A locally constant function whose reduction modulo `ℓ ^ m` vanishes is `ℓ ^ m` times a
locally constant function: divide each coefficient of each value by `ℓ ^ m` with `powDiv`. -/
theorem exists_pow_smul_of_regularReduction_eq_zero {f : LocallyConstant G (I →₀ R)}
    (hf : (regularReduction R G ℓ I m).hom f = 0) : ∃ g, ((ℓ : R) ^ m) • g = f := by
  have hc : ∀ x i, f x i ∈ Ideal.span {((ℓ : R) ^ m)} := fun x i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact congrArg (fun φ : LocallyConstant G (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}) => φ x i) hf
  refine ⟨f.map (Finsupp.mapRange (powDiv ℓ m) (powDiv_zero ℓ m)),
    LocallyConstant.ext fun x => Finsupp.ext fun i => ?_⟩
  change (ℓ : R) ^ m * powDiv ℓ m (f x i) = f x i
  exact pow_mul_powDiv ℓ m (hc x i)

/-- Multiplication by `ℓ ^ m` followed by reduction modulo `ℓ ^ m` is zero. -/
theorem powSMul_comp_regularReduction :
    powSMul ℓ m (regularRep R G I) ≫ regularReduction R G ℓ I m = 0 := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  change (regularReduction R G ℓ I m).hom ((powSMul ℓ m (regularRep R G I)).hom f) = 0
  rw [powSMul_hom_apply]
  refine LocallyConstant.ext fun x => Finsupp.ext fun i => ?_
  change Ideal.Quotient.mk _ ((ℓ : R) ^ m * f x i) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- The short complex formed by multiplication by `ℓ ^ m` on the regular representation with
coefficients `I →₀ R` and reduction modulo `ℓ ^ m` of the values. -/
abbrev regularReductionComplex : ShortComplex (Rep.{max uG uI uR} R G) :=
  ShortComplex.mk (powSMul ℓ m (regularRep R G I)) (regularReduction R G ℓ I m)
    (powSMul_comp_regularReduction R G ℓ I m)

/-- The short complex `regularReductionComplex R G ℓ I m` is exact. -/
theorem regularReductionComplex_exact : (regularReductionComplex R G ℓ I m).Exact := by
  apply ((regularReductionComplex R G ℓ I m).exact_map_iff_of_faithful
    (forget₂ (Rep.{max uG uI uR} R G) (ModuleCat.{max uG uI uR} R))).mp
  refine (ShortComplex.moduleCat_exact_iff _).mpr fun x hx => ?_
  obtain ⟨y, hy⟩ := exists_pow_smul_of_regularReduction_eq_zero R G ℓ I m hx
  refine ⟨y, ?_⟩
  change (powSMul ℓ m (regularRep R G I)).hom y = x
  rw [powSMul_hom_apply]
  exact hy

instance : Epi (regularReduction R G ℓ I m) :=
  (Rep.epi_iff_surjective _).mpr (regularReduction_surjective R G ℓ I m)

/-- The cokernel of multiplication by `ℓ ^ m` on the regular representation with coefficients
`I →₀ R` is, through reduction of the values, the regular representation with coefficients
`I →₀ R ⧸ (ℓ ^ m)`. -/
def cokernelRegularIso :
    cokernel (powSMul ℓ m (regularRep R G I)) ≅
      Rep.of (regularRepresentation R (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)})) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (regularReductionComplex_exact R G ℓ I m).gIsCokernel

/-- The projection to the cokernel followed by `cokernelRegularIso` is reduction of the
values. -/
theorem cokernelπ_cokernelRegularIso_hom :
    cokernel.π (powSMul ℓ m (regularRep R G I)) ≫ (cokernelRegularIso R G ℓ I m).hom =
      regularReduction R G ℓ I m :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

omit [Group G] [IsTopologicalGroup G] in
variable {ℓ} in
/-- If `ℓ` is a non-zero-divisor in `R`, it is a non-zero-divisor on the locally constant
functions `G → I →₀ R`. -/
theorem isSMulRegular_regular (hℓ : IsSMulRegular R (ℓ : R)) :
    IsSMulRegular (LocallyConstant G (I →₀ R)) (ℓ : R) := fun _ _ h =>
  LocallyConstant.ext fun x => Finsupp.ext fun i =>
    hℓ (congrArg (fun φ : LocallyConstant G (I →₀ R) => φ x i) h)

variable {ℓ} in
/-- If `ℓ` is a non-zero-divisor in `R`, multiplication by `ℓ` on the regular representation
with coefficients `I →₀ R` is a monomorphism in `Rep R G`. -/
theorem mono_powSMul_regular (hℓ : IsSMulRegular R (ℓ : R)) :
    Mono (powSMul ℓ 1 (regularRep R G I)) :=
  (mono_powSMul_one_iff_isSMulRegular ℓ _).mpr (isSMulRegular_regular R G I hℓ)

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- For a profinite group `G`, the cokernel of multiplication by `ℓ ^ m` on the smooth regular
representation with coefficients `I →₀ R` is a direct limit of free
`(R ⧸ (ℓ ^ m))[G ⧸ N]`-modules, `N` running over the open normal subgroups of `G`. -/
theorem isFreeLimit_cokernel_powSMul_regular :
    IsFreeLimit (cokernel (powSMul ℓ m (regularRep R G I))).ρ (R ⧸ Ideal.span {((ℓ : R) ^ m)})
      (fun N : OpenNormalSubgroup G => N.toSubgroup) :=
  (isFreeLimit_regular R G (R ⧸ Ideal.span {((ℓ : R) ^ m)}) I).of_equiv
    (Representation.equivOfIso (cokernelRegularIso R G ℓ I m))

/-- **An actual `ℓ`-divisible system of direct limits of free modules.** For a profinite group
`G` and `ℓ` a non-zero-divisor in `R`, every level of the reduction system
`m ↦ L / ℓ ^ m L` of the smooth regular representation `L` with coefficients `I →₀ R` is a
direct limit of free `(R ⧸ (ℓ ^ m))[G ⧸ N]`-modules over the open normal subgroups `N`. -/
theorem isFreeLimit_reductionSystem_regular [Mono (powSMul ℓ 1 (regularRep R G I))] :
    IsFreeLimit ((reductionSystem ℓ (regularRep R G I)).obj m).ρ
      (R ⧸ Ideal.span {((ℓ : R) ^ m)}) (fun N : OpenNormalSubgroup G => N.toSubgroup) :=
  isFreeLimit_cokernel_powSMul_regular R G ℓ I m

end Reduction

section HomSystem

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {ℓ : ℕ} (I : Type uI)
  [Mono (powSMul ℓ 1 (regularRep R G I))]
  (K : Subgroup G) [K.Normal] (hKo : IsOpen (K : Set G))

omit [TotallyDisconnectedSpace G] [K.Normal] in
include hKo in
/-- For an open subgroup `K` of the compact group `G` and an open normal subgroup `N` of `G`,
`N ⊓ K` has finite index in `K`. -/
theorem finiteIndex_openNormalSubgroup_subgroupOf (N : OpenNormalSubgroup G) :
    (N.toSubgroup.subgroupOf K).FiniteIndex :=
  finiteIndex_subgroupOf_of_isCompact N.isOpen' (K.isClosed_of_isOpen hKo).isCompact

variable (hTK : ∀ {m' m : ℕ} (h : m' ≤ m), Epi ((Rep.quotientToInvariantsFunctor R K).map
    ((reductionSystem ℓ (regularRep R G I)).projection h)))
  (W : DivisibleSystem (Rep.{max uG uI uR} R (G ⧸ K)) ℓ)

include hKo in
/-- Harris 1999, p.312, the maps (4.10.3) for the reduction system `T` of the smooth regular
representation of a profinite group and an open normal subgroup `K`: the transitions of
`m ↦ Hom((T m)^K, W m)` are surjective. -/
theorem regular_invariants_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective ((homSystem R ((reductionSystem ℓ (regularRep R G I)).mapLeftExact
      (Rep.quotientToInvariantsFunctor R K) hTK) W).map φ) :=
  isFreeLimit_invariants_homSystem_map_surjective _ _
    (fun m => isFreeLimit_reductionSystem_regular R G ℓ I m) K
    (exists_le_of_isOpen (openNormalSubgroup_shrink G) hKo)
    (fun N _ => finiteIndex_openNormalSubgroup_subgroupOf K hKo N) hTK W φ

include hKo in
/-- The inverse system `m ↦ Hom((T m)^K, W m)` satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_regular_invariants_homSystem :
    (homSystem R ((reductionSystem ℓ (regularRep R G I)).mapLeftExact
      (Rep.quotientToInvariantsFunctor R K) hTK) W ⋙ CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_isFreeLimit_invariants_homSystem _ _
    (fun m => isFreeLimit_reductionSystem_regular R G ℓ I m) K
    (exists_le_of_isOpen (openNormalSubgroup_shrink G) hKo)
    (fun N _ => finiteIndex_openNormalSubgroup_subgroupOf K hKo N) hTK W

variable {p : ℕ} (hp : p.Prime) (hR : IsUnit (p : R))
  (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup))

include hKo hp hR hK in
/-- For `K` open normal and pro-`p`, with `p` invertible in `R`, `invariantsToCoinvariants` is
bijective for `K` at every level of the reduction system of the smooth regular
representation. -/
theorem bijective_invariantsToCoinvariants_reductionSystem_regular (m : ℕ) :
    Function.Bijective (invariantsToCoinvariants
      ((reductionSystem ℓ (regularRep R G I)).obj m).ρ K) :=
  have : CompactSpace K := isCompact_iff_compactSpace.mp (K.isClosed_of_isOpen hKo).isCompact
  (isFreeLimit_reductionSystem_regular R G ℓ I m).bijective_invariantsToCoinvariants_of_isProP
    (fun N => N.isOpen') (openNormalSubgroup_shrink G) hp hR K hKo hK

include hKo hp hR hK in
/-- Harris 1999, p.312, for the reduction system `T` of the smooth regular representation and an
open normal pro-`p` subgroup `K`: the transitions of `m ↦ Hom(T m, Inf (W m))` are surjective.
The hypothesis of `mapLeftExact` is supplied by
`bijective_invariantsToCoinvariants_reductionSystem_regular`. -/
theorem regular_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective ((homSystem R (reductionSystem ℓ (regularRep R G I))
      (W.map (Rep.resFunctor (QuotientGroup.mk' K)))).map φ) :=
  have : CompactSpace K := isCompact_iff_compactSpace.mp (K.isClosed_of_isOpen hKo).isCompact
  isFreeLimit_homSystem_map_surjective _ _ (fun m => isFreeLimit_reductionSystem_regular R G ℓ I m) K
    (exists_le_of_isOpen (openNormalSubgroup_shrink G) hKo)
    (fun N _ => finiteIndex_openNormalSubgroup_subgroupOf K hKo N)
    (fun N _ => isUnit_index_subgroupOf hp hR N.isOpen' hK)
    (epi_quotientToInvariantsFunctor_map_projection R K _
      (bijective_invariantsToCoinvariants_reductionSystem_regular I K hKo hp hR hK)) W φ

include hKo hp hR hK in
/-- The inverse system `m ↦ Hom(T m, Inf (W m))` satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_regular_homSystem :
    (homSystem R (reductionSystem ℓ (regularRep R G I))
      (W.map (Rep.resFunctor (QuotientGroup.mk' K))) ⋙ CategoryTheory.forget _).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective _ fun _ _ φ =>
    regular_homSystem_map_surjective I K hKo W hp hR hK φ

end HomSystem

end Langlands.Cohomology.DivisibleSystem
