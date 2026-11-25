module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The shared tame extension and the all-perfect-core family

The constructed shared Kummer extension of the tame case, the input preparation for shared
residue absorption in the all-perfect-core (constant-numerator) family, and the normalization to
base-origin coefficients modulo `pi ^ N`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

/-! ### Constructing the shared extension in the tame case -/

section SharedTame

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [IsScalarTower A R K₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Module.Finite L (E i)]

end SharedTame

-- A shared-`K₂` construction by adjoining an exact `p ^ r`-th root of a uniformizer does not
-- work.  In residue characteristic `p` the
-- ambient field has `char K₁ = p`, so `X ^ (p ^ r) - π₁` has zero derivative and `K₁(π₁^{1/p^r})`
-- is purely inseparable over `K₁`.  Every prescribed solver the wild route ends in carries
-- `[Algebra.IsSeparable K E]` — `exists_isWeakSolution_of_baseChanged_artinSchreier_residue`
-- among them — so an exact `p ^ r`-th root can never feed it: the unit correction in
-- `exists_baseChanged_laurent_reduction` is essential, not cosmetic.  The separable construction
-- is `IsDiscreteValuationRing.exists_isGalois_totallyRamified_orbitExtension_forall_depth`, whose
-- orbit relation `∏ v : V, (α - algebraMap A K₁ v) = algebraMap A K₁ π` with deeply `π`-divisible
-- `v` yields `α ^ (p ^ rank) = π · u` with `u ≡ 1`, via `pow_card_sub_mem_span_pow_of_prod_eq`;
-- its shared parameters come from `exists_shared_orbit_parameters`.

/-! ### The all-perfect-core family: input preparation for shared residue absorption

`exists_prepared_wild_laurent_of_charP` (the wild preparation of a degree-`p` layer) returns a wild
set `J` and, off it, the statement that each Laurent coefficient is a `p ^ m`-th power for
**every** `m`.  When `J` is empty that covers the whole range: every coefficient lies in the
perfect core of the member's own residue field.  This is Epp's **constant-numerator** branch, and
it is a different endgame, not a degenerate case of the wild one — the wild construction is driven
throughout by a coefficient possessing a *terminal* root, one that is not itself a `p`-th power,
and a perfect-core coefficient has none at any depth.

The branch's intended shape, with the quantifier order it must have:

1. one shared weakly unramified base change `R → R₂` absorbing **every** member's coefficients at
   one depth, giving their `p ^ N`-th roots in `κ_{R₂}` read in any common residue overfield;
2. hence, at every member, a Laurent presentation whose numerator is *constant* — defined over the
   base rather than over the member;
3. hence one Artin--Schreier extension `K₂` of the **base** field, obtained from the finitely many
   base numerators, over which every member's layer becomes weakly unramified.

Step 1 exists as
`EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`,
proved from Epp's condition at every member.  It takes the depth `N` as a free input and the
coefficients as a **`Finset` per member**, with the proof that each of their elements lies in
the perfect core.  It lives in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption`, which this module does
not import; nothing below depends on it, and what is below is the data it consumes.

**What this section proves is step 1's input, and nothing else.**  Steps 2 and 3 are not proved,
here or anywhere in the tree.  Step 3 in particular is where the base residue field is genuinely
interrogated and where the one shared `K₂` would have to be produced, and it is the remaining
obligation of the whole wild case.  No claim is made that
the constant-numerator branch follows from what is here. -/

section ConstantNumerator

end ConstantNumerator

/-! ### Step 2: normalization to base-origin coefficients modulo `pi ^ N` -/

section Normalization

/-- The transported section: residue and truncation compatibilities along a local ring map. -/
private theorem residue_mk_algebraMap_sigma
    {F B S : Type*} [Field F] [CommRing B] [IsLocalRing B]
    [CommRing S] [IsLocalRing S] [Algebra B S] [IsLocalHom (algebraMap B S)]
    (N : ℕ) (f : F →+* IsLocalRing.ResidueField B) (sigma : F → B)
    (hsigma : ∀ x, IsLocalRing.residue B (sigma x) = f x)
    (sq : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hsq : ∀ x, Ideal.Quotient.mk _ (sigma x) = sq x) (x : F) :
    IsLocalRing.residue S (algebraMap B S (sigma x)) =
      IsLocalRing.ResidueField.map (algebraMap B S) (f x) ∧
    Ideal.Quotient.mk _ (algebraMap B S (sigma x)) =
      IsDiscreteValuationRing.truncationMap B S N (sq x) :=
  ⟨by rw [← IsLocalRing.ResidueField.map_residue, hsigma],
    by rw [← hsq, IsDiscreteValuationRing.truncationMap_mk]⟩

/-- **A Laurent expansion transports through a compatible factor square.**

This is the field-level half of re-entry.  The coefficients and integral term are mapped through
the lower ring map, while the parameter is mapped through the fraction-field map; compatibility of
the square identifies the two resulting expressions. -/
theorem laurent_expansion_map
    {B S L E : Type*} [CommRing B] [CommRing S] [Field L] [Field E]
    [Algebra B S] [Algebra B L] [Algebra S E] [Algebra L E]
    (hB : ∀ x : B, algebraMap L E (algebraMap B L x) =
      algebraMap S E (algebraMap B S x))
    (t : B) (tS : S) (ht : algebraMap B S t = tS)
    (N : ℕ) (sigma : ℕ → B) (b : B) (xi : L)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (sigma k) *
        (algebraMap B L t)⁻¹ ^ (N - k)) + algebraMap B L b) :
    algebraMap L E xi = (∑ k ∈ Finset.range N,
      algebraMap S E (algebraMap B S (sigma k)) *
        (algebraMap S E tS)⁻¹ ^ (N - k)) +
          algebraMap S E (algebraMap B S b) := by
  rw [hexp, map_add, map_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by rw [map_mul, map_pow, map_inv₀, hB, hB, ht]
  · exact hB b

/-- **Re-entry transports all data consumed by constant-Laurent normalization.**

The original coefficient section and its truncated ring homomorphism are transported to the
post-base-change factor, the Laurent identity is mapped through the factor square, and a root from
the new base residue field is identified with the transported original coefficient root. -/
theorem exists_transported_constant_laurent_data
    {A F B S L E : Type*} [CommRing A] [IsLocalRing A] [Field F]
    [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Field L] [Field E]
    [Algebra A S] [IsLocalHom (algebraMap A S)]
    [Algebra B S] [IsLocalHom (algebraMap B S)]
    [Algebra B L] [Algebra S E] [Algebra L E]
    (hB : ∀ x : B, algebraMap L E (algebraMap B L x) =
      algebraMap S E (algebraMap B S x))
    (p N : ℕ) (tA : A) (tB : B) (ht : algebraMap B S tB = algebraMap A S tA)
    (f : F →+* IsLocalRing.ResidueField B) (sigma : F → B)
    (hsigma : ∀ x, IsLocalRing.residue B (sigma x) = f x)
    (sq : F →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hsq : ∀ x, Ideal.Quotient.mk _ (sigma x) = sq x)
    (coeff rootCoeff : ℕ → F)
    (hrootCoeff : ∀ k, k ∈ Finset.range N → rootCoeff k ^ (p ^ N) = coeff k)
    (rootBase : ℕ → IsLocalRing.ResidueField A)
    (hrootBase : ∀ k, k ∈ Finset.range N →
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) (rootBase k) =
        IsLocalRing.ResidueField.map (algebraMap B S) (f (rootCoeff k)))
    (xi : L) (b : B)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (sigma (coeff k)) * (algebraMap B L tB)⁻¹ ^ (N - k)) +
        algebraMap B L b) :
    ∃ (fS : F →+* IsLocalRing.ResidueField S) (sigmaS : F → S)
      (sqS : F →+* S ⧸ (IsLocalRing.maximalIdeal S) ^ N),
      (∀ x, IsLocalRing.residue S (sigmaS x) = fS x) ∧
      (∀ x, Ideal.Quotient.mk _ (sigmaS x) = sqS x) ∧
      (∀ k, k ∈ Finset.range N →
        rootCoeff k ^ (p ^ N) = coeff k) ∧
      (∀ k, k ∈ Finset.range N →
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField S) (rootBase k) =
          fS (rootCoeff k)) ∧
      algebraMap L E xi = (∑ k ∈ Finset.range N,
        algebraMap S E (sigmaS (coeff k)) *
          (algebraMap S E (algebraMap A S tA))⁻¹ ^ (N - k)) +
            algebraMap S E (algebraMap B S b) := by
  have h := residue_mk_algebraMap_sigma (S := S) N f sigma hsigma sq hsq
  exact ⟨(IsLocalRing.ResidueField.map (algebraMap B S)).comp f, fun x => algebraMap B S (sigma x),
    (IsDiscreteValuationRing.truncationMap B S N).comp sq,
    fun x => (h x).1, fun x => (h x).2, hrootCoeff, hrootBase,
    laurent_expansion_map hB tB (algebraMap A S tA) ht N (fun k => sigma (coeff k)) b xi hexp⟩

/-- **Family normalization from roots compared in the post-base-change residue fields.**

This is the all-conjugate form of
`IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField`.
For member `i`, `F i` is the original coefficient residue field and `S i` is the re-entered
conjugate DVR.  The chosen coefficient lifts `σ i` and their truncated ring homomorphisms have
been transported from the original DVR to `S i`; no section of the whole residue field of `S i`
is required.

Each coefficient has a root `rootCoeff i k` in `F i`.  Normal residue absorption supplies a root
`rootBase i k` in the one shared base residue field, and `hrootBase` identifies their images in
the residue field of the re-entered member.  The one-coefficient normalization theorem then
produces an element of the shared base ring congruent to the transported coefficient lift modulo
the common depth.  Finite choice packages these elements for the whole family at once. -/
theorem exists_forall_coeffLift_sub_algebraMap_mem_pow_of_residueField
    {ι : Type*} {R2 : Type*} {F S : ι → Type*}
    [CommRing R2] [IsLocalRing R2]
    [∀ i, Field (F i)] [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R2 (S i)] [∀ i, IsLocalHom (algebraMap R2 (S i))]
    (p : ℕ) [Fact p.Prime] [∀ i, CharP (S i) p] (N : ℕ)
    (f : ∀ i, F i →+* IsLocalRing.ResidueField (S i))
    (σ : ∀ i, F i → S i)
    (hσ : ∀ i x, IsLocalRing.residue (S i) (σ i x) = f i x)
    (sq : ∀ i, F i →+* S i ⧸ (IsLocalRing.maximalIdeal (S i)) ^ N)
    (hsq : ∀ i x, Ideal.Quotient.mk _ (σ i x) = sq i x)
    (n : ι → ℕ) (coeff rootCoeff : ∀ i, ℕ → F i)
    (hrootCoeff : ∀ i k, k ∈ Finset.range (n i) →
      rootCoeff i k ^ (p ^ N) = coeff i k)
    (rootBase : ι → ℕ → IsLocalRing.ResidueField R2)
    (hrootBase : ∀ i k, k ∈ Finset.range (n i) →
      algebraMap (IsLocalRing.ResidueField R2)
          (IsLocalRing.ResidueField (S i)) (rootBase i k) = f i (rootCoeff i k)) :
    ∃ base : ι → ℕ → R2, ∀ i k, k ∈ Finset.range (n i) →
      σ i (coeff i k) - algebraMap R2 (S i) (base i k) ∈
        (IsLocalRing.maximalIdeal (S i)) ^ N := by
  have h : ∀ i, ∀ k ∈ Finset.range (n i), ∃ a₀ : R2,
      σ i (coeff i k) - algebraMap R2 (S i) a₀ ∈ (IsLocalRing.maximalIdeal (S i)) ^ N :=
    fun i k hk =>
      IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField
        p N (f i) (σ i) (hσ i) (sq i) (hsq i) (coeff i k) (rootCoeff i k)
        (hrootCoeff i k hk) (rootBase i k) (hrootBase i k hk)
  choose! base hbase using h
  exact ⟨base, hbase⟩

/-- **The all-conjugate constant-parameter normalization.**

After normal residue absorption, each transported Laurent coefficient has a `p ^ N`-th root
coming from the shared base residue field.  The preceding theorem upgrades that residue equality
to congruence modulo the `N`-th power of the factor's maximal ideal.  Since the factor is weakly
unramified over the shared base, the image of a base uniformizer is again a uniformizer; hence the
congruence is exactly modulo its `N`-th power.  The Laurent principal part therefore differs from
one defined over the shared fraction field only by an integral element.

The conclusion is the input shape of the split-constant-class solver, simultaneously for every
conjugate factor.  In particular, no transported minimality statement is required. -/
theorem exists_forall_base_parameter_add_integral_of_constant_laurent
    {iota : Type*} {R K : Type*} {F S L : iota → Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [∀ i, Field (F i)] [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)] [∀ i, Field (L i)]
    [∀ i, Algebra R (S i)] [∀ i, IsDiscreteValuationRing.IsExtension R (S i)]
    [∀ i, Algebra R (L i)] [∀ i, Algebra (S i) (L i)] [∀ i, Algebra K (L i)]
    [∀ i, IsScalarTower R (S i) (L i)] [∀ i, IsScalarTower R K (L i)]
    (p : ℕ) [Fact p.Prime] [∀ i, CharP (S i) p] (N : ℕ)
    (pi : R) (hpi : Irreducible pi)
    (hweak : ∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (S i))
    (f : ∀ i, F i →+* IsLocalRing.ResidueField (S i))
    (sigma : ∀ i, F i → S i)
    (hsigma : ∀ i x, IsLocalRing.residue (S i) (sigma i x) = f i x)
    (sq : ∀ i, F i →+* (S i) ⧸ (IsLocalRing.maximalIdeal (S i)) ^ N)
    (hsq : ∀ i x, Ideal.Quotient.mk _ (sigma i x) = sq i x)
    (coeff rootCoeff : ∀ i, ℕ → F i)
    (hrootCoeff : ∀ i k, k ∈ Finset.range N →
      rootCoeff i k ^ (p ^ N) = coeff i k)
    (rootBase : iota → ℕ → IsLocalRing.ResidueField R)
    (hrootBase : ∀ i k, k ∈ Finset.range N →
      algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (S i)) (rootBase i k) = f i (rootCoeff i k))
    (xi : ∀ i, L i) (b : ∀ i, S i)
    (hexp : ∀ i, xi i = (∑ k ∈ Finset.range N,
      algebraMap (S i) (L i) (sigma i (coeff i k)) *
        (algebraMap (S i) (L i) (algebraMap R (S i) pi))⁻¹ ^ (N - k)) +
          algebraMap (S i) (L i) (b i)) :
    ∃ (xi0 : iota → K) (b' : ∀ i, S i), ∀ i,
      xi i = algebraMap K (L i) (xi0 i) + algebraMap (S i) (L i) (b' i) := by
  classical
  obtain ⟨base, hbase⟩ :=
    exists_forall_coeffLift_sub_algebraMap_mem_pow_of_residueField
      p N f sigma hsigma sq hsq (fun _ => N) coeff rootCoeff hrootCoeff rootBase hrootBase
  have h : ∀ i, ∃ (c : K) (d : S i),
      xi i = algebraMap K (L i) c + algebraMap (S i) (L i) d := by
    intro i
    have hpiS : Irreducible (algebraMap R (S i) pi) :=
      IsDiscreteValuationRing.irreducible_algebraMap_of_isWeaklyUnramified (hweak i) hpi
    have hpow : (IsLocalRing.maximalIdeal (S i)) ^ N =
        Ideal.span {algebraMap R (S i) pi ^ N} := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hpiS,
        Ideal.span_singleton_pow]
    have ht : algebraMap R (L i) pi ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R K (L i)]
      simpa only [map_zero] using (algebraMap K (L i)).injective.ne
        ((IsFractionRing.injective R K).ne hpi.ne_zero)
    exact IsDiscreteValuationRing.exists_base_parameter_add_integral_of_coefficients_lift
      pi ht N (fun k => sigma i (coeff i k)) (b i) (xi i) (base i) (hexp i)
        (fun k hk => by rw [← hpow]; exact hbase i k hk)
  choose xi0 b' hxi using h
  exact ⟨xi0, b', hxi⟩

end Normalization

end Stacks.EppTheorem

end
