import Langlands.Representation.Induction.InvariantRestriction
import Langlands.Representation.Induction.PermutationDual
import Langlands.Cohomology.DivisibleSystem.InvariantHomSurjective
import Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective
import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.EquivalencePullback

/-!
# Direct limits of free modules over quotient group algebras

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ.
39-2 (1999), §2, printed p.306: "When we replace `H` by a subgroup `H'` which is normal in
`S(e)`, we obtain a natural isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`. Taking the direct limit as
`H` shrinks to the identity, we obtain an `ℓ`-divisible system of complexes `C_m^•` of
projective `ℤ/ℓ^mℤ[S(e)]`-modules"; proof of Proposition 4.10, printed pp.311-312: "Recall that
`C^j(ẽ)` has been chosen to be a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)`
varies over a family of open subgroups of `S(ẽ)`. We may replace `C^j_m(ẽ)` by
`C^j_m(ẽ)^{H_p}` in (4.10.2)." and "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are
both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all
`m`."

This module formalizes the coefficient modules of that sentence and derives from them the two
hypotheses that the published modules `InvariantHomSystem`, `InvariantHomSurjective` and
`FreeTorsionProjective` keep explicit: bijectivity of `invariantsToCoinvariants` (under which
`Hom(C, Inf W) = Hom(C^K, W)`, Harris's replacement of `C^j_m(ẽ)` by its invariants) and
freeness of the invariants over `(R ⧸ (ℓ ^ m))[G ⧸ K]`.

For a representation `ρ` of a group `G` on an `R`-module, an `R`-algebra `k` and a normal
subgroup `H`:

* `IsFreeOnInvariants ρ k H`: the `H`-invariants of `ρ`, as a representation of `G ⧸ H` over
  `R`, are a free `k[G ⧸ H]`-module, written as the permutation representation of `G ⧸ H` on
  itself with coefficients `I →₀ k`, that is `⊕_I k[G ⧸ H]`;
* `IsFreeLimit ρ k H` for a family `H : ι → Subgroup G` of normal subgroups: the family is
  directed downwards, every vector is invariant under some `H i`, and every `ρ^{H i}` is a free
  `k[G ⧸ H i]`-module. As `ρ^{H i} ⊆ ρ^{H j}` when `H j ≤ H i`, `ρ` is then the directed union
  of the free modules `ρ^{H i}`, their direct limit along the inclusions.

Results:

* `invariantsInvariantsEquiv`, `permutationQuotientEquiv`: `ρ^K = (ρ^H)^K` for `H ≤ K`, and the
  permutation representation of `G ⧸ K` on itself pulled back to `G` is that of `G` on `G ⧸ K`;
* `IsFreeOnInvariants.of_le`, `IsFreeLimit.isFreeOnInvariants`: freeness passes from `H` to a
  normal `K ⊇ H` in which `H` has finite index (with the published `permutationInvariantsEquiv`);
* `IsFreeOnInvariants.bijective_invariantsToCoinvariants`,
  `bijective_invariantsToCoinvariants_of_directed`, `IsFreeLimit.bijective_invariantsToCoinvariants`:
  `invariantsToCoinvariants` is bijective for `K` on `ρ` when some `H i ≤ K` and the indices
  `[K : H i]` for `H i ≤ K` are finite units of `R`; on each `ρ^{H i}` this is the published
  `bijective_invariantsToCoinvariants_permutation`, and the directed-union argument passes it to
  `ρ`;
* `IsFreeOnInvariants.free_asModule`: for `k = R` the invariants are free over `R[G ⧸ H]`;
* for a topological group: `directed_of_shrink`, `exists_le_of_isOpen`, `exhaustive_of_isSmooth`,
  `IsFreeLimit.of_isSmooth` (a family of open subgroups shrinking to the identity is directed and
  exhausts a smooth representation), `IsFreeLimit.isFreeOnInvariants_of_isOpen` and
  `IsFreeLimit.bijective_invariantsToCoinvariants_of_isProP` (`K` open, compact, with
  `p`-group quotients by open normal subgroups, `p` a prime invertible in `R`);
* `freeOverPowQuotient_of_equiv_permutation`, `freeOverPowQuotient_quotientToInvariants`: with
  `k = R ⧸ (ℓ ^ m)`, freeness of the `K`-invariants gives the published
  `FreeOverPowQuotient ℓ m`;
* for an `ℓ`-divisible system `T` of representations whose level `m` is `IsFreeLimit` with
  `k = R ⧸ (ℓ ^ m)`: `bijective_invariantsToCoinvariants_of_isFreeLimit`,
  `freeOverPowQuotient_invariants_of_isFreeLimit`, surjectivity of the transitions, the
  Mittag-Leffler condition and the extension of morphisms for `m ↦ Hom((T m)^K, W m)`
  (`isFreeLimit_invariants_homSystem_map_surjective`,
  `isMittagLeffler_isFreeLimit_invariants_homSystem`,
  `isFreeLimit_invariants_towerHomEval_surjective`) and for `m ↦ Hom(T m, Inf (W m))`
  (`isFreeLimit_homSystem_map_surjective`, `isMittagLeffler_isFreeLimit_homSystem`, through the
  published `invariantsHomSystemIso`); `isFreeLimit_degree_*` are the same statements for the
  degree `j` terms of an `ℓ`-divisible system of complexes.

In our reading `K` plays the role of `S(ẽ) ∩ H_p`, the family `H` that of the subgroups
`H(ẽ)`, normal as freeness over `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]` requires, and `T` that of `m ↦ C^j_m(ẽ)`.
Harris's complexes `C_m^•` are not constructed, it is not proved that they satisfy
`IsFreeLimit`, and his projectivity claim on p.306 is not formalized. The definitions, the
correspondence and the proofs are ours.
-/

noncomputable section

namespace Langlands.Induction

universe uR uk uG uV uW uI uι

section Invariants

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R G V)

/-- The representation of `G` on the `H`-invariants of `ρ`, for a normal subgroup `H`: the
representation `ρ.quotientToInvariants H` of `G ⧸ H` pulled back to `G`. -/
abbrev invariantsInflation (H : Subgroup G) [H.Normal] :
    Representation R G (Representation.invariants (ρ.comp H.subtype)) :=
  (ρ.quotientToInvariants H).comp (QuotientGroup.mk' H)

/-- Invariants under a larger subgroup are invariants under a smaller one. -/
theorem mem_invariants_of_le {H H' : Subgroup G} (hH : H' ≤ H) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp H.subtype)) :
    v ∈ Representation.invariants (ρ.comp H'.subtype) :=
  fun h => hv ⟨h.1, hH h.2⟩

/-- For normal subgroups `H ≤ K`, the `K`-invariants of `ρ` are the `K`-invariants of the
representation of `G` on the `H`-invariants of `ρ`, as representations of `G ⧸ K`. -/
def invariantsInvariantsEquiv {H K : Subgroup G} [H.Normal] [K.Normal] (hHK : H ≤ K) :
    (ρ.quotientToInvariants K).Equiv ((invariantsInflation ρ H).quotientToInvariants K) :=
  .mk
    { toFun := fun v => ⟨⟨v.1, mem_invariants_of_le ρ hHK v.2⟩, fun k => Subtype.ext (v.2 k)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun w => ⟨w.1.1, fun k => congrArg Subtype.val (w.2 k)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rfl

variable (R) in
/-- For a normal subgroup `K`, the permutation representation of `G ⧸ K` on itself, pulled back
to `G`, is the permutation representation of `G` on `G ⧸ K`. -/
def permutationQuotientEquiv (K : Subgroup G) [K.Normal] (M : Type*) [AddCommGroup M]
    [Module R M] :
    Representation.Equiv ((permutation R (G ⧸ K) (G ⧸ K) M).comp (QuotientGroup.mk' K))
      (permutation R G (G ⧸ K) M) :=
  .mk (LinearEquiv.refl R _) fun g => by
    refine LinearMap.ext fun φ => Finsupp.ext fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    change permutation R (G ⧸ K) (G ⧸ K) M (QuotientGroup.mk g) φ (QuotientGroup.mk y) =
      permutation R G (G ⧸ K) M g φ (QuotientGroup.mk y)
    rw [permutation_apply, permutation_apply, MulAction.Quotient.smul_mk]
    simp only [smul_eq_mul]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]

variable (k : Type uk) [CommRing k] [Algebra R k]

/-- Harris's "free `k[G ⧸ H]`-module", for the `H`-invariants of `ρ` and a normal subgroup
`H`: as a representation of `G ⧸ H` over `R`, `ρ^H` is the direct sum `⊕_I k[G ⧸ H]` of copies
of the group algebra, written as the permutation representation of `G ⧸ H` on itself with
coefficients `I →₀ k`, for some index type `I`. -/
def IsFreeOnInvariants (H : Subgroup G) [H.Normal] : Prop :=
  ∃ I : Type uV, Nonempty ((ρ.quotientToInvariants H).Equiv
    (permutation R (G ⧸ H) (G ⧸ H) (I →₀ k)))

variable {ρ k}

/-- If the `H`-invariants of `ρ` are a free `k[G ⧸ H]`-module, then for a normal subgroup
`K ⊇ H` in which `H` has finite index, the `K`-invariants are a free `k[G ⧸ K]`-module of the
same rank. -/
theorem IsFreeOnInvariants.of_le {H K : Subgroup G} [H.Normal] [K.Normal] (hHK : H ≤ K)
    [(H.subgroupOf K).FiniteIndex] (h : IsFreeOnInvariants ρ k H) :
    IsFreeOnInvariants ρ k K := by
  obtain ⟨I, ⟨e⟩⟩ := h
  exact ⟨I, ⟨(invariantsInvariantsEquiv ρ hHK).trans
    ((invariantsEquivOfEquiv K ((Langlands.Cohomology.HyperextAbutment.equivComp e
      (QuotientGroup.mk' H)).trans
      (permutationQuotientEquiv R H (I →₀ k)))).trans
      (permutationInvariantsEquiv R (I →₀ k) hHK))⟩⟩

/-- If the `H`-invariants of `ρ` are a free `k[G ⧸ H]`-module and the index of `H` in a normal
subgroup `K ⊇ H` is finite and a unit of `R`, then `invariantsToCoinvariants` is bijective for
the representation of `G` on the `H`-invariants. -/
theorem IsFreeOnInvariants.bijective_invariantsToCoinvariants {H K : Subgroup G} [H.Normal]
    [K.Normal] (hHK : H ≤ K) [(H.subgroupOf K).FiniteIndex]
    (hu : IsUnit ((H.subgroupOf K).index : R)) (h : IsFreeOnInvariants ρ k H) :
    Function.Bijective (invariantsToCoinvariants (invariantsInflation ρ H) K) := by
  obtain ⟨I, ⟨e⟩⟩ := h
  exact bijective_invariantsToCoinvariants_of_equiv K
    ((Langlands.Cohomology.HyperextAbutment.equivComp e (QuotientGroup.mk' H)).trans
      (permutationQuotientEquiv R H (I →₀ k)))
    (bijective_invariantsToCoinvariants_permutation hHK hu)

/-- With `k = R`: if `ρ^H` is a free `R[G ⧸ H]`-module in the sense of `IsFreeOnInvariants`,
then it is free as a module over the group algebra `R[G ⧸ H]`. -/
theorem IsFreeOnInvariants.free_asModule {H : Subgroup G} [H.Normal]
    (h : IsFreeOnInvariants ρ R H) :
    Module.Free (MonoidAlgebra R (G ⧸ H)) (ρ.quotientToInvariants H).asModule := by
  obtain ⟨I, ⟨e⟩⟩ := h
  have : Module.Free (MonoidAlgebra R (G ⧸ H)) (permutation R (G ⧸ H) (G ⧸ H) (I →₀ R)).asModule :=
    permutation_asModule_free (W := I →₀ R) (fun x => IsCancelSMul.stabilizer_eq_bot x)
  exact Module.Free.of_equiv (asModuleLinearEquiv e).symm

end Invariants

section DirectedUnion

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R G V)
  {ι : Type uι} (H : ι → Subgroup G) [∀ i, (H i).Normal] (K : Subgroup G) [K.Normal]

omit [∀ i, (H i).Normal] [K.Normal] in
/-- In a directed family of normal subgroups exhausting `V` by invariants, finitely many vectors
are invariant under a common member contained in `K`, if some member is contained in `K`. -/
theorem exists_le_forall_mem_invariants (hdir : ∀ i j, ∃ l, H l ≤ H i ⊓ H j)
    (hex : ∀ v : V, ∃ i, v ∈ Representation.invariants (ρ.comp (H i).subtype))
    (h0 : ∃ i, H i ≤ K) (s : Finset V) :
    ∃ i, H i ≤ K ∧ ∀ v ∈ s, v ∈ Representation.invariants (ρ.comp (H i).subtype) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨i, hi⟩ := h0
    exact ⟨i, hi, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  | insert a s _ ih =>
    obtain ⟨i, hiK, hi⟩ := ih
    obtain ⟨j, hj⟩ := hex a
    obtain ⟨l, hl⟩ := hdir i j
    refine ⟨l, (hl.trans inf_le_left).trans hiK, fun v hv => ?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact mem_invariants_of_le ρ (hl.trans inf_le_right) hj
    · exact mem_invariants_of_le ρ (hl.trans inf_le_left) (hi v hv)

/-- The inclusion of the `H`-invariants into `V`, as a map of representations of `K`. -/
def invariantsInflationInclusion (H' : Subgroup G) [H'.Normal] :
    Representation.IntertwiningMap ((invariantsInflation ρ H').comp K.subtype)
      (ρ.comp K.subtype) :=
  ⟨(Representation.invariants (ρ.comp H'.subtype)).subtype, fun _ => rfl⟩

/-- Let `ρ` be the directed union of its invariants under a directed family of normal subgroups
`H i`, some of which lies in `K`. If `invariantsToCoinvariants` is bijective for `K` on the
`H i`-invariants whenever `H i ≤ K`, then it is bijective for `K` on `ρ`. -/
theorem bijective_invariantsToCoinvariants_of_directed (hdir : ∀ i j, ∃ l, H l ≤ H i ⊓ H j)
    (hex : ∀ v : V, ∃ i, v ∈ Representation.invariants (ρ.comp (H i).subtype))
    (h0 : ∃ i, H i ≤ K)
    (hbij : ∀ i, H i ≤ K →
      Function.Bijective (invariantsToCoinvariants (invariantsInflation ρ (H i)) K)) :
    Function.Bijective (invariantsToCoinvariants ρ K) := by
  classical
  constructor
  · -- injectivity: a relation in the coinvariants involves finitely many vectors
    have key : ∀ x : Representation.invariants (ρ.comp K.subtype),
        invariantsToCoinvariants ρ K x = 0 → x = 0 := by
      intro x hx
      have hmem : x.1 ∈ Representation.Coinvariants.ker (ρ.comp K.subtype) :=
        (Representation.Coinvariants.mk_eq_zero _).mp hx
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
      obtain ⟨i, hiK, hi⟩ := exists_le_forall_mem_invariants ρ H K hdir hex h0
        (insert x.1 (c.support.image Prod.snd))
      have hx' : x.1 ∈ Representation.invariants (ρ.comp (H i).subtype) :=
        hi x.1 (Finset.mem_insert_self _ _)
      have hmap : x.1 ∈ (Representation.Coinvariants.ker
          ((invariantsInflation ρ (H i)).comp K.subtype)).map
          (Representation.invariants (ρ.comp (H i).subtype)).subtype := by
        rw [← hc]
        refine Submodule.sum_mem _ fun p hp => ?_
        have hp2 : p.2 ∈ Representation.invariants (ρ.comp (H i).subtype) :=
          hi p.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
        exact ⟨c p • ((invariantsInflation ρ (H i)) p.1 ⟨p.2, hp2⟩ - ⟨p.2, hp2⟩),
          Submodule.smul_mem _ _ (Representation.Coinvariants.sub_mem_ker _ _), rfl⟩
      obtain ⟨y, hy, hyx⟩ := hmap
      have hyK : y ∈ Representation.invariants
          ((invariantsInflation ρ (H i)).comp K.subtype) := fun k => by
        refine Subtype.ext ?_
        change ρ k y.1 = y.1
        rw [show y.1 = x.1 from hyx]
        exact x.2 k
      have h1 : invariantsToCoinvariants (invariantsInflation ρ (H i)) K ⟨y, hyK⟩ = 0 :=
        (Representation.Coinvariants.mk_eq_zero _).mpr hy
      have h2 : (⟨y, hyK⟩ : Representation.invariants
          ((invariantsInflation ρ (H i)).comp K.subtype)) = 0 :=
        (hbij i hiK).1 (h1.trans (map_zero _).symm)
      refine Subtype.ext ?_
      rw [← show y.1 = x.1 from hyx]
      exact congrArg (fun z => z.1.1) h2
    intro x y hxy
    have h := key (x - y) (by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp h
  · -- surjectivity: every class comes from some `H i`-invariants with `H i ≤ K`
    intro c
    obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
    obtain ⟨i, hiK, hi⟩ := exists_le_forall_mem_invariants ρ H K hdir hex h0 {w}
    have hw := hi w (Finset.mem_singleton_self w)
    obtain ⟨z, hz⟩ := (hbij i hiK).2 (Representation.Coinvariants.mk _ ⟨w, hw⟩)
    refine ⟨⟨z.1.1, fun k => congrArg Subtype.val (z.2 k)⟩, ?_⟩
    exact congrArg (Representation.Coinvariants.map _ _ (invariantsInflationInclusion ρ K (H i))) hz

end DirectedUnion

section FreeLimit

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R G V)
  (k : Type uk) [CommRing k] [Algebra R k]
  {ι : Type uι} (H : ι → Subgroup G) [∀ i, (H i).Normal]

/-- Harris's direct limit of free `k[G ⧸ H]`-modules as `H` varies over a family of normal
subgroups: the family `H` is directed downwards, every vector of `ρ` is invariant under some
`H i`, so that `ρ` is the directed union of its `H i`-invariants, and the `H i`-invariants are
a free `k[G ⧸ H i]`-module for every `i`. -/
structure IsFreeLimit : Prop where
  directed : ∀ i j, ∃ l, H l ≤ H i ⊓ H j
  exhaustive : ∀ v : V, ∃ i, v ∈ Representation.invariants (ρ.comp (H i).subtype)
  free : ∀ i, IsFreeOnInvariants ρ k (H i)

variable {ρ k H}

/-- For a normal subgroup `K` containing some `H i` with finite index, the `K`-invariants of a
direct limit of free modules are a free `k[G ⧸ K]`-module. -/
theorem IsFreeLimit.isFreeOnInvariants (hρ : IsFreeLimit ρ k H) {K : Subgroup G} [K.Normal]
    {i : ι} (hiK : H i ≤ K) [((H i).subgroupOf K).FiniteIndex] :
    IsFreeOnInvariants ρ k K :=
  (hρ.free i).of_le hiK

/-- For a normal subgroup `K` containing some `H i`, such that the index of every `H i ≤ K` in
`K` is finite and a unit of `R`, `invariantsToCoinvariants` is bijective for `K` on a direct
limit of free modules. -/
theorem IsFreeLimit.bijective_invariantsToCoinvariants (hρ : IsFreeLimit ρ k H)
    (K : Subgroup G) [K.Normal] (h0 : ∃ i, H i ≤ K)
    (hfin : ∀ i, H i ≤ K → ((H i).subgroupOf K).FiniteIndex)
    (hu : ∀ i, H i ≤ K → IsUnit (((H i).subgroupOf K).index : R)) :
    Function.Bijective (invariantsToCoinvariants ρ K) :=
  bijective_invariantsToCoinvariants_of_directed ρ H K hρ.directed hρ.exhaustive h0
    fun i hi => haveI := hfin i hi; (hρ.free i).bijective_invariantsToCoinvariants hi (hu i hi)

end FreeLimit

section Topological

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R G V)
  {k : Type uk} [CommRing k] [Algebra R k]
  {ι : Type uι} {H : ι → Subgroup G}

/-- A family of open subgroups shrinking to the identity is directed downwards. -/
theorem directed_of_shrink (hopen : ∀ i, IsOpen (H i : Set G))
    (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U) :
    ∀ i j, ∃ l, H l ≤ H i ⊓ H j := fun i j => by
  obtain ⟨l, hl⟩ := hshrink _
    (((hopen i).inter (hopen j)).mem_nhds ⟨(H i).one_mem, (H j).one_mem⟩)
  exact ⟨l, fun x hx => hl hx⟩

/-- A family of subgroups shrinking to the identity has a member in every open subgroup. -/
theorem exists_le_of_isOpen (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U)
    {K : Subgroup G} (hK : IsOpen (K : Set G)) : ∃ i, H i ≤ K := by
  obtain ⟨i, hi⟩ := hshrink _ (hK.mem_nhds K.one_mem)
  exact ⟨i, fun x hx => hi hx⟩

/-- Every vector of a smooth representation is invariant under some member of a family of
subgroups shrinking to the identity. -/
theorem exhaustive_of_isSmooth (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U)
    (hρ : IsSmooth ρ) (v : V) : ∃ i, v ∈ Representation.invariants (ρ.comp (H i).subtype) := by
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨i, hi⟩ := hshrink _ U.mem_nhds_one
  exact ⟨i, mem_invariants_of_le ρ (fun x hx => hi hx) hU⟩

variable [∀ i, (H i).Normal]

/-- A smooth representation whose invariants under every member of a family of open normal
subgroups shrinking to the identity are free is a direct limit of free modules. -/
theorem IsFreeLimit.of_isSmooth (hopen : ∀ i, IsOpen (H i : Set G))
    (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U) (hρ : IsSmooth ρ)
    (hfree : ∀ i, IsFreeOnInvariants ρ k (H i)) : IsFreeLimit ρ k H :=
  ⟨directed_of_shrink hopen hshrink, exhaustive_of_isSmooth ρ hshrink hρ, hfree⟩

variable {ρ} [IsTopologicalGroup G]

/-- For a family of open normal subgroups shrinking to the identity, the invariants of a direct
limit of free `k[G ⧸ H i]`-modules under an open compact normal subgroup `K` are a free
`k[G ⧸ K]`-module. -/
theorem IsFreeLimit.isFreeOnInvariants_of_isOpen (hρ : IsFreeLimit ρ k H)
    (hopen : ∀ i, IsOpen (H i : Set G)) (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U)
    (K : Subgroup G) [K.Normal] (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    IsFreeOnInvariants ρ k K := by
  obtain ⟨i, hi⟩ := exists_le_of_isOpen hshrink hKo
  have := finiteIndex_subgroupOf_of_isCompact (hopen i) hKc
  exact hρ.isFreeOnInvariants hi

/-- Let `K` be an open normal subgroup of `G` that is compact with quotients by open normal
subgroups `p`-groups, `p` a prime invertible in `R`. For a family of open normal subgroups
shrinking to the identity, `invariantsToCoinvariants` is bijective for `K` on a direct limit of
free modules. -/
theorem IsFreeLimit.bijective_invariantsToCoinvariants_of_isProP (hρ : IsFreeLimit ρ k H)
    (hopen : ∀ i, IsOpen (H i : Set G)) (hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U)
    {p : ℕ} (hp : p.Prime) (hR : IsUnit (p : R)) (K : Subgroup G) [K.Normal]
    (hKo : IsOpen (K : Set G)) [CompactSpace K]
    (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup)) :
    Function.Bijective (invariantsToCoinvariants ρ K) :=
  hρ.bijective_invariantsToCoinvariants K (exists_le_of_isOpen hshrink hKo)
    (fun i _ => finiteIndex_subgroupOf_of_isCompact (hopen i)
      (isCompact_iff_compactSpace.mpr ‹CompactSpace K›))
    (fun i _ => isUnit_index_subgroupOf hp hR (hopen i) hK)

end Topological

end Langlands.Induction

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Induction

universe w u v uI uι

namespace DivisibleSystem

section FreeOverPowQuotient

variable {R : Type u} [CommRing R] {Γ : Type v} [Group Γ] {ℓ m : ℕ}

/-- Finitely supported functions with values in `R ⧸ (ℓ ^ m)` are killed by `ℓ ^ m`. -/
lemma powSMul_finsupp_quotient {X : Type*} {I : Type uI}
    (y : X →₀ I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}) : ((ℓ : R) ^ m) • y = 0 := by
  rw [← algebraMap_smul (R ⧸ Ideal.span {((ℓ : R) ^ m)}) ((ℓ : R) ^ m) y,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_smul]

/-- A representation over `R` equivalent to the permutation representation of `Γ` on itself with
coefficients `I →₀ R ⧸ (ℓ ^ m)`, that is, to the free `(R ⧸ (ℓ ^ m))[Γ]`-module of rank `I`,
satisfies the published `FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_of_equiv_permutation (Q : Rep.{w} R Γ) {I : Type uI}
    (e : Q.ρ.Equiv (permutation R Γ Γ (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}))) :
    FreeOverPowQuotient ℓ m Q := by
  have h : powSMul ℓ m Q = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    refine (powSMul_hom_apply _ x).trans ?_
    calc ((ℓ : R) ^ m) • x = e.symm.toLinearEquiv (((ℓ : R) ^ m) • e.toLinearEquiv x) := by
          rw [map_smul]
          exact congrArg (((ℓ : R) ^ m) • ·) (e.symm_apply_apply x).symm
      _ = 0 := by rw [powSMul_finsupp_quotient, map_zero]
  refine ⟨h, ?_⟩
  let hQ := isTorsionBySet_of_powSMul_eq_zero h
  let _ := hQ.module
  let e' : Representation.Equiv (torsionQuotientRepresentation Q hQ)
      (permutation (R ⧸ Ideal.span {((ℓ : R) ^ m)}) Γ Γ
        (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)})) :=
    .mk
      { toAddEquiv := e.toLinearEquiv.toAddEquiv
        map_smul' := fun s x => by
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
          rw [RingHom.id_apply, Module.IsTorsionBySet.mk_smul hQ, ← Ideal.Quotient.algebraMap_eq,
            algebraMap_smul]
          exact e.toLinearEquiv.map_smul r x }
      fun g => LinearMap.ext fun x =>
        Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x
  have : Module.Free (MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) Γ)
      (permutation (R ⧸ Ideal.span {((ℓ : R) ^ m)}) Γ Γ
        (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)})).asModule :=
    permutation_asModule_free (W := I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)})
      (fun x => IsCancelSMul.stabilizer_eq_bot x)
  exact Module.Free.of_equiv (asModuleLinearEquiv e').symm

/-- If the `K`-invariants of a representation `P` over `R` are a free
`(R ⧸ (ℓ ^ m))[G ⧸ K]`-module, then the representation `P^K` of `G ⧸ K` satisfies
`FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_quotientToInvariants {G : Type v} [Group G] (P : Rep.{w} R G)
    (K : Subgroup G) [K.Normal]
    (h : IsFreeOnInvariants P.ρ (R ⧸ Ideal.span {((ℓ : R) ^ m)}) K) :
    FreeOverPowQuotient ℓ m ((Rep.quotientToInvariantsFunctor R K).obj P) := by
  obtain ⟨I, ⟨e⟩⟩ := h
  exact freeOverPowQuotient_of_equiv_permutation (Rep.of (P.ρ.quotientToInvariants K)) e

end FreeOverPowQuotient

section HomSystem

/-- Surjectivity of the transition maps transfers along an isomorphism of inverse systems. -/
lemma map_surjective_of_iso {R : Type u} [CommRing R] {F F' : ℕᵒᵖ ⥤ ModuleCat.{w} R}
    (e : F ≅ F') {m m' : ℕᵒᵖ} (φ : m ⟶ m') (h : Function.Surjective (F'.map φ)) :
    Function.Surjective (F.map φ) := by
  intro y
  obtain ⟨x, hx⟩ := h ((e.hom.app m').hom y)
  refine ⟨(e.inv.app m).hom x, ?_⟩
  have h1 := congrArg (fun f => f.hom x) (e.inv.naturality φ)
  have h2 := congrArg (fun f => f.hom y) (e.hom_inv_id_app m')
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    at h1 h2
  rw [← h1, hx, h2]

variable {R : Type u} [CommRing R] {G : Type v} [Group G] {ℓ : ℕ}
  (T : DivisibleSystem (Rep.{w} R G) ℓ) {ι : Type uι} (H : ι → Subgroup G)
  [∀ i, (H i).Normal]
  (hT : ∀ m, IsFreeLimit (T.obj m).ρ (R ⧸ Ideal.span {((ℓ : R) ^ m)}) H)
  (K : Subgroup G) [K.Normal] (h0 : ∃ i, H i ≤ K)
  (hfin : ∀ i, H i ≤ K → ((H i).subgroupOf K).FiniteIndex)
  (hu : ∀ i, H i ≤ K → IsUnit (((H i).subgroupOf K).index : R))

include hT h0 hfin hu in
/-- At every level of an `ℓ`-divisible system of direct limits of free
`(R ⧸ (ℓ ^ m))[G ⧸ H i]`-modules, `invariantsToCoinvariants` is bijective for `K`. -/
theorem bijective_invariantsToCoinvariants_of_isFreeLimit (m : ℕ) :
    Function.Bijective (invariantsToCoinvariants (T.obj m).ρ K) :=
  (hT m).bijective_invariantsToCoinvariants K h0 hfin hu

include hT h0 hfin in
/-- At every level of such a system, the `K`-invariants are free over
`(R ⧸ (ℓ ^ m))[G ⧸ K]`. -/
theorem freeOverPowQuotient_invariants_of_isFreeLimit (m : ℕ) :
    FreeOverPowQuotient ℓ m ((Rep.quotientToInvariantsFunctor R K).obj (T.obj m)) := by
  obtain ⟨i, hi⟩ := h0
  have := hfin i hi
  exact freeOverPowQuotient_quotientToInvariants _ K ((hT m).isFreeOnInvariants hi)

variable (hTK : ∀ {m' m : ℕ} (h : m' ≤ m),
    Epi ((Rep.quotientToInvariantsFunctor R K).map (T.projection h)))
  (W : DivisibleSystem (Rep.{w} R (G ⧸ K)) ℓ)

include hT h0 hfin in
/-- Harris 1999, p.312, the maps (4.10.3): the transitions of the inverse system
`m ↦ Hom((T m)^K, W m)` are surjective. -/
lemma isFreeLimit_invariants_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R (T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK) W).map φ) :=
  homSystem_map_surjective R _ W (fun m => powTorsionProjective_of_freeOverPowQuotient
    (freeOverPowQuotient_invariants_of_isFreeLimit T H hT K h0 hfin m)) φ

include hT h0 hfin in
/-- The inverse system `m ↦ Hom((T m)^K, W m)` satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_isFreeLimit_invariants_homSystem :
    (homSystem R (T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK) W ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_homSystem R _ W fun m => powTorsionProjective_of_freeOverPowQuotient
    (freeOverPowQuotient_invariants_of_isFreeLimit T H hT K h0 hfin m)

include hT h0 hfin in
/-- Every morphism `(T n)^K ⟶ W n` is the level-`n` component of a morphism of inverse systems
`T^K ⟶ W`. -/
lemma isFreeLimit_invariants_towerHomEval_surjective (n : ℕ) :
    Function.Surjective
      (towerHomEval R (T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK) W n) :=
  towerHomEval_surjective R _ W (fun m => powTorsionProjective_of_freeOverPowQuotient
    (freeOverPowQuotient_invariants_of_isFreeLimit T H hT K h0 hfin m)) n

include hT h0 hfin hu hTK in
/-- Harris 1999, p.312, before replacing `C^j_m(ẽ)` by its `H_p`-invariants: the transitions of
the inverse system `m ↦ Hom(T m, Inf (W m))` are surjective. -/
lemma isFreeLimit_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R T (W.map (Rep.resFunctor (QuotientGroup.mk' K)))).map φ) :=
  map_surjective_of_iso (invariantsHomSystemIso R K T hTK W
    (bijective_invariantsToCoinvariants_of_isFreeLimit T H hT K h0 hfin hu)) φ
    (isFreeLimit_invariants_homSystem_map_surjective T H hT K h0 hfin hTK W φ)

include hT h0 hfin hu hTK in
/-- The inverse system `m ↦ Hom(T m, Inf (W m))` satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_isFreeLimit_homSystem :
    (homSystem R T (W.map (Rep.resFunctor (QuotientGroup.mk' K))) ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective _ fun _ _ φ =>
    isFreeLimit_homSystem_map_surjective T H hT K h0 hfin hu hTK W φ

end HomSystem


section Complexes

variable {R : Type u} [CommRing R] {G : Type v} [Group G] {ℓ : ℕ}
  (C : DivisibleSystem (CochainComplex (Rep.{w} R G) ℕ) ℓ) {ι : Type uι} (H : ι → Subgroup G)
  [∀ i, (H i).Normal] (j : ℕ)
  (hC : ∀ m, IsFreeLimit ((C.obj m).X j).ρ (R ⧸ Ideal.span {((ℓ : R) ^ m)}) H)
  (K : Subgroup G) [K.Normal] (h0 : ∃ i, H i ≤ K)
  (hfin : ∀ i, H i ≤ K → ((H i).subgroupOf K).FiniteIndex)
  (hu : ∀ i, H i ≤ K → IsUnit (((H i).subgroupOf K).index : R))
  (hCK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((Rep.quotientToInvariantsFunctor R K).map ((C.projection h).f q)))
  (W : DivisibleSystem (Rep.{w} R (G ⧸ K)) ℓ)

include hC h0 hfin in
/-- Harris 1999, p.312, the maps (4.10.3) for the degree `j` terms of an `ℓ`-divisible system
of complexes: the transitions of `m ↦ Hom((C_m^K)^j, W m)` are surjective. -/
lemma isFreeLimit_degree_invariants_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((C.mapComplexes (Rep.quotientToInvariantsFunctor R K) hCK).degree j)
        W).map φ) :=
  isFreeLimit_invariants_homSystem_map_surjective (C.degree j) H hC K h0 hfin
    (fun h => hCK h j) W φ

include hC h0 hfin in
/-- The degree-`j` inverse system `m ↦ Hom((C_m^K)^j, W m)` satisfies the Mittag-Leffler
condition. -/
lemma isMittagLeffler_isFreeLimit_degree_invariants_homSystem :
    (homSystem R ((C.mapComplexes (Rep.quotientToInvariantsFunctor R K) hCK).degree j) W ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_isFreeLimit_invariants_homSystem (C.degree j) H hC K h0 hfin
    (fun h => hCK h j) W

include hC h0 hfin hu hCK in
/-- Harris 1999, p.312: the transitions of the degree-`j` inverse system
`m ↦ Hom(C_m^j, Inf (W m))` are surjective. -/
lemma isFreeLimit_degree_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R (C.degree j) (W.map (Rep.resFunctor (QuotientGroup.mk' K)))).map φ) :=
  isFreeLimit_homSystem_map_surjective (C.degree j) H hC K h0 hfin hu (fun h => hCK h j) W φ

include hC h0 hfin hu hCK in
/-- The degree-`j` inverse system `m ↦ Hom(C_m^j, Inf (W m))` satisfies the Mittag-Leffler
condition. -/
lemma isMittagLeffler_isFreeLimit_degree_homSystem :
    (homSystem R (C.degree j) (W.map (Rep.resFunctor (QuotientGroup.mk' K))) ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_isFreeLimit_homSystem (C.degree j) H hC K h0 hfin hu (fun h => hCK h j) W

end Complexes

end DivisibleSystem

end Langlands.Cohomology
