import Langlands.GaloisCohomology.Field.KummerSequence
import Langlands.Cohomology.Profinite.Dimension.Procyclic
import Langlands.Cohomology.Profinite.Characters

/-!
# Modules of divisors attached to a family of homomorphisms

Let `G` be a profinite group, `φ i : H i →* G` a family of homomorphisms and `A` an abelian group.
The functions `f : I → G → A` that have finite support in `i`, are locally constant in the second
variable and invariant under left translation by the image of `φ i` form a smooth `G`-module under
right translation (`divisorModule φ A`). For `G = G_S` and the decomposition maps at the places
outside `S` with `A = ℤ` this is the module of divisors prime to `S` of the maximal extension
unramified outside `S`: a divisor is determined by its multiplicities at the places `g⁻¹ w_v`,
`g ∈ G`, above each `v`.

* `divisorEval i`: evaluation at `(i, 1)`, a map of `H i`-modules to `A` with trivial action;
* `divisorSequence`: the short exact sequence for `0 → ℤ → ℚ → ℚ/ℤ → 0`;
* `isZero_cohomology_divisorModule_rat`: the rational divisors have no cohomology in positive
  degree (multiplication by `n ≠ 0` is bijective on them);
* `isZero_cohomology_one_divisorModule_int`: `H¹(G, D_ℤ) = 0`;
* `eq_zero_of_divisorEval_eq_zero`: a class of `H²(G, D_ℤ)` whose evaluations in all
  `H²(H i, ℤ)` vanish is zero;
* `finite_divisorEval_ne_zero`: only finitely many evaluations of a class are nonzero;
* `exists_coprime_nsmul_cohomology_eq_zero`: if every element of a module is killed by an integer
  prime to `ℓ`, so is every cohomology class.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology

universe u

noncomputable section

section Trivial

variable (G : Type u) [Group G] (A : Type u) [AddCommGroup A]

/-- The abelian group `A` with the trivial action of `G`, as a `ULift ℤ`-representation. -/
abbrev trivialModule : Rep.{u} (ULift.{u} ℤ) G := Rep.of (intRep.{u} (1 : G →* AddMonoid.End A))

theorem trivialModule_ρ_apply (g : G) (a : A) : (trivialModule G A).ρ g a = a :=
  rfl

instance isTrivial_trivialModule : (trivialModule G A).ρ.IsTrivial where
  out _ := rfl

instance isSmoothRep_trivialModule [TopologicalSpace G] : IsSmoothRep (trivialModule G A) :=
  isSmoothRep_of_isTrivial _

/-- An additive map as a morphism of trivial modules. -/
def trivialMap {A B : Type u} [AddCommGroup A] [AddCommGroup B] (g : A →+ B) :
    trivialModule G A ⟶ trivialModule G B :=
  Rep.ofHom ⟨uliftIntLinearMap g, fun _ => LinearMap.ext fun _ => rfl⟩

end Trivial

section Coefficients

/-- The quotient map `ℚ → ℚ/ℤ`. -/
abbrev ratToQZ : ℚ →+ QZ := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))

theorem ratToQZ_eq_zero_iff (q : ℚ) : ratToQZ q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  have : ratToQZ q = 0 ↔ q ∈ AddSubgroup.zmultiples (1 : ℚ) := QuotientAddGroup.eq_zero_iff q
  rw [this, AddSubgroup.mem_zmultiples_iff]
  simp

theorem ratToQZ_surjective : Function.Surjective ratToQZ := QuotientAddGroup.mk'_surjective _

/-- `ℤ → ℚ` on the lifted groups. -/
def uliftIntToRat : ULift.{u} ℤ →+ ULift.{u} ℚ :=
  (AddEquiv.ulift.symm : ℚ ≃+ ULift.{u} ℚ).toAddMonoidHom.comp
    ((Int.castAddHom ℚ).comp (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom)

/-- `ℚ → ℚ/ℤ` on the lifted groups. -/
def uliftRatToQZ : ULift.{u} ℚ →+ ULift.{u} QZ :=
  (AddEquiv.ulift.symm : QZ ≃+ ULift.{u} QZ).toAddMonoidHom.comp
    (ratToQZ.comp (AddEquiv.ulift : ULift.{u} ℚ ≃+ ℚ).toAddMonoidHom)

@[simp]
theorem uliftIntToRat_apply (n : ULift.{u} ℤ) : uliftIntToRat n = ULift.up (n.down : ℚ) :=
  rfl

@[simp]
theorem uliftRatToQZ_apply (q : ULift.{u} ℚ) : uliftRatToQZ q = ULift.up (ratToQZ q.down) :=
  rfl

theorem bijective_nsmul_uliftRat {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective fun q : ULift.{u} ℚ => n • q := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun a b hab => ?_, fun a => ⟨ULift.up (a.down / n), ?_⟩⟩
  · apply ULift.ext
    have : n • a.down = n • b.down := congrArg ULift.down hab
    simp only [nsmul_eq_mul] at this
    exact mul_left_cancel₀ hn' this
  · apply ULift.ext
    change n • (a.down / n) = a.down
    simp only [nsmul_eq_mul]
    field_simp

end Coefficients

section Torsion

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- If every element of a smooth module is killed by an integer prime to `ℓ`, so is every
cohomology class. -/
theorem exists_coprime_nsmul_cohomology_eq_zero [CompactSpace G] {k : Type u} [CommRing k] (M : Rep.{u} k G)
    [IsSmoothRep M] (ℓ : ℕ) (hM : ∀ m : M, ∃ N : ℕ, N.Coprime ℓ ∧ N • m = 0) (n : ℕ)
    (x : cohomology M n) : ∃ N : ℕ, N.Coprime ℓ ∧ N • x = 0 := by
  classical
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective M n x
  set c := cochainOf M (cocycleι M n z) with hc
  have hlc : IsLocallyConstant c := isLocallyConstant_cochainOf _
  have hfin : (Set.range c).Finite := hlc.range_finite
  choose N hNc hNm using hM
  refine ⟨∏ m ∈ hfin.toFinset, N m, Nat.Coprime.prod_left fun m _ => hNc m, ?_⟩
  have hz : (∏ m ∈ hfin.toFinset, N m) • z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [map_nsmul, map_zero, cochainOf_zero]
    funext g
    have hmem : c g ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨g, rfl⟩
    change (∏ m ∈ hfin.toFinset, N m) • c g = 0
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N hmem
    rw [hd, mul_comm, ← smul_smul, hNm, smul_zero]
  rw [← map_nsmul, hz, map_zero]

/-- A class killed by a power of `ℓ` in the cohomology of a module whose elements are killed by
integers prime to `ℓ` is zero. -/
theorem eq_zero_of_pow_nsmul_eq_zero_of_coprime [CompactSpace G] {k : Type u} [CommRing k] (M : Rep.{u} k G)
    [IsSmoothRep M] (ℓ : ℕ) (hM : ∀ m : M, ∃ N : ℕ, N.Coprime ℓ ∧ N • m = 0) (n : ℕ)
    (x : cohomology M n) (j : ℕ) (hx : ℓ ^ j • x = 0) : x = 0 := by
  obtain ⟨N, hN, hNx⟩ := exists_coprime_nsmul_cohomology_eq_zero M ℓ hM n x
  have h1 : addOrderOf x ∣ N := addOrderOf_dvd_of_nsmul_eq_zero hNx
  have h2 : addOrderOf x ∣ ℓ ^ j := addOrderOf_dvd_of_nsmul_eq_zero hx
  have h3 : addOrderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (hN.pow_right j)) h2
  exact AddMonoid.addOrderOf_eq_one_iff.1 h3

end Torsion

section Functions

variable {G : Type u} [Group G] [TopologicalSpace G] {I : Type u} {H : I → Type u}
  [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] (φ : ∀ i, H i →ₜ* G) (A : Type u) [AddCommGroup A]

/-- Functions `f : I → G → A` with finite support in `i`, locally constant and invariant under left
translation by the image of `φ i` in the `i`-th component. -/
def divisorFunctions : AddSubgroup (I → G → A) where
  carrier := {f | {i | f i ≠ 0}.Finite ∧
    ∀ i, IsLocallyConstant (f i) ∧ ∀ (h : H i) (x : G), f i (φ i h * x) = f i x}
  add_mem' {f g} hf hg := by
    refine ⟨(hf.1.union hg.1).subset fun i hi => ?_,
      fun i => ⟨(hf.2 i).1.add (hg.2 i).1, fun h x => ?_⟩⟩
    · by_contra hc
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
      exact hi (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
    · simp only [Pi.add_apply, (hf.2 i).2, (hg.2 i).2]
  zero_mem' := ⟨by simp, fun i => ⟨IsLocallyConstant.const 0, fun _ _ => rfl⟩⟩
  neg_mem' {f} hf := by
    refine ⟨hf.1.subset fun i hi => ?_, fun i => ⟨(hf.2 i).1.neg, fun h x => ?_⟩⟩
    · simp only [Set.mem_ofPred_eq, Pi.neg_apply, ne_eq, neg_eq_zero] at hi ⊢
      exact hi
    · simp only [Pi.neg_apply, (hf.2 i).2]

theorem mem_divisorFunctions {f : I → G → A} : f ∈ divisorFunctions φ A ↔
    {i | f i ≠ 0}.Finite ∧ ∀ i, IsLocallyConstant (f i) ∧ ∀ (h : H i) (x : G), f i (φ i h * x) = f i x :=
  Iff.rfl

variable [IsTopologicalGroup G]

/-- The action of `G` on `divisorFunctions φ A` by right translation. -/
def divisorAction : G →* AddMonoid.End (divisorFunctions φ A) where
  toFun g :=
    { toFun := fun f => ⟨fun i x => (f : I → G → A) i (x * g), by
        refine ⟨f.2.1.subset fun i hi => ?_, fun i => ⟨(f.2.2 i).1.comp_continuous
          (continuous_mul_const g), fun h x => ?_⟩⟩
        · intro hc
          apply hi
          change (fun x => (f : I → G → A) i (x * g)) = 0
          funext x
          rw [hc]
          rfl
        · simp only [mul_assoc, (f.2.2 i).2]⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_one' := by
    ext f i x
    simp only [mul_one]
    rfl
  map_mul' g₁ g₂ := by
    ext f i x
    change (f : I → G → A) i (x * (g₁ * g₂)) = (f : I → G → A) i (x * g₁ * g₂)
    rw [mul_assoc]

theorem coe_divisorAction_apply (g : G) (f : divisorFunctions φ A) (i : I) (x : G) :
    ((divisorAction φ A g f : divisorFunctions φ A) : I → G → A) i x = (f : I → G → A) i (x * g) :=
  rfl

omit [IsTopologicalGroup G] in
theorem exists_mem_nhds_one_forall_mul_eq [IsTopologicalGroup G] [CompactSpace G] {X : Type*}
    {f : G → X} (hf : IsLocallyConstant f) :
    ∃ V ∈ nhds (1 : G), ∀ x : G, ∀ v ∈ V, f (x * v) = f x := by
  have hN : ∀ x : G, {w | f (x * w) = f x} ∈ nhds (1 : G) := fun x =>
    ((hf.isOpen_fiber (f x)).preimage (continuous_const_mul x)).mem_nhds (by simp)
  choose W hWo hW1 hWW using fun x => exists_open_nhds_one_split (hN x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' W x)
    (fun x => (hWo x).preimage (continuous_const_mul x⁻¹))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using hW1 y⟩)
  refine ⟨⋂ x ∈ t, W x, (Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (hW1 x), ?_⟩
  intro y v hv
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hv' : v ∈ W x := Set.mem_iInter₂.1 hv x hxt
  have h1 : f (x * (x⁻¹ * y * v)) = f x := hWW x _ hyx _ hv'
  have h2 : f (x * (x⁻¹ * y * 1)) = f x := hWW x _ hyx _ (hW1 x)
  rw [mul_one, mul_inv_cancel_left] at h2
  rw [mul_assoc x⁻¹, mul_inv_cancel_left] at h1
  rw [h1, h2]

/-- The `G`-module of divisor functions. -/
abbrev divisorModule : Rep.{u} (ULift.{u} ℤ) G := Rep.of (intRep.{u} (divisorAction φ A))

instance isSmoothRep_divisorModule [CompactSpace G] : IsSmoothRep (divisorModule φ A) := by
  refine IsSmoothRep.of_isOpen_stabilizer _ fun f => ?_
  have hfin := f.2.1
  choose V hV hVf using fun i => exists_mem_nhds_one_forall_mul_eq ((f.2.2 i).1)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset ((Filter.biInter_mem hfin).2 fun i _ => hV i) ?_
  intro g hg
  rw [SetLike.mem_coe, mem_vectorStabilizer]
  apply Subtype.ext
  funext i x
  change (f : I → G → A) i (x * g) = (f : I → G → A) i x
  by_cases hi : i ∈ {i | (f : I → G → A) i ≠ 0}
  · exact hVf i x g (Set.mem_iInter₂.1 hg i hi)
  · simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hi
    rw [hi]
    rfl

/-- Evaluation at `(i, 1)`, a map of `H i`-modules to `A` with trivial action. -/
def divisorEval (i : I) : Rep.res (φ i : H i →* G) (divisorModule φ A) ⟶ trivialModule (H i) A :=
  Rep.ofHom ⟨uliftIntLinearMap
    { toFun := fun f : divisorFunctions φ A => (f : I → G → A) i 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl },
    fun h => LinearMap.ext fun f => by
      change (f : I → G → A) i (1 * φ i h) = (f : I → G → A) i 1
      rw [one_mul, ← mul_one (φ i h), (f.2.2 i).2 h 1]⟩

theorem divisorEval_hom_apply (i : I) (f : divisorFunctions φ A) :
    (divisorEval φ A i).hom f = (f : I → G → A) i 1 :=
  rfl

/-- The map of divisor modules induced by an additive map of coefficients. -/
def divisorMap {B : Type u} [AddCommGroup B] (g : A →+ B) : divisorModule φ A ⟶ divisorModule φ B :=
  Rep.ofHom ⟨uliftIntLinearMap
    { toFun := fun f : divisorFunctions φ A => ⟨fun i x => g ((f : I → G → A) i x), by
        refine ⟨f.2.1.subset fun i hi => ?_, fun i => ⟨(f.2.2 i).1.comp g, fun h x => ?_⟩⟩
        · intro hc
          apply hi
          change (fun x => g ((f : I → G → A) i x)) = 0
          funext x
          rw [hc, Pi.zero_apply, Pi.zero_apply, map_zero]
        · change g ((f : I → G → A) i (φ i h * x)) = g ((f : I → G → A) i x)
          rw [(f.2.2 i).2]⟩
      map_zero' := Subtype.ext (funext fun _ => funext fun _ => map_zero g)
      map_add' := fun f₁ f₂ => Subtype.ext (funext fun _ => funext fun _ => map_add g _ _) },
    fun _ => LinearMap.ext fun _ => rfl⟩

theorem coe_divisorMap_hom_apply {B : Type u} [AddCommGroup B] (g : A →+ B)
    (f : divisorFunctions φ A) :
    (((divisorMap φ A g).hom f : divisorFunctions φ B) : I → G → B) =
      fun i x => g ((f : I → G → A) i x) :=
  rfl

/-- The short exact sequence of divisor modules for `0 → ℤ → ℚ → ℚ/ℤ → 0`. -/
def divisorSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
  ShortComplex.mk (divisorMap φ (ULift.{u} ℤ) uliftIntToRat) (divisorMap φ (ULift.{u} ℚ) uliftRatToQZ)
    (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext i x
      exact ULift.ext ((ratToQZ_eq_zero_iff _).2
        ⟨(((f : divisorFunctions φ (ULift.{u} ℤ)) : I → G → ULift.{u} ℤ) i x).down, rfl⟩))

instance isSmoothRep_divisorSequence_X₁ [CompactSpace G] : IsSmoothRep (divisorSequence φ).X₁ :=
  inferInstanceAs (IsSmoothRep (divisorModule φ (ULift.{u} ℤ)))

instance isSmoothRep_divisorSequence_X₂ [CompactSpace G] : IsSmoothRep (divisorSequence φ).X₂ :=
  inferInstanceAs (IsSmoothRep (divisorModule φ (ULift.{u} ℚ)))

instance isSmoothRep_divisorSequence_X₃ [CompactSpace G] : IsSmoothRep (divisorSequence φ).X₃ :=
  inferInstanceAs (IsSmoothRep (divisorModule φ (ULift.{u} QZ)))

theorem divisorSequence_shortExact : (divisorSequence φ).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f₀ hf
    let f : divisorFunctions φ (ULift.{u} ℚ) := f₀
    have hint : ∀ i x, ((⌊((f : I → G → ULift.{u} ℚ) i x).down⌋ : ℤ) : ℚ) =
        ((f : I → G → ULift.{u} ℚ) i x).down := fun i x => by
      have h0 : ratToQZ ((f : I → G → ULift.{u} ℚ) i x).down = 0 :=
        congrArg (fun f : divisorFunctions φ (ULift.{u} QZ) =>
          ((f : I → G → ULift.{u} QZ) i x).down)
          (show (divisorMap φ (ULift.{u} ℚ) uliftRatToQZ).hom f = 0 from hf)
      obtain ⟨n, hn⟩ := (ratToQZ_eq_zero_iff _).1 h0
      rw [← hn, Int.floor_intCast]
    refine ⟨⟨fun i x => ULift.up ⌊((f : I → G → ULift.{u} ℚ) i x).down⌋, ?_,
      fun i => ⟨(f.2.2 i).1.comp fun q => ULift.up ⌊q.down⌋, fun h x => ?_⟩⟩, ?_⟩
    · refine f.2.1.subset fun i hi => ?_
      intro hc
      apply hi
      funext x
      change ULift.up ⌊((f : I → G → ULift.{u} ℚ) i x).down⌋ = (0 : ULift.{u} ℤ)
      rw [hc]
      rfl
    · change ULift.up ⌊((f : I → G → ULift.{u} ℚ) i (φ i h * x)).down⌋ =
        ULift.up ⌊((f : I → G → ULift.{u} ℚ) i x).down⌋
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      exact ULift.ext (hint i x)
  mono_f := (Rep.mono_iff_injective _).2 fun f₁ f₂ h => by
    apply Subtype.ext
    funext i x
    have := congrArg (fun f : divisorFunctions φ (ULift.{u} ℚ) =>
      ((f : I → G → ULift.{u} ℚ) i x).down) h
    exact ULift.ext (Int.cast_injective this)
  epi_g := (Rep.epi_iff_surjective _).2 fun f₀ => by
    classical
    let f : divisorFunctions φ (ULift.{u} QZ) := f₀
    let sec : QZ → ℚ := fun q => if q = 0 then 0 else Function.surjInv ratToQZ_surjective q
    have hsec : ∀ q, ratToQZ (sec q) = q := fun q => by
      by_cases hq : q = 0
      · simp [sec, hq]
      · simp only [sec, hq, ite_false]
        exact Function.surjInv_eq ratToQZ_surjective q
    refine ⟨⟨fun i x => ULift.up (sec ((f : I → G → ULift.{u} QZ) i x).down), ?_,
      fun i => ⟨(f.2.2 i).1.comp fun q => ULift.up (sec q.down), fun h x => ?_⟩⟩, ?_⟩
    · refine f.2.1.subset fun i hi => ?_
      intro hc
      apply hi
      funext x
      change ULift.up (sec ((f : I → G → ULift.{u} QZ) i x).down) = (0 : ULift.{u} ℚ)
      rw [hc]
      simp [sec]
      rfl
    · change ULift.up (sec ((f : I → G → ULift.{u} QZ) i (φ i h * x)).down) =
        ULift.up (sec ((f : I → G → ULift.{u} QZ) i x).down)
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      exact ULift.ext (hsec _)

end Functions

section TrivialSequence

variable (H : Type u) [Group H]

/-- The short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` of trivial `H`-modules. -/
def trivialSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) H) :=
  ShortComplex.mk (trivialMap H uliftIntToRat) (trivialMap H uliftRatToQZ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    exact ULift.ext ((ratToQZ_eq_zero_iff _).2 ⟨(n : ULift.{u} ℤ).down, rfl⟩))

theorem trivialSequence_shortExact : (trivialSequence H).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro q hq
    have hq' : ratToQZ (q : ULift.{u} ℚ).down = 0 := congrArg ULift.down hq
    obtain ⟨n, hn⟩ := (ratToQZ_eq_zero_iff _).1 hq'
    exact ⟨(ULift.up n : ULift.{u} ℤ), ULift.ext hn⟩
  mono_f := (Rep.mono_iff_injective _).2 fun a b h =>
    ULift.ext (Int.cast_injective (α := ℚ) (congrArg ULift.down h))
  epi_g := (Rep.epi_iff_surjective _).2 fun q => by
    obtain ⟨r, hr⟩ := ratToQZ_surjective (q : ULift.{u} QZ).down
    exact ⟨(ULift.up r : ULift.{u} ℚ), ULift.ext hr⟩

variable [TopologicalSpace H]

instance isSmoothRep_trivialSequence_X₁ : IsSmoothRep (trivialSequence H).X₁ :=
  inferInstanceAs (IsSmoothRep (trivialModule H (ULift.{u} ℤ)))

instance isSmoothRep_trivialSequence_X₂ : IsSmoothRep (trivialSequence H).X₂ :=
  inferInstanceAs (IsSmoothRep (trivialModule H (ULift.{u} ℚ)))

instance isSmoothRep_trivialSequence_X₃ : IsSmoothRep (trivialSequence H).X₃ :=
  inferInstanceAs (IsSmoothRep (trivialModule H (ULift.{u} QZ)))

end TrivialSequence

section Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {I : Type u} {H : I → Type u} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] (φ : ∀ i, H i →ₜ* G)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [∀ i, IsTopologicalGroup (H i)] in
theorem bijective_nsmul_divisorFunctions_rat {n : ℕ} (hn : n ≠ 0) :
    Function.Bijective fun f : divisorModule φ (ULift.{u} ℚ) => n • f := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro f g h
    apply Subtype.ext
    funext i x
    have h' := congrArg (fun f : divisorFunctions φ (ULift.{u} ℚ) =>
      (((f : I → G → ULift.{u} ℚ) i x).down)) h
    have e : ∀ f : divisorFunctions φ (ULift.{u} ℚ),
        (((n • f : divisorFunctions φ (ULift.{u} ℚ)) : I → G → ULift.{u} ℚ) i x).down =
          n * ((f : I → G → ULift.{u} ℚ) i x).down := fun f => by
      rw [AddSubgroup.coe_nsmul, Pi.smul_apply, Pi.smul_apply]
      change n • _ = _
      rw [nsmul_eq_mul]
    simp only [e] at h'
    exact ULift.ext (mul_left_cancel₀ hn' h')
  · intro f
    refine ⟨⟨fun i x => ULift.up (((f : I → G → ULift.{u} ℚ) i x).down / n), f.2.1.subset fun i hi => ?_,
      fun i => ⟨(f.2.2 i).1.comp fun q => ULift.up (q.down / (n : ℚ)), fun h x => ?_⟩⟩, ?_⟩
    · intro hc
      apply hi
      funext x
      change ULift.up (((f : I → G → ULift.{u} ℚ) i x).down / n) = (0 : ULift.{u} ℚ)
      rw [hc]
      apply ULift.ext
      change (0 : ℚ) / n = 0
      simp
    · change ULift.up (((f : I → G → ULift.{u} ℚ) i (φ i h * x)).down / n) =
        ULift.up (((f : I → G → ULift.{u} ℚ) i x).down / n)
      rw [(f.2.2 i).2]
    · apply Subtype.ext
      funext i x
      apply ULift.ext
      change n • (((f : I → G → ULift.{u} ℚ) i x).down / n) = ((f : I → G → ULift.{u} ℚ) i x).down
      rw [nsmul_eq_mul]
      field_simp

/-- The rational divisor module has no cohomology in positive degrees. -/
theorem isZero_cohomology_divisorModule_rat {q : ℕ} (hq : 1 ≤ q) :
    IsZero (cohomology (divisorModule φ (ULift.{u} ℚ)) q) :=
  isZero_cohomology_of_bijective_nsmul _ (fun _ hn => bijective_nsmul_divisorFunctions_rat φ hn) hq

theorem isZero_cohomology_trivialModule_rat (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K] {q : ℕ} (hq : 1 ≤ q) :
    IsZero (cohomology (trivialModule K (ULift.{u} ℚ)) q) :=
  isZero_cohomology_of_bijective_nsmul _ (fun _ hn => bijective_nsmul_uliftRat hn) hq

/-- `H¹(G, D_ℤ) = 0`. -/
theorem isZero_cohomology_one_divisorModule_int :
    IsZero (cohomology (divisorModule φ (ULift.{u} ℤ)) 1) := by
  have hS := divisorSequence_shortExact φ
  have h1 : Subsingleton (cohomology (divisorSequence φ).X₂ 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_divisorModule_rat φ le_rfl)
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  suffices h : ∀ x : cohomology (divisorSequence φ).X₁ 1, x = 0 from (h x).trans (h y).symm
  intro x
  obtain ⟨v, rfl⟩ := exists_δ_zeroIso_inv_eq hS h1 x
  rw [δ_zeroIso_inv_eq_zero_iff]
  classical
  let a : divisorFunctions φ (ULift.{u} QZ) := v.1
  have hconst : ∀ i x, (a : I → G → ULift.{u} QZ) i x = (a : I → G → ULift.{u} QZ) i 1 :=
    fun i x => by
      have := congrArg (fun f : divisorFunctions φ (ULift.{u} QZ) =>
        (f : I → G → ULift.{u} QZ) i 1) (v.2 x)
      change (a : I → G → ULift.{u} QZ) i (1 * x) = (a : I → G → ULift.{u} QZ) i 1 at this
      rwa [one_mul] at this
  let sec : QZ → ℚ := fun q => if q = 0 then 0 else Function.surjInv ratToQZ_surjective q
  have hsec : ∀ q, ratToQZ (sec q) = q := fun q => by
    by_cases hq : q = 0
    · simp [sec, hq]
    · simp only [sec, hq, ite_false]
      exact Function.surjInv_eq ratToQZ_surjective q
  let b : divisorFunctions φ (ULift.{u} ℚ) :=
    ⟨fun i _ => ULift.up (sec ((a : I → G → ULift.{u} QZ) i 1).down), a.2.1.subset fun i hi => ?_,
      fun i => ⟨IsLocallyConstant.const _, fun _ _ => rfl⟩⟩
  · refine ⟨⟨b, fun g => rfl⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i x
    apply ULift.ext
    change ratToQZ (sec ((a : I → G → ULift.{u} QZ) i 1).down) = ((a : I → G → ULift.{u} QZ) i x).down
    rw [hsec, ← hconst i x]
  · intro hc
    apply hi
    funext x
    change ULift.up (sec ((a : I → G → ULift.{u} QZ) i 1).down) = (0 : ULift.{u} ℚ)
    rw [hc]
    apply ULift.ext
    simp [sec]

/-- The evaluation maps on the sequences `0 → ℤ → ℚ → ℚ/ℤ → 0`. -/
def divisorEvalSequence (i : I) :
    (divisorSequence φ).map (Rep.resFunctor (φ i : H i →* G)) ⟶ trivialSequence (H i) where
  τ₁ := divisorEval φ (ULift.{u} ℤ) i
  τ₂ := divisorEval φ (ULift.{u} ℚ) i
  τ₃ := divisorEval φ (ULift.{u} QZ) i
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    rfl

/-- A class of `H²(G, D_ℤ)` whose evaluations in all `H²(H i, ℤ)` vanish is zero. -/
theorem eq_zero_of_divisorEval_eq_zero [∀ i, CompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)] (x : cohomology (divisorModule φ (ULift.{u} ℤ)) 2)
    (hx : ∀ i, (map (φ i) (divisorEval φ (ULift.{u} ℤ) i) 2).hom x = 0) : x = 0 := by
  have hS := divisorSequence_shortExact φ
  have h2 : IsZero (cohomology (divisorSequence φ).X₂ 2) :=
    isZero_cohomology_divisorModule_rat φ (by norm_num)
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 1 2 rfl) x
    ((ModuleCat.subsingleton_of_isZero h2).elim _ _)
  suffices hy : y = 0 by
    change (δ hS 1 2 rfl).hom y = 0
    rw [hy, map_zero]
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 y
  set c : (Fin 1 → G) → divisorFunctions φ (ULift.{u} QZ) := cocycleFun (divisorSequence φ).X₃ z
    with hc
  have hloc : ∀ (i : I) (h : H i),
      ((c fun _ => φ i h : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1 = 0 := by
    intro i h
    have hT := trivialSequence_shortExact (H i)
    have e := congrArg (fun ψ => ψ.hom ((cohomologyπ _ 1) z))
      (δ_comp_map (φ i) (divisorEvalSequence φ i) hS hT 1 2 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e
    have hzero := e.symm.trans (hx i)
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 1 2 rfl) _ hzero
    have hw0 : w = 0 := (ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_trivialModule_rat (H i) le_rfl)).elim _ _
    rw [hw0, map_zero] at hw
    have hyi : (cohomologyπ _ 1).hom
        (cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ 1 z) = 0 := by
      rw [← cohomologyπ_map_apply]
      exact hw.symm
    have hev := congrArg (H1Eval (trivialSequence (H i)).X₃ h).hom hyi
    rw [map_zero, H1Eval_cohomology_class_apply, Submodule.Quotient.mk_eq_zero] at hev
    obtain ⟨a, ha⟩ := hev
    have h0 : ((trivialSequence (H i)).X₃.ρ h - 1) a = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      rfl
    rw [h0] at ha
    have key : cocycleFun (trivialSequence (H i)).X₃
        (cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ 1 z) =
        fun g => (divisorEval φ (ULift.{u} QZ) i).hom (c (⇑(φ i) ∘ g)) :=
      cochainOf_cocycleι_cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ z
    have := congrFun key fun _ => h
    rw [← ha] at this
    exact this.symm
  have hd := d_cocycleFun (divisorSequence φ).X₃ z
  have hmul : ∀ g h : G, c (fun _ => g * h) =
      divisorAction φ (ULift.{u} QZ) g (c fun _ => h) + c fun _ => g :=
    fun g h => cocycle_mul_of_d_eq_zero hd g h
  have hlcc : IsLocallyConstant c := isLocallyConstant_cocycleFun _ z
  have hfin : (Set.range c).Finite := hlcc.range_finite
  have hlcx : IsLocallyConstant fun x : G => c fun _ => x :=
    hlcc.comp_continuous (continuous_pi fun _ => continuous_id)
  let b : divisorFunctions φ (ULift.{u} QZ) :=
    ⟨fun i x => ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1, by
      refine ⟨(hfin.biUnion fun f _ => f.2.1).subset fun i hi => ?_, fun i =>
        ⟨hlcx.comp fun f : divisorFunctions φ (ULift.{u} QZ) => (f : I → G → ULift.{u} QZ) i 1,
          fun h x => ?_⟩⟩
      · obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
        refine Set.mem_iUnion₂.2 ⟨c fun _ => x, ⟨_, rfl⟩, fun hc => hx ?_⟩
        change ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1 = 0
        rw [hc]
        rfl
      · change ((c fun _ => φ i h * x : divisorFunctions φ (ULift.{u} QZ)) :
            I → G → ULift.{u} QZ) i 1 =
          ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1
        rw [hmul]
        change ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i
            (1 * φ i h) +
          ((c fun _ => φ i h : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1 = _
        rw [hloc, add_zero, one_mul, ← mul_one (φ i h), ((c fun _ => x).2.2 i).2]⟩
  let b0 : (cochains (divisorSequence φ).X₃).X 0 :=
    (⟨fun _ => b, IsLocallyConstant.const _⟩ : locallyConstantCochains (divisorSequence φ).X₃ 0)
  have hz : z = ((cochains _).toCycles 0 1).hom b0 := by
    apply cocycleFun_injective
    rw [cocycleFun_toCycles]
    funext g
    rw [inhomogeneousD_zero_apply]
    have hg : g = fun _ => g 0 := funext fun j => by rw [Subsingleton.elim j 0]
    apply Subtype.ext
    funext i x
    change ((c g : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i x =
      b.1 i (x * g 0) - b.1 i x
    change _ = ((c fun _ => x * g 0 : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1 -
      ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1
    rw [hmul]
    change _ = ((c fun _ => g 0 : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i (1 * x) +
      ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1 -
      ((c fun _ => x : divisorFunctions φ (ULift.{u} QZ)) : I → G → ULift.{u} QZ) i 1
    rw [add_sub_cancel_right, one_mul, ← hg]
  rw [hz]
  exact cohomologyπ_toCycles _ 0 1 b0

omit [TotallyDisconnectedSpace G] in
/-- Only finitely many evaluations of a cohomology class of a divisor module are nonzero. -/
theorem finite_divisorEval_ne_zero (A : Type u) [AddCommGroup A] (n : ℕ)
    (x : cohomology (divisorModule φ A) n) :
    {i | (map (φ i) (divisorEval φ A i) n).hom x ≠ 0}.Finite := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective (divisorModule φ A) n x
  set c := cochainOf (divisorModule φ A) (cocycleι (divisorModule φ A) n z) with hc
  have hfin : (Set.range c).Finite := (isLocallyConstant_cochainOf _).range_finite
  have hT : (⋃ f ∈ Set.range c, {i | ((f : divisorFunctions φ A) : I → G → A) i ≠ 0}).Finite :=
    hfin.biUnion fun f _ => (f : divisorFunctions φ A).2.1
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hz : cocyclesMap (φ i) (divisorEval φ A i) n z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [cochainOf_cocycleι_cocyclesMap, map_zero]
    funext h
    rw [divisorEval_hom_apply]
    have hmem : ((c (⇑(φ i) ∘ h) : divisorFunctions φ A) : I → G → A) i = 0 := by
      by_contra hne
      exact hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)
    change ((c (⇑(φ i) ∘ h) : divisorFunctions φ A) : I → G → A) i 1 = 0
    rw [hmem]
    rfl
  change (map (φ i) (divisorEval φ A i) n).hom ((cohomologyπ (divisorModule φ A) n).hom z) = 0
  rw [cohomologyπ_map_apply, hz, map_zero]

end Cohomology

end

end Langlands.GaloisCohomology
