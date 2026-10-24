import Langlands.Cohomology.HerbrandQuotient
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Herbrand quotients of permutation lattices

Let a finite cyclic group `G` act on a finite set `X`. The permutation representation `ℤ[X]`
(Mathlib's `Rep.ofMulAction`, over the lifted integers) has `H¹(G, ℤ[X]) = 0` and
`|H²(G, ℤ[X])| = ∏ |G_x|`, the product over the orbits of the orders of the stabilizers. In
particular its Herbrand quotient is this product.

The proof is a direct computation with the subquotients `ker N ⧸ range (ρ(g) - 1)` and
`ker (ρ(g) - 1) ⧸ range N` for a generator `g`, through the sums of coordinates over the orbits.
-/

namespace Langlands.Cohomology.Herbrand

open CategoryTheory

universe u

section Orbits

variable (G X : Type*) [Group G] [MulAction G X]

/-- The order of the stabilizer of a point, as a function on the orbits. -/
noncomputable def orbitStabilizerOrder : Quotient (MulAction.orbitRel G X) → ℕ :=
  Quotient.lift (fun x => Nat.card (MulAction.stabilizer G x))
    (fun _ _ h => Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv)

@[simp]
theorem orbitStabilizerOrder_mk (x : X) :
    orbitStabilizerOrder G X (Quotient.mk'' x) = Nat.card (MulAction.stabilizer G x) :=
  rfl

/-- The product of the orders of the stabilizers, with one factor for each orbit. -/
noncomputable def orbitStabilizerProduct [Finite (Quotient (MulAction.orbitRel G X))] : ℕ :=
  letI := Fintype.ofFinite (Quotient (MulAction.orbitRel G X))
  ∏ q, orbitStabilizerOrder G X q

theorem orbitStabilizerOrder_pos [Finite G] (q : Quotient (MulAction.orbitRel G X)) :
    0 < orbitStabilizerOrder G X q := by
  induction q using Quotient.inductionOn with
  | h x => exact Nat.card_pos

theorem orbitStabilizerProduct_pos [Finite G] [Finite (Quotient (MulAction.orbitRel G X))] :
    0 < orbitStabilizerProduct G X := by
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel G X))
  exact Finset.prod_pos fun q _ => orbitStabilizerOrder_pos G X q

end Orbits

section Permutation

open MonoidAlgebra

variable {G : Type u} [Group G] {X : Type u} [MulAction G X]

/-- The sum of the integer coordinates of an element of `ℤ[X]` over the orbit `q`. -/
noncomputable def orbitSum [Fintype X] (q : Quotient (MulAction.orbitRel G X)) :
    MonoidAlgebra (ULift.{u} ℤ) X →+ ℤ := by
  classical
  exact AddMonoidHom.mk' (fun x => ∑ y : X,
      if (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = q then (x.coeff y).down else 0)
    (fun x x' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp [MonoidAlgebra.coeff_add])

open scoped Classical in
theorem orbitSum_apply [Fintype X] (q : Quotient (MulAction.orbitRel G X))
    (x : MonoidAlgebra (ULift.{u} ℤ) X) :
    orbitSum q x = ∑ y : X,
      if (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = q then (x.coeff y).down else 0 := by
  simp only [orbitSum, AddMonoidHom.mk'_apply]

theorem mk_smul_eq (σ : G) (y : X) :
    (Quotient.mk'' (σ • y) : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' y :=
  Quotient.sound' (MulAction.mem_orbit y σ)

open scoped Classical in
theorem orbitSum_single [Fintype X] (q : Quotient (MulAction.orbitRel G X)) (y : X)
    (r : ULift.{u} ℤ) :
    orbitSum q (single y r) =
      if (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = q then r.down else 0 := by
  classical
  rw [orbitSum_apply, Finset.sum_eq_single y]
  · simp [MonoidAlgebra.coeff_single]
  · intro y' _ hy'
    simp [MonoidAlgebra.coeff_single, Ne.symm hy']
  · simp

theorem orbitSum_ofMulAction [Fintype X] (σ : G) (q : Quotient (MulAction.orbitRel G X))
    (x : MonoidAlgebra (ULift.{u} ℤ) X) :
    orbitSum q (Representation.ofMulAction (ULift.{u} ℤ) G X σ x) = orbitSum q x := by
  classical
  rw [orbitSum_apply, orbitSum_apply]
  refine Fintype.sum_equiv (MulAction.toPerm σ⁻¹) _ _ fun y => ?_
  simp only [MulAction.toPerm_apply, Representation.coeff_ofMulAction, mk_smul_eq]

theorem orbitSum_norm [Fintype G] [Fintype X] (q : Quotient (MulAction.orbitRel G X))
    (x : MonoidAlgebra (ULift.{u} ℤ) X) :
    orbitSum q ((Representation.ofMulAction (ULift.{u} ℤ) G X).norm x) =
      Fintype.card G * orbitSum q x := by
  rw [Representation.norm, LinearMap.sum_apply, map_sum]
  simp only [orbitSum_ofMulAction, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem coeff_smul_of_invariant {x : MonoidAlgebra (ULift.{u} ℤ) X}
    (hx : ∀ σ : G, Representation.ofMulAction (ULift.{u} ℤ) G X σ x = x) (σ : G) (y : X) :
    x.coeff (σ • y) = x.coeff y := by
  calc x.coeff (σ • y) = (Representation.ofMulAction (ULift.{u} ℤ) G X σ x).coeff (σ • y) := by
        rw [hx σ]
    _ = x.coeff y := by rw [Representation.coeff_ofMulAction, inv_smul_smul]

theorem orbitSum_of_invariant [Fintype X] {x : MonoidAlgebra (ULift.{u} ℤ) X}
    (hx : ∀ σ : G, Representation.ofMulAction (ULift.{u} ℤ) G X σ x = x) (b : X) :
    orbitSum (Quotient.mk'' b : Quotient (MulAction.orbitRel G X)) x =
      Nat.card (MulAction.orbit G b) * (x.coeff b).down := by
  classical
  have hc : ∀ y : X, (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' b →
      x.coeff y = x.coeff b := by
    intro y hy
    obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact' hy : y ∈ MulAction.orbit G b)
    exact coeff_smul_of_invariant hx σ b
  have hcard : (Finset.univ.filter fun y : X =>
      (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' b).card =
      Nat.card (MulAction.orbit G b) := by
    rw [Nat.card_eq_card_toFinset (MulAction.orbit G b)]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    exact Quotient.eq''
  rw [orbitSum_apply]
  calc (∑ y : X, if (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' b
        then (x.coeff y).down else 0)
      = ∑ y : X, if (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' b
          then (x.coeff b).down else 0 :=
        Finset.sum_congr rfl fun y _ => by
          split_ifs with h
          · rw [hc y h]
          · rfl
    _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]

theorem orbitSum_eq_zero_of_norm_eq_zero [Fintype G] [Fintype X]
    {x : MonoidAlgebra (ULift.{u} ℤ) X}
    (hx : (Representation.ofMulAction (ULift.{u} ℤ) G X).norm x = 0)
    (q : Quotient (MulAction.orbitRel G X)) : orbitSum q x = 0 := by
  have h := orbitSum_norm q x
  rw [hx, map_zero] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- Moving a basis vector along `g ^ n` changes it by an element of `range (ρ(g) - 1)`. -/
theorem single_sub_single_mem_range (g : G) (z : X) (n : ℕ) :
    single (g ^ n • z) (1 : ULift.{u} ℤ) - single z 1 ∈
      LinearMap.range (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : single (g ^ (n + 1) • z) (1 : ULift.{u} ℤ) - single z 1 =
        (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1) (single (g ^ n • z) 1) +
          (single (g ^ n • z) 1 - single z 1) := by
      rw [LinearMap.sub_apply, Representation.ofMulAction_single, Module.End.one_apply,
        pow_succ', mul_smul]
      abel
    rw [h]
    exact add_mem ⟨_, rfl⟩ ih

/-- An element whose orbit sums all vanish lies in `range (ρ(g) - 1)`. -/
theorem mem_range_of_orbitSum_eq_zero [Finite G] [Fintype X] {g : G}
    (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (x : MonoidAlgebra (ULift.{u} ℤ) X)
    (h : ∀ q : Quotient (MulAction.orbitRel G X), orbitSum q x = 0) :
    x ∈ LinearMap.range (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1) := by
  classical
  let b : X → X := fun y => (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)).out
  have hb : ∀ y, single y (1 : ULift.{u} ℤ) - single (b y) 1 ∈
      LinearMap.range (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1) := by
    intro y
    have hy : y ∈ MulAction.orbit G (b y) :=
      MulAction.mem_orbit_symm.1 (Quotient.mk_out' (s₁ := MulAction.orbitRel G X) y)
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 hy
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, g ^ n = σ :=
      Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg σ))
    have := single_sub_single_mem_range g (b y) n
    rwa [hσ] at this
  have h1 : x = ∑ y, x.coeff y • single y (1 : ULift.{u} ℤ) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
    rw [Finsupp.sum_fintype _ _ fun _ => single_zero _]
    simp
  have h2 : ∑ y, x.coeff y • single (b y) (1 : ULift.{u} ℤ) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ
      (fun y => (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)))]
    refine Finset.sum_eq_zero fun q _ => ?_
    have hbq : ∀ y ∈ Finset.univ.filter
        (fun y => (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = q), b y = q.out := by
      intro y hy
      simp only [b, (Finset.mem_filter.1 hy).2]
    rw [Finset.sum_congr rfl fun y hy => by rw [hbq y hy], ← Finset.sum_smul]
    have hsum : ∑ y ∈ Finset.univ.filter
        (fun y => (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)) = q), x.coeff y = 0 := by
      have hq := h q
      rw [orbitSum_apply, ← Finset.sum_filter] at hq
      apply ULift.ext
      rw [ULift.zero_down, ← hq]
      exact map_sum (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ) _ _
    rw [hsum, zero_smul]
  have hx : x = ∑ y, x.coeff y • (single y (1 : ULift.{u} ℤ) - single (b y) 1) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, h2, sub_zero, ← h1]
  rw [hx]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hb y)

/-- `ker N ⧸ range (ρ(g) - 1)`, that is `H¹(G, ℤ[X])`, is trivial. -/
theorem subsingleton_subquotient_norm [Fintype G] [Fintype X] {g : G}
    (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Subsingleton (Subquotient (Representation.ofMulAction (ULift.{u} ℤ) G X).norm
      (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨x, hx, rfl⟩ := Subquotient.mk_surjective z
  rw [Subquotient.mk_eq_zero_iff]
  exact mem_range_of_orbitSum_eq_zero hg x (orbitSum_eq_zero_of_norm_eq_zero hx)

/-- An element fixed by a generator is fixed by the whole group. -/
theorem invariant_of_sub_one_eq_zero [Finite G] {g : G} (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    {x : MonoidAlgebra (ULift.{u} ℤ) X}
    (hx : (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1) x = 0) (σ : G) :
    Representation.ofMulAction (ULift.{u} ℤ) G X σ x = x := by
  have h1 : Representation.ofMulAction (ULift.{u} ℤ) G X g x = x := by
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, g ^ n = σ :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg σ))
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', map_mul, Module.End.mul_apply, ih, h1]

/-- `ker (ρ(g) - 1) ⧸ range N`, that is `H²(G, ℤ[X])`, has order `∏ |G_x|` (one factor for each
orbit). -/
theorem natCard_subquotient_sub_one [Fintype G] [Fintype X] {g : G}
    (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    Nat.card (Subquotient (Representation.ofMulAction (ULift.{u} ℤ) G X g - 1)
      (Representation.ofMulAction (ULift.{u} ℤ) G X).norm) = orbitStabilizerProduct G X := by
  classical
  set ρ := Representation.ofMulAction (ULift.{u} ℤ) G X with hρ
  let K := LinearMap.ker (ρ g - 1)
  let d := orbitStabilizerOrder G X
  have hd : ∀ q, 0 < d q := orbitStabilizerOrder_pos G X
  have hdq : ∀ q : Quotient (MulAction.orbitRel G X),
      d q = Nat.card (MulAction.stabilizer G q.out) := by
    intro q
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  have hos : ∀ b : X, (Nat.card (MulAction.orbit G b) : ℤ) *
      Nat.card (MulAction.stabilizer G b) = Fintype.card G := by
    intro b
    have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G b
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact_mod_cast this
  have horb : ∀ b : X, (Nat.card (MulAction.orbit G b) : ℤ) ≠ 0 := by
    intro b
    have : Nonempty (MulAction.orbit G b) := ⟨⟨b, MulAction.mem_orbit_self b⟩⟩
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key : ∀ (y : MonoidAlgebra (ULift.{u} ℤ) X), (∀ σ, ρ σ y = y) →
      ∀ q : Quotient (MulAction.orbitRel G X),
        (Nat.card (MulAction.orbit G q.out) : ℤ) * (y.coeff q.out).down = orbitSum q y := by
    intro y hy q
    have := orbitSum_of_invariant hy q.out
    rw [Quotient.out_eq'] at this
    exact this.symm
  let f : K →ₗ[ULift.{u} ℤ] ((q : Quotient (MulAction.orbitRel G X)) → ZMod (d q)) :=
    { toFun := fun x q => (((x : MonoidAlgebra (ULift.{u} ℤ) X).coeff q.out).down : ZMod (d q))
      map_add' := fun x y => by funext q; simp [MonoidAlgebra.coeff_add]
      map_smul' := fun r x => by
        funext q
        show (((r • (x : MonoidAlgebra (ULift.{u} ℤ) X)).coeff q.out).down : ZMod (d q)) =
          r.down • (((x : MonoidAlgebra (ULift.{u} ℤ) X).coeff q.out).down : ZMod (d q))
        rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, ULift.mul_down, Int.cast_mul,
          zsmul_eq_mul] }
  have hf : Function.Surjective f := by
    intro c
    let x : MonoidAlgebra (ULift.{u} ℤ) X := MonoidAlgebra.ofCoeff
      (Finsupp.equivFunOnFinite.symm fun y => ULift.up (((c (Quotient.mk'' y)).val : ℕ) : ℤ))
    have hxc : ∀ y, x.coeff y = ULift.up (((c (Quotient.mk'' y)).val : ℕ) : ℤ) := fun y => rfl
    have hx : x ∈ K := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      apply MonoidAlgebra.coeff_injective
      ext y
      rw [Representation.coeff_ofMulAction, hxc, hxc, mk_smul_eq]
    refine ⟨⟨x, hx⟩, funext fun q => ?_⟩
    have : NeZero (d q) := ⟨(hd q).ne'⟩
    show (((x.coeff q.out).down : ℤ) : ZMod (d q)) = c q
    rw [hxc, Quotient.out_eq']
    simp
  have hker : ∀ x : K, f x = 0 ↔ (x : MonoidAlgebra (ULift.{u} ℤ) X) ∈ LinearMap.range ρ.norm := by
    rintro ⟨x, hx⟩
    have hinv : ∀ σ, ρ σ x = x := invariant_of_sub_one_eq_zero hg hx
    rw [funext_iff]
    change (∀ q, (((x.coeff q.out).down : ℤ) : ZMod (d q)) = (0 : (q : _) → ZMod (d q)) q) ↔
      x ∈ LinearMap.range ρ.norm
    simp_rw [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    symm
    constructor
    · rintro ⟨z, rfl⟩ q
      refine ⟨orbitSum q z, mul_left_cancel₀ (horb q.out) ?_⟩
      rw [key _ (fun σ => ρ.self_norm_apply σ z) q, orbitSum_norm, ← hos q.out, hdq]
      ring
    · intro hdiv
      choose m hm using hdiv
      refine ⟨∑ q, m q • single q.out (1 : ULift.{u} ℤ), ?_⟩
      set z := ∑ q, m q • single q.out (1 : ULift.{u} ℤ) with hzdef
      have hz : ∀ q, orbitSum q z = m q := by
        intro q
        rw [hzdef, map_sum]
        simp only [map_zsmul, orbitSum_single, Quotient.out_eq', smul_eq_mul, mul_ite, mul_zero,
          ULift.one_down, mul_one]
        rw [Finset.sum_ite_eq']
        simp
      have hNinv : ∀ σ, ρ σ (ρ.norm z) = ρ.norm z := fun σ => ρ.self_norm_apply σ z
      apply MonoidAlgebra.coeff_injective
      ext y
      obtain ⟨σ, hσ⟩ : ∃ σ : G,
          σ • (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)).out = y :=
        MulAction.mem_orbit_iff.1
          (MulAction.mem_orbit_symm.1 (Quotient.mk_out' (s₁ := MulAction.orbitRel G X) y))
      rw [← hσ, coeff_smul_of_invariant hNinv, coeff_smul_of_invariant hinv]
      apply mul_left_cancel₀ (horb (Quotient.mk'' y : Quotient (MulAction.orbitRel G X)).out)
      rw [key _ hNinv, orbitSum_norm, hz, hm, ← hos, hdq]
      ring
  obtain ⟨e⟩ := nonempty_linearEquiv_subquotient f hf hker
  have : ∀ q, NeZero (d q) := fun q => ⟨(hd q).ne'⟩
  calc Nat.card (Subquotient (ρ g - 1) ρ.norm)
      = Nat.card ((q : Quotient (MulAction.orbitRel G X)) → ZMod (d q)) :=
        (Nat.card_congr e.toEquiv).symm
    _ = ∏ q, d q := by
        rw [Nat.card_pi]
        simp
    _ = orbitStabilizerProduct G X := by
        unfold orbitStabilizerProduct
        congr!

/-- For a finite cyclic group `G` acting on a finite set `X`, `H¹(G, ℤ[X]) = 0`. -/
theorem subsingleton_groupCohomology_one_ofMulAction [Finite G] [IsCyclic G] [Finite X] :
    Subsingleton (groupCohomology (Rep.ofMulAction (ULift.{u} ℤ) G X) 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  let := Fintype.ofFinite X
  obtain ⟨e⟩ := nonempty_linearEquiv_one hg (Rep.ofMulAction (ULift.{u} ℤ) G X)
  have := subsingleton_subquotient_norm (X := X) hg
  exact e.toEquiv.subsingleton

/-- For a finite cyclic group `G` acting on a finite set `X`, `|H²(G, ℤ[X])| = ∏ |G_x|`, the
product over the orbits of the orders of the stabilizers. -/
theorem natCard_groupCohomology_two_ofMulAction [Finite G] [IsCyclic G] [Finite X] :
    Nat.card (groupCohomology (Rep.ofMulAction (ULift.{u} ℤ) G X) 2) =
      orbitStabilizerProduct G X := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let := Fintype.ofFinite G
  let := Fintype.ofFinite X
  obtain ⟨e⟩ := nonempty_linearEquiv_two hg (Rep.ofMulAction (ULift.{u} ℤ) G X)
  rw [Nat.card_congr e.toEquiv]
  exact natCard_subquotient_sub_one hg

/-- **Herbrand quotient of a permutation lattice.** For a finite cyclic group `G` acting on a
finite set `X`, `H¹(G, ℤ[X])` and `H²(G, ℤ[X])` are finite and the Herbrand quotient of `ℤ[X]`
is `∏ |G_x|`, one factor for each orbit. -/
theorem hasHerbrandQuotient_ofMulAction [Finite G] [IsCyclic G] [Finite X] :
    HasHerbrandQuotient (Rep.ofMulAction (ULift.{u} ℤ) G X) (orbitStabilizerProduct G X) := by
  have h1 := subsingleton_groupCohomology_one_ofMulAction (G := G) (X := X)
  have h2 := natCard_groupCohomology_two_ofMulAction (G := G) (X := X)
  refine (hasHerbrandQuotient_natCast_iff _ _).2 ⟨Finite.of_subsingleton,
    Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h2]
    exact (orbitStabilizerProduct_pos G X).ne'
  · rw [h2, Nat.card_of_subsingleton (0 : groupCohomology (Rep.ofMulAction (ULift.{u} ℤ) G X) 1),
      mul_one]

end Permutation

end Langlands.Cohomology.Herbrand
