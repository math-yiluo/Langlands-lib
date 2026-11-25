/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Instances.ZMod
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor

/-!
# Morphisms of torsors from monodromy, connectedness, and lifting of characters

Let `Y` be a connected scheme with geometric point `s` and fundamental group `G = π₁(Y, s)`.
By the Galois correspondence `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction`, a
`G`-equivariant map of geometric fibres of finite étale `Y`-schemes comes from a unique morphism
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_hom_fiber_map_eq`), and a finite étale `Y`-scheme
whose geometric fibre is a single nonempty `G`-orbit is connected
(`AlgebraicGeometry.Scheme.FiniteEtale.isConnected_of_exists_smul_eq`).

For torsors this gives:

* a morphism `P ⟶ P'` from an `M`-torsor to an `M'`-torsor, equivariant along `φ : M →+ M'`,
  as soon as the monodromy characters satisfy `φ ∘ f_P = f_{P'}`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_hom_of_monodromy`);
* the total space of a torsor with surjective monodromy is connected
  (`AlgebraicGeometry.Scheme.EtaleTorsor.connectedSpace_of_surjective_monodromy`);
* a torsor with trivial monodromy has a section
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_monodromy_eq_one`), and conversely
  (`AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_eq_one_of_section`).

Finally, if `G` has exactly `l ^ (r k)` continuous characters with values in `ℤ / lᵏ` for
`k ≤ n`, every nontrivial character `χ : G → ℤ / lⁿ` is of the form `lᵃ χ'` with `a < n` and `χ'`
surjective (`ContinuousMonoidHom.exists_surjective_of_card_eq`): the reduction of characters
`Hom(G, ℤ / lᵐ⁺¹) → Hom(G, ℤ / lᵐ)` is surjective by counting, and a non-surjective character
takes values in `l ℤ / lᵐ⁺¹ ≅ ℤ / lᵐ`, hence is `l` times a character. In the torsor language:
a `ℤ / lⁿ`-torsor without section is, at the level of monodromy, `lᵃ` times a torsor with
surjective monodromy (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_monodromy_eq_pow_smul`).
-/

@[expose] public section

universe u v

open CategoryTheory Limits PreGaloisCategory

namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]
  {M M' : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']

/-- Postcomposition of continuous characters with values in a discrete abelian group with an
additive homomorphism `φ : M →+ M'`. -/
def postcompAddMonoidHom (φ : M →+ M') :
    (G →ₜ* Multiplicative M) →* (G →ₜ* Multiplicative M') where
  toFun ψ := ContinuousMonoidHom.comp
    ⟨AddMonoidHom.toMultiplicative φ, continuous_of_discreteTopology⟩ ψ
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
lemma toAdd_postcompAddMonoidHom_apply (φ : M →+ M') (ψ : G →ₜ* Multiplicative M) (g : G) :
    (postcompAddMonoidHom φ ψ g).toAdd = φ (ψ g).toAdd := rfl

/-- A continuous character with values in the range of an injective homomorphism `φ` factors
through `φ`. -/
lemma exists_postcompAddMonoidHom_eq {φ : M →+ M'} (hφ : Function.Injective φ)
    (ψ : G →ₜ* Multiplicative M') (h : ∀ g, (ψ g).toAdd ∈ φ.range) :
    ∃ ψ₀, postcompAddMonoidHom φ ψ₀ = ψ := by
  choose f hf using h
  refine ⟨⟨⟨⟨fun g ↦ .ofAdd (f g), ?_⟩, fun g h ↦ ?_⟩, ?_⟩, ?_⟩
  · exact ofAdd_eq_one.mpr (hφ (by rw [hf, map_one, toAdd_one, map_zero]))
  · change Multiplicative.ofAdd (f (g * h)) =
      Multiplicative.ofAdd (f g) * Multiplicative.ofAdd (f h)
    rw [← ofAdd_add]
    exact congrArg _ (hφ (by rw [map_add, hf, hf, hf, map_mul, toAdd_mul]))
  · refine continuous_discrete_rng.mpr fun y ↦ ?_
    have : (fun g ↦ Multiplicative.ofAdd (f g)) ⁻¹' {y} =
        ψ ⁻¹' {Multiplicative.ofAdd (φ y.toAdd)} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        rw [toAdd_ofAdd, hf, ofAdd_toAdd]
      · intro hg
        apply Multiplicative.toAdd.injective
        apply hφ
        rw [toAdd_ofAdd, hf, hg, toAdd_ofAdd]
    rw [this]
    exact (isOpen_discrete _).preimage ψ.continuous
  · ext g
    change Multiplicative.ofAdd (φ (f g)) = ψ g
    rw [hf, ofAdd_toAdd]

/-- Postcomposition with `φ` is surjective on continuous characters as soon as the numbers of
characters satisfy `#Hom(G, M) = #ker · #Hom(G, M')`. -/
lemma surjective_postcompAddMonoidHom_of_card (φ : M →+ M')
    (hcard : Nat.card (G →ₜ* Multiplicative M) =
      Nat.card (postcompAddMonoidHom (G := G) φ).ker * Nat.card (G →ₜ* Multiplicative M'))
    (h0 : Nat.card (G →ₜ* Multiplicative M) ≠ 0) :
    Function.Surjective (postcompAddMonoidHom (G := G) φ) := by
  set f := postcompAddMonoidHom (G := G) φ
  have : Finite (G →ₜ* Multiplicative M) := Nat.finite_of_card_ne_zero h0
  have hk : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hcard] at h1
  have h2 : Nat.card f.range = Nat.card (G →ₜ* Multiplicative M') :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h1
  have : Finite f.range := Set.finite_range f
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h2)

end ContinuousMonoidHom

namespace ZMod

variable (l : ℕ)

/-- Multiplication by `l`, as an additive map `ℤ / lᵐ → ℤ / lᵐ⁺¹`. -/
def mulLeftPowSucc (m : ℕ) : ZMod (l ^ m) →+ ZMod (l ^ (m + 1)) :=
  ZMod.lift (l ^ m) ⟨zmultiplesHom _ (l : ZMod (l ^ (m + 1))), by
    rw [zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ← pow_succ,
      ZMod.natCast_self]⟩

lemma mulLeftPowSucc_natCast (m k : ℕ) :
    mulLeftPowSucc l m (k : ZMod (l ^ m)) = ((k * l : ℕ) : ZMod (l ^ (m + 1))) := by
  rw [← Int.cast_natCast, mulLeftPowSucc, ZMod.lift_coe, zmultiplesHom_apply, zsmul_eq_mul,
    Int.cast_natCast, Nat.cast_mul]

/-- The inclusion `ℤ / l ⟶ ℤ / lᵐ⁺¹`, `x ↦ lᵐ x`, of the `l`-torsion. -/
def mulLeftPowTorsion (m : ℕ) : ZMod l →+ ZMod (l ^ (m + 1)) :=
  ZMod.lift l ⟨zmultiplesHom _ ((l ^ m : ℕ) : ZMod (l ^ (m + 1))), by
    rw [zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ← pow_succ',
      ZMod.natCast_self]⟩

lemma mulLeftPowTorsion_natCast (m k : ℕ) :
    mulLeftPowTorsion l m (k : ZMod l) = ((k * l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
  rw [← Int.cast_natCast, mulLeftPowTorsion, ZMod.lift_coe, zmultiplesHom_apply, zsmul_eq_mul,
    Int.cast_natCast, Nat.cast_mul]

/-- The reduction `ℤ / lᵐ⁺¹ ⟶ ℤ / lᵐ`. -/
def reducePowSucc (m : ℕ) : ZMod (l ^ (m + 1)) →+ ZMod (l ^ m) :=
  (ZMod.castHom (pow_dvd_pow l m.le_succ) _).toAddMonoidHom

lemma reducePowSucc_natCast (m k : ℕ) :
    reducePowSucc l m (k : ZMod (l ^ (m + 1))) = (k : ZMod (l ^ m)) :=
  map_natCast (ZMod.castHom (pow_dvd_pow l m.le_succ) _) k

variable {l} [Fact l.Prime]

lemma mulLeftPowSucc_reducePowSucc (m : ℕ) (x : ZMod (l ^ (m + 1))) :
    mulLeftPowSucc l m (reducePowSucc l m x) = l • x := by
  rw [← x.natCast_zmod_val, reducePowSucc_natCast, mulLeftPowSucc_natCast, nsmul_eq_mul,
    Nat.cast_mul, mul_comm]

lemma injective_mulLeftPowSucc (m : ℕ) : Function.Injective (mulLeftPowSucc l m) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ hl⟩
  refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
  rw [← y.natCast_zmod_val, mulLeftPowSucc_natCast, ZMod.natCast_eq_zero_iff, pow_succ] at hy
  rw [← y.natCast_zmod_val, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hl) hy

lemma injective_mulLeftPowTorsion (m : ℕ) : Function.Injective (mulLeftPowTorsion l m) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero l := ⟨hl⟩
  refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
  rw [← y.natCast_zmod_val, mulLeftPowTorsion_natCast, ZMod.natCast_eq_zero_iff, pow_succ'] at hy
  rw [← y.natCast_zmod_val, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (pow_ne_zero _ hl)) hy

lemma reducePowSucc_eq_zero_iff (m : ℕ) (x : ZMod (l ^ (m + 1))) :
    reducePowSucc l m x = 0 ↔ x ∈ (mulLeftPowTorsion l m).range := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl⟩
  constructor
  · intro hx
    rw [← x.natCast_zmod_val, reducePowSucc_natCast, ZMod.natCast_eq_zero_iff] at hx
    obtain ⟨j, hj⟩ := hx
    refine ⟨(j : ZMod l), ?_⟩
    rw [mulLeftPowTorsion_natCast, ← x.natCast_zmod_val, hj, mul_comm]
  · rintro ⟨y, rfl⟩
    have : NeZero l := ⟨hl⟩
    rw [← y.natCast_zmod_val, mulLeftPowTorsion_natCast, reducePowSucc_natCast,
      ZMod.natCast_eq_zero_iff]
    exact dvd_mul_left _ _

/-- An element of `ℤ / lᵐ⁺¹` outside `l ℤ / lᵐ⁺¹` is a unit. -/
lemma isUnit_of_notMem_range_mulLeftPowSucc (m : ℕ) (x : ZMod (l ^ (m + 1)))
    (hx : x ∉ (mulLeftPowSucc l m).range) : IsUnit x := by
  have hl : l.Prime := Fact.out
  have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← x.natCast_zmod_val, isUnit_natCast_iff_not_dvd_pow hl m.succ_pos]
  rintro ⟨j, hj⟩
  refine hx ⟨(j : ZMod (l ^ m)), ?_⟩
  rw [mulLeftPowSucc_natCast, ← x.natCast_zmod_val, hj, mul_comm]

end ZMod

namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G] {l : ℕ} [Fact l.Prime]

/-- The additive map `ULift A →+ ULift B` induced by `φ : A →+ B`. -/
def _root_.AddMonoidHom.uliftMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) : ULift.{v} A →+ ULift.{v} B :=
  AddEquiv.ulift.symm.toAddMonoidHom.comp (φ.comp AddEquiv.ulift.toAddMonoidHom)

@[simp]
lemma _root_.AddMonoidHom.uliftMap_apply_down {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (x : ULift.{v} A) : (φ.uliftMap x).down = φ x.down := rfl

lemma _root_.AddMonoidHom.uliftMap_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {φ : A →+ B} (hφ : Function.Injective φ) :
    Function.Injective (φ.uliftMap : ULift.{v} A →+ ULift.{v} B) :=
  fun _ _ h ↦ ULift.ext (hφ (congrArg ULift.down h))

/-- A continuous character `G → ℤ / lᵐ⁺¹` which is not surjective is `l` times a character,
provided that `G` has `l ^ (r k)` characters with values in `ℤ / lᵏ` for `k = 1, m, m + 1`: its
values lie in `l ℤ / lᵐ⁺¹ ≅ ℤ / lᵐ`, and the reduction `Hom(G, ℤ / lᵐ⁺¹) → Hom(G, ℤ / lᵐ)` is
surjective since its kernel `Hom(G, ℤ / l)` has `l ^ r` elements. -/
lemma exists_eq_smul_of_not_surjective {m r : ℕ}
    (h1 : Nat.card (G →ₜ* Multiplicative (ULift.{v} (ZMod l))) = l ^ r)
    (hm : Nat.card (G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ m)))) = l ^ (r * m))
    (hm1 : Nat.card (G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ (m + 1))))) =
      l ^ (r * (m + 1)))
    (ψ : G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ (m + 1)))))
    (hψ : ¬ Function.Surjective fun g ↦ (ψ g).toAdd.down) :
    ∃ ψ₁ : G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ (m + 1)))),
      ∀ g, (ψ g).toAdd = l • (ψ₁ g).toAdd := by
  have hl : l.Prime := Fact.out
  -- the values of `ψ` are divisible by `l`
  have hval (g : G) : (ψ g).toAdd ∈ ((ZMod.mulLeftPowSucc l m).uliftMap).range := by
    by_contra hg
    refine hψ fun y ↦ ?_
    have hu : IsUnit (ψ g).toAdd.down := ZMod.isUnit_of_notMem_range_mulLeftPowSucc m _
      fun ⟨z, hz⟩ ↦ hg ⟨ULift.up z, ULift.ext hz⟩
    obtain ⟨u, hu⟩ := hu
    refine ⟨g ^ (y * u⁻¹ : ZMod (l ^ (m + 1))).val, ?_⟩
    have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
    change (ψ (g ^ _)).toAdd.down = y
    rw [map_pow, toAdd_pow, ULift.smul_down, nsmul_eq_mul, ZMod.natCast_zmod_val, ← hu,
      mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨ψ₀, hψ₀⟩ := exists_postcompAddMonoidHom_eq
    (AddMonoidHom.uliftMap_injective (ZMod.injective_mulLeftPowSucc m)) ψ hval
  -- the reduction of characters is surjective
  set red := postcompAddMonoidHom (G := G)
    ((ZMod.reducePowSucc l m).uliftMap : ULift.{v} _ →+ ULift.{v} _)
  set inc := postcompAddMonoidHom (G := G)
    ((ZMod.mulLeftPowTorsion l m).uliftMap : ULift.{v} _ →+ ULift.{v} _)
  have hinc : Function.Injective inc := fun a b hab ↦ ContinuousMonoidHom.ext fun g ↦ by
    have := congrArg (fun f ↦ (f g).toAdd) hab
    simp only [inc, toAdd_postcompAddMonoidHom_apply] at this
    exact Multiplicative.toAdd.injective
      (AddMonoidHom.uliftMap_injective (ZMod.injective_mulLeftPowTorsion m) this)
  have hker : red.ker = inc.range := by
    ext χ
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hχ
      refine exists_postcompAddMonoidHom_eq
        (AddMonoidHom.uliftMap_injective (ZMod.injective_mulLeftPowTorsion m)) χ fun g ↦ ?_
      have := congrArg (fun f ↦ (f g).toAdd.down) hχ
      simp only [red, toAdd_postcompAddMonoidHom_apply, AddMonoidHom.uliftMap_apply_down,
        ContinuousMonoidHom.coe_one, Pi.one_apply, toAdd_one, ULift.zero_down] at this
      obtain ⟨z, hz⟩ := (ZMod.reducePowSucc_eq_zero_iff m _).mp this
      exact ⟨ULift.up z, ULift.ext hz⟩
    · rintro ⟨χ₀, rfl⟩
      refine ContinuousMonoidHom.ext fun g ↦ ?_
      apply Multiplicative.toAdd.injective
      refine ULift.ext ?_
      simp only [red, inc, toAdd_postcompAddMonoidHom_apply, AddMonoidHom.uliftMap_apply_down,
        ContinuousMonoidHom.coe_one, Pi.one_apply, toAdd_one, ULift.zero_down]
      exact (ZMod.reducePowSucc_eq_zero_iff m _).mpr ⟨_, rfl⟩
  have hcardker : Nat.card red.ker = l ^ r := by
    rw [hker, ← Nat.card_congr (MonoidHom.ofInjective hinc).toEquiv, h1]
  have hsurj : Function.Surjective red := surjective_postcompAddMonoidHom_of_card _
    (by rw [hcardker, hm1, hm, ← pow_add, mul_add, mul_one, add_comm])
    (by rw [hm1]; exact pow_ne_zero _ hl.ne_zero)
  obtain ⟨ψ₁, hψ₁⟩ := hsurj ψ₀
  refine ⟨ψ₁, fun g ↦ ULift.ext ?_⟩
  rw [← hψ₀, ← hψ₁]
  simp only [red, toAdd_postcompAddMonoidHom_apply, AddMonoidHom.uliftMap_apply_down,
    ZMod.mulLeftPowSucc_reducePowSucc, ULift.smul_down]

/-- **Lifting of characters.** Let `G` be a topological group with exactly `l ^ (r k)`
continuous characters with values in `ℤ / lᵏ` for every `k ≤ n`. Then every nontrivial
continuous character `χ : G → ℤ / lⁿ` is `lᵃ χ'` for some `a < n` and some surjective continuous
character `χ' : G → ℤ / lⁿ`: take `a` maximal with `χ ∈ lᵃ Hom(G, ℤ / lⁿ)`; a non-surjective `χ'`
would be divisible by `l` (`ContinuousMonoidHom.exists_eq_smul_of_not_surjective`). -/
theorem exists_surjective_of_card_eq {n r : ℕ}
    (hcard : ∀ k ≤ n, Nat.card (G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ k)))) = l ^ (r * k))
    (χ : G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ n)))) (hχ : χ ≠ 1) :
    ∃ a < n, ∃ χ' : G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ n))),
      Function.Surjective (fun g ↦ (χ' g).toAdd.down) ∧
        ∀ g, (χ g).toAdd = l ^ a • (χ' g).toAdd := by
  let P : ℕ → Prop := fun a ↦ ∃ χ' : G →ₜ* Multiplicative (ULift.{v} (ZMod (l ^ n))),
    ∀ g, (χ g).toAdd = l ^ a • (χ' g).toAdd
  have hP0 : P 0 := ⟨χ, fun g ↦ by rw [pow_zero, one_smul]⟩
  have hPn (a : ℕ) (ha : n ≤ a) : ¬ P a := by
    rintro ⟨χ', hχ'⟩
    refine hχ (ContinuousMonoidHom.ext fun g ↦ ?_)
    rw [ContinuousMonoidHom.coe_one, Pi.one_apply, ← toAdd_eq_zero, hχ' g]
    refine ULift.ext ?_
    rw [ULift.smul_down, ULift.zero_down, nsmul_eq_mul,
      (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow l ha), zero_mul]
  obtain ⟨a, ⟨χ', hχ'⟩, hna⟩ : ∃ a, P a ∧ ¬ P (a + 1) := by
    by_contra! H
    exact hPn n le_rfl (Nat.rec hP0 (fun a ha ↦ H a ha) n)
  have ha : a < n := lt_of_not_ge fun h ↦ hPn a h ⟨χ', hχ'⟩
  refine ⟨a, ha, χ', ?_, hχ'⟩
  by_contra hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := hcard 1 (by omega)
  rw [pow_one, mul_one] at h1
  obtain ⟨ψ₁, hψ₁⟩ := exists_eq_smul_of_not_surjective h1 (hcard m (by omega))
    (hcard (m + 1) le_rfl) χ' hs
  exact hna ⟨ψ₁, fun g ↦ by rw [hχ', hψ₁, smul_smul, ← pow_succ]⟩

end ContinuousMonoidHom

namespace AlgebraicGeometry.Scheme

namespace FiniteEtale

open scoped FintypeCatDiscrete

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- A `G`-equivariant map of geometric fibres of finite étale `Y`-schemes is induced by a
morphism, by full faithfulness of the Galois correspondence
`AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction`. -/
lemma exists_hom_fiber_map_eq {X Z : Y.FiniteEtale} (ψ : (fiber s).obj X → (fiber s).obj Z)
    (hψ : ∀ (g : G) x, ψ (g • x) = g • ψ x) :
    ∃ f : X ⟶ Z, ∀ x, (fiber s).map f x = ψ x := by
  let E := equivalenceContAction s G
  let I : E.functor.obj X ⟶ E.functor.obj Z := ObjectProperty.homMk
    { hom := FintypeCat.homMk ψ
      comm g := FintypeCat.hom_ext _ _ fun x ↦ hψ g x }
  exact ⟨E.fullyFaithfulFunctor.preimage I, fun x ↦
    congrArg (fun f ↦ f.hom.hom x) (E.fullyFaithfulFunctor.map_preimage I)⟩

/-- A finite étale `Y`-scheme whose geometric fibre is a single nonempty orbit of the fundamental
group is a connected object of `FÉt(Y)`: the fibre of a non-initial subobject is a nonempty
`G`-stable subset, hence everything. -/
lemma isConnected_of_exists_smul_eq (P : Y.FiniteEtale) [Nonempty ((fiber s).obj P)]
    (h : ∀ x y : (fiber s).obj P, ∃ g : G, g • x = y) : IsConnected P := by
  refine ⟨fun hP ↦ ?_, fun Z i _ hZ ↦ ?_⟩
  · have := (initial_iff_fiber_empty (fiber s) P).1 ⟨hP⟩
    obtain ⟨x⟩ := ‹Nonempty ((fiber s).obj P)›
    exact IsEmpty.false x
  · obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty (fiber s) Z).1 hZ
    have hs : Function.Surjective ((fiber s).map i) := fun y ↦ by
      obtain ⟨g, hg⟩ := h ((fiber s).map i z) y
      exact ⟨g • z, (IsNaturalSMul.naturality g i z).trans hg⟩
    by_contra hni
    exact (Nat.card_le_card_of_surjective _ hs).not_gt
      (lt_card_fiber_of_mono_of_notIso (fiber s) i hni)

end FiniteEtale

namespace EtaleTorsor

open FiniteEtale

open scoped FintypeCatDiscrete

variable {M M' : Type (u + 1)} [AddCommGroup M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M] [AddCommGroup M'] [Finite M'] [TopologicalSpace M'] [DiscreteTopology M']
  {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- **Morphisms of torsors from monodromy.** Let `φ : M →+ M'` and let `P`, `P'` be an `M`-torsor
and an `M'`-torsor over `Y` whose monodromy characters satisfy `φ ∘ f_P = f_{P'}`. Then there is a
morphism `P ⟶ P'` over `Y` which is `φ`-equivariant: choosing points `p ∈ P_s`, `p' ∈ P'_s`, the
map `m +ᵥ p ↦ φ m +ᵥ p'` of geometric fibres is `π₁(Y, s)`-equivariant, hence comes from a
morphism of finite étale `Y`-schemes. -/
theorem exists_hom_of_monodromy (φ : M →+ M') (t : EtaleTorsor M Y) (t' : EtaleTorsor M' Y)
    (h : ∀ g, φ (t.monodromy s G g).toAdd = (t'.monodromy s G g).toAdd) :
    ∃ f : t.P ⟶ t'.P, f ≫ t'.π = t.π ∧ ∀ a, t.vadd a ≫ f = f ≫ t'.vadd (φ a) := by
  let p := (t.nonempty_fiber s).some
  let p' := (t'.nonempty_fiber s).some
  choose d hd using t.exists_fiber_map_vaddHom s p
  have hd' (m : M) : d ((fiber s).map (t.vaddHom m) p) = m :=
    t.eq_of_fiber_map_vaddHom_eq s p (hd _)
  let ψ : (fiber s).obj t.toFiniteEtale → (fiber s).obj t'.toFiniteEtale :=
    fun x ↦ (fiber s).map (t'.vaddHom (φ (d x))) p'
  have hvadd (m : M) (x : (fiber s).obj t.toFiniteEtale) :
      ψ ((fiber s).map (t.vaddHom m) x) = (fiber s).map (t'.vaddHom (φ m)) (ψ x) := by
    have : (fiber s).map (t.vaddHom m) x = (fiber s).map (t.vaddHom (d x + m)) p := by
      rw [← fiber_map_vaddHom_vaddHom, hd]
    simp only [ψ]
    rw [this, hd', fiber_map_vaddHom_vaddHom, map_add]
  have hsmul (g : G) (x : (fiber s).obj t.toFiniteEtale) : ψ (g • x) = g • ψ x := by
    rw [← t.fiber_map_vaddHom_monodromy s G g x, hvadd, h,
      t'.fiber_map_vaddHom_monodromy s G g (ψ x)]
  obtain ⟨F, hF⟩ := exists_hom_fiber_map_eq s G ψ hsmul
  refine ⟨F.hom.left, hom_left_comp F, fun a ↦ ?_⟩
  have : t.vaddHom a ≫ F = F ≫ t'.vaddHom (φ a) := by
    refine (fiber s).map_injective (FintypeCat.hom_ext _ _ fun x ↦ ?_)
    rw [Functor.map_comp, Functor.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply, hF,
      hF, hvadd]
  exact congrArg (fun f ↦ f.hom.left) this

/-- **Torsors with surjective monodromy are connected.** If the monodromy character of an
`M`-torsor `P` is surjective, then `π₁(Y, s)` acts transitively on the geometric fibre `P_s`
(on which `M` acts simply transitively), so `P` is connected. -/
theorem connectedSpace_of_surjective_monodromy (t : EtaleTorsor M Y)
    (h : Function.Surjective fun g ↦ (t.monodromy s G g).toAdd) : ConnectedSpace t.P := by
  have : Nonempty ((fiber s).obj t.toFiniteEtale) := t.nonempty_fiber s
  have : IsConnected t.toFiniteEtale := isConnected_of_exists_smul_eq s G _ fun x y ↦ by
    obtain ⟨m, hm⟩ := t.exists_fiber_map_vaddHom s x y
    obtain ⟨g, hg⟩ := h m
    have hg' : (t.monodromy s G g).toAdd = m := hg
    exact ⟨g, (t.fiber_map_vaddHom_monodromy s G g x).symm.trans (hg' ▸ hm)⟩
  exact connectedSpace_of_isConnected t.toFiniteEtale

/-- A torsor with trivial monodromy has a section: a point `p` of the geometric fibre is fixed
by `π₁(Y, s)`, so the map from the geometric fibre of `Y` sending its unique point to `p` comes
from a morphism `Y ⟶ P` over `Y`. -/
theorem exists_section_of_monodromy_eq_one (t : EtaleTorsor M Y) (h : t.monodromy s G = 1) :
    ∃ σ : Y ⟶ t.P, σ ≫ t.π = 𝟙 Y := by
  let T : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance,
    inferInstanceAs (IsFinite (𝟙 Y))⟩
  let p := (t.nonempty_fiber s).some
  have hp (g : G) : g • p = p := by
    rw [← t.fiber_map_vaddHom_monodromy s G g p, h, ContinuousMonoidHom.coe_one, Pi.one_apply,
      toAdd_one, fiber_map_vaddHom_zero]
  obtain ⟨F, -⟩ := exists_hom_fiber_map_eq s G (X := T) (fun _ ↦ p) fun g _ ↦ (hp g).symm
  exact ⟨F.hom.left, hom_left_comp F⟩

/-- A torsor with a section has trivial monodromy: the point of the geometric fibre through the
section is the image of the unique point of the geometric fibre of `Y` itself, which is fixed by
`G`. -/
lemma monodromy_eq_one_of_section (t : EtaleTorsor M Y) {σ : Y ⟶ t.P} (hσ : σ ≫ t.π = 𝟙 Y) :
    t.monodromy s G = 1 := by
  let T : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance,
    inferInstanceAs (IsFinite (𝟙 Y))⟩
  let S : T ⟶ t.toFiniteEtale := ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  let x₀ : (fiber s).obj T := Over.homMk s (Category.comp_id s)
  have hx₀ (g : G) : g • x₀ = x₀ := fiber_ext s <| by
    rw [← Category.comp_id (g • x₀).left, ← Category.comp_id x₀.left]
    exact (fiber_left_comp s (g • x₀)).trans (fiber_left_comp s x₀).symm
  ext g
  let x := (fiber s).map S x₀
  refine congrArg Multiplicative.toAdd ((t.monodromy_eq_iff s G g x 0).mpr ?_)
  rw [t.fiber_map_vaddHom_zero s, ← IsNaturalSMul.naturality g S x₀, hx₀]

/-- **Lifting of torsors.** Let `l` be a prime and suppose that `π₁(Y, s)` has exactly
`l ^ (r k)` continuous characters with values in `ℤ / lᵏ` for `k ≤ n`. A `ℤ / lⁿ`-torsor `P`
without section has nontrivial monodromy, so by
`ContinuousMonoidHom.exists_surjective_of_card_eq` there are `a < n` and a `ℤ / lⁿ`-torsor `P'`
with surjective monodromy such that `f_P = lᵃ f_{P'}`. -/
theorem exists_monodromy_eq_pow_smul {l : ℕ} [Fact l.Prime] {n r : ℕ}
    (hcard : ∀ k ≤ n, Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ k)))) =
      l ^ (r * k))
    (t : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) Y)
    (ht : ¬ ∃ σ : Y ⟶ t.P, σ ≫ t.π = 𝟙 Y) :
    ∃ a < n, ∃ t' : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) Y,
      Function.Surjective (fun g ↦ (t'.monodromy s G g).toAdd.down) ∧
        ∀ g, (t.monodromy s G g).toAdd = l ^ a • (t'.monodromy s G g).toAdd := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨a, ha, χ', hs, hχ'⟩ := ContinuousMonoidHom.exists_surjective_of_card_eq hcard
    (t.monodromy s G) fun h ↦ ht (t.exists_section_of_monodromy_eq_one s G h)
  obtain ⟨t', rfl⟩ := exists_monodromy_eq s G χ'
  exact ⟨a, ha, t', hs, hχ'⟩

end EtaleTorsor

end AlgebraicGeometry.Scheme
