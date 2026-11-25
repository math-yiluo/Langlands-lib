# Dual modules and dualizing data

`Langlands/Cohomology/Profinite/Duality/DualModule.lean`, namespace
`Langlands.ProfiniteCohomology`.

For representations `D` and `M` of `G`, the dual `M* = Hom(M, D)` with the action
`(σ f)(m) = σ f(σ⁻¹ m)`, the evaluation pairing `M ⊗ M* → D`, and the duality map
`Hʳ(G, M) → Hom(Hˢ(G, M*), ℤ/n)` given by cup product, evaluation and a map
`t : H^{r+s}(G, D) → ℤ/n`. A *dualizing datum* (Serre's dualizing module, in the form used for
local fields and for Poincaré duality groups) is a module `D ≅ ℤ/n` with, on every open
subgroup `U`, finite cohomology for finite modules killed by `n`, vanishing `H³`, an isomorphism
`t_U : H²(U, D) ≅ ℤ/n` compatible with corestriction, and a perfect cup product pairing
`H¹(U, ℤ/n) × H¹(U, D) → H²(U, D) → ℤ/n`. The main theorem
(`DualizingData.dualityMap_bijective`, in `Main.lean`) says that the duality maps are then
bijective for all finite modules killed by `n`.

## Declarations

General pieces.

- `repIsoOfBijective f hf`: a bijective morphism of representations as an isomorphism
  (`repIsoOfBijective_hom`); `injective_coeffMap_of_bijective f hf n`: a bijective morphism of
  smooth representations is injective on `Hⁿ`.
- `zmodRep G n`: the trivial representation `ℤ/n` (as `ULift (ZMod n)` over `ULift ℤ`);
  `nsmul_zmodRep_eq_zero`, `exponent_zmodRep`, instance `finite_zmodRep`, `zmodRep_eq_zsmul`;
  `zmodRepResIso θ n : Rep.res θ (zmodRep G' n) ≅ zmodRep G n` for a topological isomorphism
  `θ : G ≃ₜ* G'` (the identity of `ℤ/n`).
- `uliftIntLinearEquivAddHom A B`: `ULift ℤ`-linear maps are additive maps
  (`uliftIntLinearEquivAddHom_apply`, `uliftIntLinearEquivAddHom_symm_apply`).
- On `H⁰`: `cocyclesIso₀_hom_comp_f`, `shortComplexH0_f_zeroIso_hom`,
  `zeroIso_hom_cohomology_class_zero (A) [IsSmoothRep A] (z : cocycles A 0) :
  (((zeroIso A).hom.hom (cohomologyπ A 0 z) : A.ρ.invariants) : A) =
  cochainOf A (cocycleι A 0 z) Fin.elim0` (the invariant vector of the class of a `0`-cocycle is its
  value at the empty tuple), `zeroIso_inv_hom_apply`,
  `zeroIso_hom_inv_apply`, `cohomologyMap_zero_comp_zeroIso_hom` (coefficient maps on `H⁰` are
  the maps on invariants).

Duals and the duality map.

- `dualRep D M` (`= (Rep.ihom M).obj D`, `dualRep_eq_ihom`; `dualRep_ρ_apply`), `dualMap D φ`
  (contravariant functoriality: `dualMap_hom_apply`, `dualMap_id`, `dualMap_comp`),
  `dualEvalBilin`, `evalPairing D M : M ⊗ M* → D` (`evalPairing_tmul`, `tensorHom_evalPairing`),
  `toDualDual D M : M → M**` (`toDualDual_hom_apply`), instance `isSmoothRep_dualRep` (for `M`
  finite).
- `bilinAddHom`, `IsPerfectPairing β t` (both maps `X → Hom(Y, ℤ/n)` and `Y → Hom(X, ℤ/n)`
  obtained from `β` and `t` are bijective).
- `dualityMap D h t M : Hʳ(G, M) →+ (Hˢ(G, M*) →+ ℤ/n)`, `x ↦ (y ↦ t(x ∪ y))`
  (`dualityMap_apply`).
- `nsmul_eq_zero_of_nonempty_addEquiv`, `zsmul_eq_zsmul_of_intCast_eq`, `zmodMulAddHom`,
  `bilinOfAddHom`, `zmodMulPairing n D hD : ℤ/n ⊗ D → D` (`zmodMulPairing_tmul`).
- `DualizingData n D` (structure, fields `nonempty_addEquiv`, `finite_cohomology`,
  `subsingleton_cohomology_three`, `t`, `t_cores`, `isPerfectPairing`, as described above).

Characters with values in `ℤ/n`.

- `zmodToQZ n : ℤ/n → ℚ/ℤ` (`zmodToQZ_intCast`, `zmodToQZ_injective`, `exists_zmodToQZ_eq`),
  `zmodOfQZ`, `zmodToQZ_zmodOfQZ`; `zmod_exists_comp_eq_of_ker_le` (extension of characters
  killed by `n`), `zmod_exists_apply_ne_zero` (characters separate points),
  `comp_zmodToQZ_injective`, instance `finite_addMonoidHom_zmod`, `card_addMonoidHom_zmod_le`,
  `bijective_of_bijective_flip` (for finite groups killed by `n`, one side of a pairing bijective
  gives the other).

Finite abelian groups and perfect pairings with values in `ℤ/n`.

- `finite_of_exact_of_finite g f hex`: `B` is finite when `g : A → B`, `f : B → C` with `A`, `C`
  finite and `ker f ⊆ range g`.
- `isUnit_of_surjective_of_eq_mul`: if `f = c · g` for maps `Y → ℤ/n` with `f` surjective, `c` is
  a unit.
- `card_addMonoidHom_zmod_of_nsmul hB : |Hom(B, ℤ/n)| = |B|` for a finite group killed by `n`.
- `annihilatorEquiv S`: homomorphisms vanishing on `S` are homomorphisms from `Y/S`.
- `card_annihilator_left`, `card_annihilator_right`: in a perfect pairing `X × Y → ℤ/n` (through
  `β : X →+ Y →+ Z` and `t : Z →+ ℤ/n`, `IsPerfectPairing β t`) of finite groups killed by `n`, the
  annihilator of `S ⊆ Y` has `|Y|/|S|` elements (resp. that of `A ⊆ X` has `|X|/|A|`);
  `leftAnnihilator β t S`, the annihilator as a subgroup; `mem_of_forall_leftAnnihilator`: a
  subgroup is the annihilator of its annihilator.
- `card_quotient_le_of_pairing`: the common kernel `N` of a finite group `A` of characters
  `G → ℤ/n` has `|G/N| ≤ |A|` (`G/N` embeds into `Hom(A, ℤ/n)`).

Complete types of these and of `zmodRepResIso`, `injective_coeffMap_of_bijective`, as printed by
`PrettyPrinter.ppSignature`:

```lean
Langlands.ProfiniteCohomology.annihilatorEquiv.{u_2} {n : ℕ} {Y : Type u_2} [AddCommGroup Y] (S : AddSubgroup Y) :
  { f // ∀ y ∈ S, f y = 0 } ≃ (Y ⧸ S →+ ZMod n)
Langlands.ProfiniteCohomology.card_addMonoidHom_zmod_of_nsmul.{u_1} {n : ℕ} [NeZero n] {B : Type u_1} [AddCommGroup B]
  [Finite B] (hB : ∀ (b : B), n • b = 0) : Nat.card (B →+ ZMod n) = Nat.card B
Langlands.ProfiniteCohomology.card_annihilator_left.{u_1, u_2, u_3} {n : ℕ} [NeZero n] {X : Type u_1} {Y : Type u_2}
  {Z : Type u_3} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Finite Y] (hY : ∀ (y : Y), n • y = 0)
  {β : X →+ Y →+ Z} {t : Z →+ ZMod n} (hP : Langlands.ProfiniteCohomology.IsPerfectPairing β t) (S : AddSubgroup Y) :
  Nat.card { x // ∀ y ∈ S, t ((β x) y) = 0 } * Nat.card ↥S = Nat.card Y
Langlands.ProfiniteCohomology.card_annihilator_right.{u_1, u_2, u_3} {n : ℕ} [NeZero n] {X : Type u_1} {Y : Type u_2}
  {Z : Type u_3} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Finite X] (hX : ∀ (x : X), n • x = 0)
  {β : X →+ Y →+ Z} {t : Z →+ ZMod n} (hP : Langlands.ProfiniteCohomology.IsPerfectPairing β t) (A : AddSubgroup X) :
  Nat.card { y // ∀ x ∈ A, t ((β x) y) = 0 } * Nat.card ↥A = Nat.card X
Langlands.ProfiniteCohomology.card_quotient_le_of_pairing.{u_4, u_5} {n : ℕ} [NeZero n] {G : Type u_4} [Group G]
  {X : Type u_5} [AddCommGroup X] (A : AddSubgroup X) [Finite ↥A] (c : X → G → ZMod n)
  (hadd : ∀ (x y : X) (g : G), c (x + y) g = c x g + c y g) (hmul : ∀ (x : X) (g h : G), c x (g * h) = c x g + c x h)
  (N : Subgroup G) (hN : ∀ (g : G), g ∈ N ↔ ∀ x ∈ A, c x g = 0) : Nat.card (G ⧸ N) ≤ Nat.card ↥A
Langlands.ProfiniteCohomology.finite_of_exact_of_finite.{u_1, u_2, u_3} {A : Type u_1} {B : Type u_2} {C : Type u_3}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Finite A] [Finite C] (g : A →+ B) (f : B →+ C)
  (hex : ∀ (b : B), f b = 0 → ∃ a, g a = b) : Finite B
Langlands.ProfiniteCohomology.injective_coeffMap_of_bijective.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (f : A ⟶ B) (hf : Function.Bijective ⇑(Rep.Hom.hom f)) (n : ℕ) :
  Function.Injective ⇑(ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap f n))
Langlands.ProfiniteCohomology.isUnit_of_surjective_of_eq_mul.{u_1} {n : ℕ} {Y : Type u_1} [AddCommGroup Y]
  (f g : Y →+ ZMod n) (hf : Function.Surjective ⇑f) (c : ZMod n) (hfg : ∀ (y : Y), f y = c * g y) : IsUnit c
Langlands.ProfiniteCohomology.leftAnnihilator.{u_1, u_2, u_3} {n : ℕ} {X : Type u_1} {Y : Type u_2} {Z : Type u_3}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (β : X →+ Y →+ Z) (t : Z →+ ZMod n) (S : AddSubgroup Y) :
  AddSubgroup X
Langlands.ProfiniteCohomology.mem_of_forall_leftAnnihilator.{u_1, u_2, u_3} {n : ℕ} [NeZero n] {X : Type u_1}
  {Y : Type u_2} {Z : Type u_3} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Finite X] [Finite Y]
  (hX : ∀ (x : X), n • x = 0) (hY : ∀ (y : Y), n • y = 0) {β : X →+ Y →+ Z} {t : Z →+ ZMod n}
  (hP : Langlands.ProfiniteCohomology.IsPerfectPairing β t) (S : AddSubgroup Y) {y : Y}
  (hy : ∀ x ∈ Langlands.ProfiniteCohomology.leftAnnihilator β t S, t ((β x) y) = 0) : y ∈ S
Langlands.ProfiniteCohomology.zmodRepResIso.{u} {G G' : Type u} [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] (θ : G ≃ₜ* G') (n : ℕ) :
  Rep.res (↑θ) (Langlands.ProfiniteCohomology.zmodRep G' n) ≅ Langlands.ProfiniteCohomology.zmodRep G n
```

Duals of torsion modules.

- `zmodULiftModule`, `nsmul_dualRep_eq_zero`, `finite_of_nonempty_addEquiv`, instance
  `finite_dualRep`, `card_dualRep_le`, `exists_dualRep_apply_ne_zero`, `bijective_toDualDual`
  (biduality for finite modules killed by `n`, when `D ≅ ℤ/n`).
- `dualEvalAt D X x hx`, `tensorHom_dualEvalAt`: evaluation at an invariant vector.
- `dualShortComplex D S`: the dual of a short complex, short exact when `S` is short exact and
  killed by `n` (`dualShortComplex_injective_f`, `dualShortComplex_exact`,
  `dualShortComplex_surjective_g`, `dualShortComplex_shortExact`).
- `zmodDualHom`, `zmodDualHom_hom_apply`, `dualRep_zmodRep_apply`, `bijective_zmodDualHom`,
  `zmodDualIso : Hom(ℤ/n, D) ≅ D` and `tensorHom_zmodDualIso_zmodMulPairing` (under this
  isomorphism the evaluation pairing is the multiplication pairing).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/NsmulEqZeroOfNonemptyAddEquiv.lean`,
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/Torsion.lean`,
`src/GroundTheory/ProfiniteCohomology/PoincareDuality/TensorHomZmodDualIsoZmodMulPairing.lean`,
and, for the general pieces, `src/GroundTheory/ProfiniteCohomology/CartierDualDefs.lean`
(`Rep.isoOfBijective`, `zmodRep`), `src/GroundTheory/ProfiniteCohomology/CartierDual.lean`
(`uliftIntLinearEquivAddHom`, `nsmul_zmodRep_eq_zero`, `exponent_zmodRep`, `finite_zmodRep`,
`zmodRep_eq_zsmul`) and `src/GroundTheory/ProfiniteCohomology/GaloisCohomology/Kummer.lean`
(the lemmas on `H⁰`), with `zeroIso_hom_cohomology_class_zero` from
`src/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/H0IsoHomCohomologyClassZero.lean`
and `finite_of_exact_of_finite` from
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseInputs.lean` (lines 17–22). The
perfect-pairing lemmas, `isUnit_of_surjective_of_eq_mul`, `zmodRepResIso` and
`injective_coeffMap_of_bijective` contain no text of the source.
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

Names: `DualityHypotheses` → `DualizingData`; `Rep.isoOfBijective` → `repIsoOfBijective` (the
name `Rep.isoOfBijective` is to be kept free for Mathlib); `H0Iso` → `zeroIso` in the names of the
lemmas on `H⁰`; the other names are the source's.

## References

- J.-P. Serre, *Galois Cohomology* (English translation of *Cohomologie galoisienne*, Springer 1997;
  corrected printing 2002), chapter I, §3.5, Proposition 17 and Remark 2, pp. 24–25 (the dualizing
  module `I`, representing `A ↦ Hⁿ(G, A)*` on finite modules when `cd(G) ≤ n`), and chapter II,
  §5.2, Theorems 1 and 2, p. 91 (for a `p`-adic field the dualizing module is `μ`; duality for
  finite modules).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter III, §4, Theorem (3.4.1), p. 182 (dualizing module), and Duality
  Theorems (3.4.3), p. 183, and (3.4.6), p. 186.

Serre and Neukirch–Schmidt–Wingberg construct the dualizing module from the cohomology of a group of
finite cohomological dimension; the dualizing datum here is given by hypotheses on `D ≅ ℤ/n` and on
the cohomology of the open subgroups.
