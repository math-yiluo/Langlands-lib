# Commutative trivial square-zero extensions

Module `Langlands.Algebra.ThickSquareZero`, namespace `Langlands.Algebra.Thick` (the type
itself is `Langlands.Algebra.Thick`). Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Pure commutative algebra in one universe `u`. Everything is proved in the file,
with no hypotheses beyond those in the signatures.

## The ring

For a commutative ring `A` and an `A`-module `F`, `Thick A F` is the trivial square-zero
extension `A ⊕ F` with multiplication `(a, f) * (a', f') = (a * a', a • f' + a' • f)`.
It is defined as Mathlib's `TrivSqZeroExt A F`. Mathlib's commutative ring structure on
`TrivSqZeroExt` needs a right action `Module Aᵐᵒᵖ F` with `IsCentralScalar A F`, and a
plain `A`-module does not carry one. The instance `instCommRing` therefore supplies,
locally, the right action equal to the left one: `Module.compHom` along
`(RingEquiv.toOpposite A).symm`. The new name keeps this choice out of instance search on
`TrivSqZeroExt`.

## Declarations

- `mk a f`, `fst`, `snd`, `ext`, `mk_fst_snd`: the pair `(a, f)`, its components, and
  extensionality.
- Component lemmas (all `simp`): `fst_add`, `snd_add`, `fst_neg`, `snd_neg`, `fst_sub`,
  `snd_sub`, `fst_zero`, `snd_zero`, `fst_one` (`1`), `snd_one` (`0`), `fst_mul`
  (`fst x * fst y`), and `snd_mul` (`fst x • snd y + fst y • snd x`).
- `inl : A →+* Thick A F`, `a ↦ (a, 0)`, and `fstHom : Thick A F →+* A`, `(a, f) ↦ a`.
- `instAlgebra`: for every commutative ring `S` with `Algebra S A`, `Thick A F` is an
  `S`-algebra with `algebraMap S (Thick A F) = inl ∘ algebraMap S A`
  (`algebraMap_apply`). So `s • (a, f) = (algebraMap S A s * a, algebraMap S A s • f)`
  (`fst_smul`, `snd_smul`). `instIsScalarTower`: `IsScalarTower S T (Thick A F)` whenever
  `IsScalarTower S T A`.
- `inr : F →ₗ[A] Thick A F`, `f ↦ (0, f)`. Then `inr_mul_inr` (`inr f * inr f' = 0`),
  `inl_mul_inr` (`inl a * inr f = inr (a • f)`), and `eq_inl_add_inr`. The kernel of
  `fstHom` is the image of `inr` (`mem_ker_fstHom_iff`).
- `fstAlgHom S : Thick A F →ₐ[S] A`, the projection as an `S`-algebra map. Also
  `fst_surjective`, `inr_injective`, and `isNilpotent_of_fst_eq_zero` (an element with
  first component `0` squares to `0`).
- `lift ρ D hD hDD : Thick A F →+* B`, `(a, f) ↦ ρ a + D f`, for a ring map `ρ : A →+* B`
  and an additive map `D : F →+ B` with `D (a • f) = ρ a * D f` and `D f * D f' = 0`
  (`lift_apply`).
- `ofDerivation D : P →ₐ[R] Thick P F`, `p ↦ (p, D p)`, for an `R`-algebra `P`, a
  `P`-module `F` with an `R`-module structure, and `D : Derivation R P F`. Being a ring map
  is the Leibniz rule. The `R`-linearity is `D (algebraMap R P r) = 0`.
- `map π hπ : Thick A F →+* Thick A' F`, `(a, f) ↦ (π a, f)`, for a ring map
  `π : A →+* A'` when `A` acts on `F` through `π` (`hπ : a • f = π a • f`). It is
  `lift (inl ∘ π) inr` (`fst_map`, `snd_map`).

## Provenance

Internal commutative algebra: a commutative wrapper of Mathlib's `TrivSqZeroExt`. In the
openness-of-versality proof, `Thick P F` is the universal first-order thickening along a
derivation `D : P → F`. No literature statement is formalized.
