# Norm laws for tensoring with a finite field extension

`Langlands.Algebra.TensorFiniteExtensionNormStatement.{u}` is a
universe-polymorphic `Prop`-valued definition. It is a statement target: this
module only states the proposition. It supplies no proof, adds no axiom and
defines no new norm.

Worker 208 specified the target in the task. Worker 248 wrote the Lean
statement and this companion.

## Exact statement

The module imports only Mathlib:
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `Mathlib.RingTheory.Norm.Defs`,
`Mathlib.RingTheory.Spectrum.Prime.RingHom`,
`Mathlib.RingTheory.TensorProduct.Free` and
`Mathlib.RingTheory.TensorProduct.Maps`. It opens the scoped `TensorProduct`
notation, so `A ⊗[K] L` is Mathlib's tensor product of `K`-modules.

The proposition quantifies, in this order, over

- fields `K L : Type u` with `[Algebra K L]` and `[FiniteDimensional K L]`;
- a commutative ring `A : Type u` with `[Algebra K A]`.

For these data it asserts the conjunction of the following three clauses.

1. **Base change.** For every commutative ring `B : Type u` with
   `[Algebra K B]`, every `K`-algebra map `φ : A →ₐ[K] B` and every
   `f : A ⊗[K] L`,

   ```text
   φ (Algebra.norm A f) =
     Algebra.norm B (Algebra.TensorProduct.map φ (AlgHom.id K L) f)
   ```

2. **Degree.** For every `a : A`,

   ```text
   Algebra.norm A (algebraMap A (A ⊗[K] L) a) = a ^ Module.finrank K L
   ```

3. **Fibre support.** For every `f : A ⊗[K] L` and every
   `p : PrimeSpectrum A`,

   ```text
   Algebra.norm A f ∉ p.asIdeal ↔
     ∀ q : PrimeSpectrum (A ⊗[K] L),
       PrimeSpectrum.comap (algebraMap A (A ⊗[K] L)) q = p → f ∉ q.asIdeal
   ```

The objects in these clauses are existing Mathlib constructions, resolved by
ordinary instance search:

- `A ⊗[K] L` is a commutative ring (`Algebra.TensorProduct.instCommRing`).
  Its `A`-algebra structure is `Algebra.TensorProduct.leftAlgebra`, so
  `algebraMap A (A ⊗[K] L) a = a ⊗ₜ 1` and `A` acts on the left factor.
  The same holds for `B ⊗[K] L`.
- `Algebra.norm A : A ⊗[K] L →* A` is Mathlib's norm
  (`Mathlib/RingTheory/Norm/Defs.lean`): `Algebra.norm A f` is the
  determinant `LinearMap.det (Algebra.lmul A (A ⊗[K] L) f)` of the
  `A`-linear map "multiply by `f`". Mathlib's `LinearMap.det` is `1` for a
  module without a finite basis. Here `A ⊗[K] L` is free of finite rank over
  `A` (instance `Algebra.TensorProduct.instFree`), with basis
  `Algebra.TensorProduct.basis A b`, the elements `1 ⊗ₜ b i` for any
  `K`-basis `b` of `L`. So the norm is the determinant of the matrix of
  multiplication by `f` in such a basis (`Algebra.norm_eq_matrix_det`), as in
  the source.
- `Algebra.TensorProduct.map φ (AlgHom.id K L) : A ⊗[K] L →ₐ[K] B ⊗[K] L` is
  `φ ⊗ id_L`. On pure tensors it sends `x ⊗ₜ l` to `φ x ⊗ₜ l`
  (`Algebra.TensorProduct.map_tmul`).
- `Module.finrank K L` is the dimension `d = [L : K]` of `L` over `K`. It is
  at least `1`.
- `PrimeSpectrum.comap (algebraMap A (A ⊗[K] L))` is the unbundled function
  from `PrimeSpectrum (A ⊗[K] L)` to `PrimeSpectrum A` with
  `(PrimeSpectrum.comap _ q).asIdeal = Ideal.comap (algebraMap A (A ⊗[K] L)) q.asIdeal`.
  So the condition `PrimeSpectrum.comap _ q = p` says that the prime `q` lies
  over `p`. The primes `q` with this property are the points of the fibre of
  `Spec (A ⊗[K] L) → Spec A` over `p`.

In geometric terms: clause 2 says that the norm of a function pulled back
from `Spec A` is its `d`-th power. Clause 3 says that `Algebra.norm A f` is
nonzero in the residue field at `p` exactly when `f` is nonzero in the
residue field at every point of the fibre over `p`.

## Scope

All universes `u` and all fields `K` of any characteristic are included. The
extension `L / K` is any finite extension: separable, inseparable, or trivial
(`L = K`, `d = 1`). The ring `A` is an arbitrary commutative `K`-algebra. It
need not be a domain, reduced, noetherian or nonzero, and the same holds for
`B` in clause 1. There is no separability, reducedness, domain, noetherianity,
local or nonzero hypothesis, and no chosen basis.

If `A` is the zero ring, clause 2 holds because all elements of `A` are
equal. Clause 1 holds because every `B` receiving a ring map from the zero
ring is also the zero ring. Clause 3 is vacuous because `PrimeSpectrum A` is
empty. The
exponent in clause 2 is `Module.finrank K L`, not `Module.finrank A (A ⊗[K] L)`.
These differ in general: over the zero ring Mathlib's
`Module.finrank_subsingleton` gives `Module.finrank A (A ⊗[K] L) = 1`.

`K`, `L`, `A` and `B` share the single universe `u`, as the task requires.
This is the setting of the consumer statement
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement`,
where the rings of sections lie in the scheme universe `u`.

## Source correspondence and derived provenance

The source is Stacks Project Section 31.18 "Norms" (tag 0BCX), in particular
Lemma 31.18.6 (tag 0BD2). This proposition is a derived algebraic helper,
not a statement in the source. The source's norm is a geometric map of
sheaves. The three clauses here are internal algebraic consequences of the
determinant construction for one affine morphism. The comparison is as
follows.

**The source's norm.** At the start of Section 31.18, for a finite morphism
`π : X → Y` and an integer `d ≥ 1`, a norm of degree `d` for `π` is a
multiplicative map of sheaves `Norm_π : π_* 𝒪_X → 𝒪_Y` such that

- (1) the composition `𝒪_Y → π_* 𝒪_X → 𝒪_Y` of `π^♯` and `Norm_π` equals
  `g ↦ g^d`, and
- (2) for `V ⊂ Y` open, if `f ∈ 𝒪_X(π⁻¹ V)` is zero at `x ∈ π⁻¹(V)`, then
  `Norm_π(f)` is zero at `π(x)`.

The remark after the definition observes that a multiplicative map sends
units to units. So if `f` is defined and nonvanishing at every `x` with
`π(x) = y`, then `Norm_π(f)` does not vanish at `y`. This needs no condition
(2).

Lemma 31.18.6 says that a finite locally free morphism `π : X → Y` of degree
`d ≥ 1` has a canonical norm of degree `d` whose formation commutes with
arbitrary base change. Its proof works on an affine open `V ⊂ Y` over which
`π_* 𝒪_X` is free of rank `d`. A basis gives a `d × d` matrix `M_f` for
multiplication by `f`, and `Norm_π(f) = det(M_f)`. The determinant does not
depend on the basis, so these local norms glue. Base change compatibility is
called "straightforward from the construction". Property (1) is the
determinant of the scalar matrix with entries `g`. For property (2) the proof
base changes to the spectrum of a field `k`. Then `X = Spec(A)` with
`dim_k A = d`; if `f` vanishes at a point, multiplication by `f` is not
surjective, so its determinant is `0`.

**The algebraic case used here.** Take `Y = Spec A` and
`X = Spec(A ⊗[K] L)`. This is the base change of `Spec L → Spec K` along
`Spec A → Spec K`. Then `π_* 𝒪_X` is free of rank `d = Module.finrank K L`
over all of `Y`, and the global section of the source's determinant norm at
`f ∈ A ⊗[K] L` is the determinant of multiplication by `f` in the basis
`1 ⊗ b i`. That determinant is Mathlib's `Algebra.norm A f`. On this
identification:

- Clause 1 is the affine algebraic form of "formation commutes with
  arbitrary base change", restricted to base change along a `K`-algebra map
  `φ : A → B`. Here `B ⊗[A] (A ⊗[K] L)` is identified with `B ⊗[K] L`, and
  `Algebra.TensorProduct.map φ (AlgHom.id K L)` is the induced map. The
  source gives no details for this step.
- Clause 2 is condition (1) on global sections.
- Clause 3 is a two-sided reformulation of nonvanishing at a point of
  `Spec A`. Its direction "`→`", read contrapositively, is condition (2)
  for global sections: if `f` lies in a prime `q` over `p`, then the norm
  lies in `p`. Its direction "`←`" is the pointwise algebraic form of the
  remark that a function nonvanishing on the whole fibre has nonvanishing
  norm. The source derives that remark from multiplicativity, using a
  neighbourhood of the fibre on which `f` is a unit. Clause 3 instead
  states it for a single prime, so its future proof must argue
  algebraically, for example by base change to the residue field at `p`.

The Library statement
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement` uses
the same two-sided nonvanishing formulation for the projection
`X_L → X` of a `K`-scheme `X`. This module does not import or prove it, and
the Library already proves it independently, in
`Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof`. The
present proposition is the self-contained affine algebraic form. It is
stated for the ring `A ⊗[K] L` rather than for rings of sections, and it
asserts the three laws for Mathlib's actual `Algebra.norm A`, not merely the
existence of some norm.

**What is derived.** The source does not state these clauses as a lemma
about `A ⊗[K] L`. The conjunction, the use of Mathlib's `Algebra.norm`,
the formulation of base change along `K`-algebra maps through
`Algebra.TensorProduct.map`, and the prime-by-prime form of clause 3 are
internal choices. They make the affine case of the source's determinant
norm along `X_L → X` available as one algebraic unit.

## Original source and reading record

Registered source `stacks-norms-field-ample-descent-2026-10-26`, directory
SHA-256 `af3256169e1d1a032cecd20fa228482bad8e1b478ccfc55a4a73c7ec187d9f5a`.
It is The Stacks Project Authors, The Stacks Project, HTML snapshot retrieved
2026-10-26. Read passages:

- `0BCX.html` (SHA-256
  `b48f40b4a036e6ab2fb22b9c1da840099d78553cbf1f6cf30627613cd83119b6`),
  Section 31.18: the definition of a norm of degree `d`, conditions (1) and
  (2), the remark following it, and Lemma 31.18.6 (tag 0BD2) with its proof.
  The current page comments only fix the phrase "`V ⊂ Y` open" in the
  definition. They do not affect the passages used here.
- `0BDB.html` (SHA-256
  `cd855d8884fd0c2c9561d270089ca7e3d8b3cd9923cc18adfa3b48980640a31c`),
  Lemma 33.15.1. Its proof uses that `X_{k'} → X` is finite locally free for
  a finite extension `k'/k`, and applies Proposition 31.18.9. This is the
  context in which the norm along a finite field extension is needed.

No errata for these passages were found.

## Obligations for a future proof

This module proves nothing. A separate proof module must prove exactly
`Langlands.Algebra.TensorFiniteExtensionNormStatement`, import this module,
and leave this Lean and Markdown pair unchanged. It must establish all three
clauses, including both directions of clause 3, for arbitrary `K`, `L`, `A`
and `B`:

- **Clause 1.** Show that `φ` applied to the determinant of the
  multiplication matrix of `f` in the basis `1 ⊗ b i` over `A` equals the
  determinant of the multiplication matrix of the image of `f` in the basis
  `1 ⊗ b i` over `B`. Matrix entries map by `φ`, and the determinant commutes
  with ring homomorphisms. Possible Mathlib and Library tools are
  `Algebra.norm_eq_matrix_det`, `Algebra.TensorProduct.basis`,
  `RingHom.map_det`, `LinearMap.det_baseChange`, and the published
  `Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm.norm_map_of_basis`.
- **Clause 2.** Use a finite `K`-basis of `L`, for example
  `Algebra.norm_algebraMap_of_basis` with
  `Algebra.TensorProduct.basis A (Module.finBasis K L)`, whose index type
  has cardinality `Module.finrank K L`. A private compile check confirmed
  that this rewrite closes clause 2. It is not part of this module.
- **Clause 3, direction "`→`".** If `f ∈ q` with `q` over `p`, show
  `Algebra.norm A f ∈ p`. For example, Cayley–Hamilton for multiplication by
  `f` shows that `f` divides `algebraMap A _ (Algebra.norm A f)`, so this
  element lies in `q` and the norm lies in `Ideal.comap _ q = p`. A
  published Library lemma in this form is
  `Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm.norm_mem_comap`.
- **Clause 3, direction "`←`".** If `Algebra.norm A f ∈ p`, produce a prime
  `q` over `p` with `f ∈ q`. One route base changes to the residue field
  `κ(p)` with clause 1. The norm of the image of `f` in `κ(p) ⊗[K] L` is
  `0`, so multiplication by that image is not bijective and the image is not
  a unit. It therefore lies in a maximal ideal, whose contraction is a prime
  of `A ⊗[K] L` over `p` containing `f`. Another route localizes at `p` and
  uses integrality and going-up. A published Library lemma in this form is
  `Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNorm.exists_prime_over_of_norm_mem`.

The Library lemmas named above are hints, not dependencies of this module.
Their exact hypotheses must be checked when the proof is written.
