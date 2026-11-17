# Statement: finite étale covers of affine space in characteristic zero have trivial Picard group

`Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. The module does not prove it, and it adds no
other definitions, theorems or axioms. It imports only Mathlib:

- `Mathlib.RingTheory.Etale.Basic`, for `Algebra.Etale`;
- `Mathlib.RingTheory.PicardGroup`, for `CommRing.Pic`;
- `Mathlib.RingTheory.MvPolynomial.Basic`, for `MvPolynomial`.

## Statement

For every field `k : Type u` with `[CharZero k]`, every `n : ℕ` and every commutative ring
`A : Type u` with `[Algebra (MvPolynomial (Fin n) k) A]` such that

- `Algebra.Etale (MvPolynomial (Fin n) k) A`, and
- `Module.Finite (MvPolynomial (Fin n) k) A`,

we have `Subsingleton (CommRing.Pic A)`.

The notions used are Mathlib's:

- `MvPolynomial (Fin n) k` is the polynomial ring `k[x₁, …, xₙ]`, the coordinate ring of
  affine `n`-space `𝔸ⁿ_k`.
- `Algebra.Etale R A` says that `A` is a formally étale `R`-algebra of finite presentation,
  so `Spec A → Spec R` is étale. Together with `Module.Finite R A`, the morphism
  `Spec A → 𝔸ⁿ_k` is finite étale. Every finite étale cover of the affine scheme `𝔸ⁿ_k` is
  of this form.
- `CommRing.Pic A` is the Picard group of `A`: isomorphism classes of invertible `A`-modules
  under tensor product. `Subsingleton (CommRing.Pic A)` says that every invertible
  `A`-module is free (Mathlib's `CommRing.Pic.subsingleton_iff`), that is, `Pic(Spec A) = 1`.

In words: every finite étale cover of `𝔸ⁿ_k`, for a field `k` of characteristic zero, has
trivial Picard group.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).

- Remark 7.2.13, p.259: "The only role of semi-locality for the affine S in the proof of
  Proposition 7.2.12 is to ensure that every finite étale cover of S has trivial Picard
  group. Thus, the conclusion also holds (with the same proof) for S = Spec Z and
  S = A^n_k for a field k of characteristic 0."

## Derivation from the source

The provenance is derived. Conrad does not state this proposition as a separate result. The
remark says that the proof of Proposition 7.2.12 needs only that every finite étale cover of
`S` has trivial Picard group, and then applies the proof to `S = 𝔸ⁿ_k` with
`char k = 0`. That application uses exactly this statement for `S = 𝔸ⁿ_k`, which the remark
leaves to the reader.

The standard argument, which is not formalized here, runs as follows. In characteristic zero,
`𝔸ⁿ` over an algebraic closure `k̄` of `k` has no nontrivial connected finite étale covers.
Therefore every connected finite étale cover of `𝔸ⁿ_k` is `𝔸ⁿ_{k'}` for a finite field
extension `k'` of `k`. A finite étale `k[x₁, …, xₙ]`-algebra `A` is then a finite product of
polynomial rings `k_i[x₁, …, xₙ]` over finite extension fields `k_i`. Each factor is a
unique factorization domain, so its Picard group is trivial. The Picard group of a finite
product is the product of the Picard groups of the factors.

The Lean statement encodes this as follows:

- "finite étale cover of `S`" becomes a finite étale `k[x₁, …, xₙ]`-algebra `A`. The
  statement quantifies over all such algebras, not only faithful or connected ones. `A` may
  be the zero ring, whose Picard group is trivial.
- `A` lies in the universe `u` of `k`. This loses nothing: a module-finite algebra over a
  ring in `Type u` is isomorphic to one in `Type u`.
- `n = 0` is allowed. Then the statement is about finite étale `k`-algebras, which are
  products of fields.

This is the input that the case `S = 𝔸ⁿ_k` of the published
`Langlands.GroupScheme.ReductivePicardTrivialQuasiSplitInnerFormStatement` needs from its
clause 1: with `R = MvPolynomial (Fin n) k`, the statement says exactly that every finite
étale `R`-algebra in universe `u` has subsingleton Picard group.

## Scope and not stated

The characteristic-zero hypothesis comes from the source. In positive characteristic `p`,
`𝔸¹` has nontrivial connected finite étale covers (Artin–Schreier covers), so the argument
above does not apply. The statement asserts nothing in positive characteristic. It does not
state the simple connectivity of `𝔸ⁿ_{k̄}`, the description of finite étale covers of
`𝔸ⁿ_k`, or the behaviour of Picard groups under finite products. Those are steps of a
proof, not part of the statement.
