# Tate exponents of the adic avatars of an algebraic Hecke character

`Langlands.GaloisRepresentation.AlgebraicHeckeAvatarTateExponentStatement`
computes the labelled rank-one Tate exponent of the adic avatars of an algebraic
Hecke character. In the even-degree Harris route it supplies the exponent shift
of the scalar correction.

Let `K` be a CM field. Let `χ` be a Hecke character of `K` whose archimedean
component is `InfinityType.toCharacter a`, that is,
`χ_∞(x) = ∏_σ σ(x)^{a(σ)}` over the complex embeddings `σ` of `K`. Let `L` be a
number field with `ι : L → ℂ`, and let `β` and `ψ` satisfy
`IsUniformHeckeAvatar ι χ S β ψ`. That is, at every finite place `v ∉ S`,
`ι(β_v)` is `χ_v` of a uniformizer, and every geometric Frobenius lift at `v`
acts through `ψ_λ` by `β_v` (for `λ` of different residue characteristic). Then
for every finite place `λ` of `L` and every embedding `j : K → L`,

`HasCharacterTateExponentAt λ (λ ∘ j) ψ_λ (a(ι ∘ j))`.

Here `λ ∘ j` is `NumberField.FinitePlace.embedding λ` composed with `j`. The
local pullback of `ψ_λ` along this label therefore has a nonzero period `x`
with `ψ_λ(g) g(x) = cyclotomic(g)^{a(ι ∘ j)} x`.

## Conventions and a check

The exponent convention is that of `HasLocalCharacterTateExponent`: the
cyclotomic character has exponent `1`. The Library's avatars use the
**geometric** Frobenius convention. As a check, take the adelic norm
`‖·‖`. Its infinity type is `a ≡ 1`, since `‖z‖_∞ = ∏_v z_v z̄_v`, and its
finite values at uniformizers are `q_v^{-1}`. Its avatar sends geometric
Frobenius to `q_v^{-1}`, so it is the cyclotomic character, of exponent `1`
at every label.

General case. The hypotheses give one embedding `j` for the queried label.
They do not ask `ι(L)` to contain every conjugate image of `K`, so the
derivation passes through an auxiliary field and then descends.

1. Choose a finite Galois extension `L'` of `L` that contains the values of
   `χ_f` and the images of all complex embeddings of `K`. Choose an extension
   `ι' : L' → ℂ` of `ι`, and a place `λ'` of `L'` above `λ` whose embedding
   into `Q̄_p` extends the given embedding of `L_λ`. Then `L'_{λ'}/L_λ` is
   Galois, with finite group `H`.
2. Over `L'`, Serre's construction gives the avatar
   `ψ'_{λ'} = (ι'_{λ'} ι'^{-1})(χ · ∏_σ σ(x_∞)^{-a(σ)}) · ∏_σ (ι'_{λ'} ι'^{-1} σ)(x_p)^{a(σ)}`
   on ideles, read through the geometric reciprocity map. Its good Frobenius
   values are those of `ψ_λ`. By Chebotarev density, `ψ'_{λ'}` is the scalar
   extension of the supplied `ψ_λ` to `L'_{λ'}`.
3. Let `v` be the place of `K` induced by the extended label `λ' ∘ j`, and
   write `τ_σ = ι'_{λ'} ι'^{-1} σ`. Pull the idelic formula back along the
   extended label to the local Weil group of `L'_{λ'}`, read through
   geometric reciprocity and the norm from `L'_{λ'}` to `K_v`, and restrict
   it to inertia, that is, to the local units `u` of `K_v`. There it has two
   factors. The first is the algebraic correction `u ↦ ∏ τ_σ(u)^{a(σ)}` over
   those `σ` for which `τ_σ` induces `v`; on units it is the product of the
   Lubin–Tate characters `u ↦ τ_σ(u)^{a(σ)}`, because the norm description
   of Appendix A4 is a statement about the projection to the local unit
   group. The second is the finite part of the type `A₀` character. It is
   locally constant, so it is trivial on an open subgroup of inertia. The
   factorization does not extend to the whole Weil group: at a uniformizer
   the algebraic correction is not the value of the Lubin–Tate characters,
   and the quotient of the avatar by the Lubin–Tate monomial is an
   unramified unit-valued character, possibly of infinite order. So the
   avatar and the Lubin–Tate monomial agree on an open subgroup of
   inertia. That is exactly the relation `≡` of Serre's Appendix A5, and
   nothing more is used. With the norm description of Appendix A4, Theorem 2
   and Lemma 2 of A5 give the labelled Hodge–Tate decomposition. The
   norm-compatible Lubin–Tate character has exponent `1` at the inclusion
   label and `0` at the other embeddings. Only `σ = ι ∘ j` has `τ_σ` equal to
   the extended label `λ' ∘ j`, so the exponent there is `a(ι ∘ j)`. The
   unramified part does not change the exponent, because the comparison is
   made only on inertia.
4. Step 3 gives a nonzero period `x` in the completed algebraic closure `C`
   with `ψ_λ(g) g(x) = cyclotomic(g)^{a(ι ∘ j)} x` for all `g` in the
   absolute Galois group of `L'_{λ'}`. The ratio of two such periods is
   fixed by that group, so by Tate's theorem (the fixed field of `C` is
   `L'_{λ'}`) the periods and `0` form a one-dimensional `L'_{λ'}`-line `P`
   in `C`. The absolute Galois group of `L_λ` acts on `C` by
   `h · x = ψ_λ(h) cyclotomic(h)^{-a(ι ∘ j)} h(x)`; this is an action
   because the values of both characters lie in `L_λ` or `ℤ_p` and are
   fixed. The absolute Galois group of `L'_{λ'}` is normal and characters
   are invariant under conjugation, so this action preserves `P`. On `P`
   the subgroup fixing `L'_{λ'}` acts trivially, by the period equation, so
   `H` acts semilinearly on `P`. Hilbert 90 for
   this finite Galois group gives a nonzero `H`-fixed vector. It lies in `C`
   and is a period over `L_λ` for the original character and the original
   label `λ ∘ j`. Equivalently, Serre's open-inertia criterion (Appendix A2,
   Proposition 1, using A1 Theorem 1) gives the same conclusion: the
   absolute Galois group of `L'_{λ'}` meets the inertia group of `L_λ` in an
   open subgroup.

## Provenance and boundary

This is derived from Serre, *Abelian l-Adic Representations and Elliptic
Curves* (1989 reprint):
- Chapter II, §2.3, printed pp. II-10–II-12 (PDF pp. 60–62): the idelic
  construction with the algebraic correction at the coefficient prime;
- §2.5, Proposition (b), pp. II-18–II-19 (PDF pp. 68–69): the Frobenius
  formula, in Serre's arithmetic convention;
- §2.7, p. II-24 (PDF p. 74): the correction at infinity giving type `A₀`;
- Chapter III, §1.2, pp. III-6–III-7 (PDF pp. 98–99): Hodge–Tate type of
  locally algebraic abelian representations;
- Appendix A2, Proposition 1, p. III-35 (PDF p. 127): the open-inertia
  admissibility criterion;
- Appendix A4, the norm remark, p. III-42 (PDF p. 134): the Lubin–Tate
  character on inertia is the inverse of the norm;
- Appendix A5, Theorem 2 and Lemma 2, pp. III-44–III-47 (PDF pp. 136–139):
  the labelled decomposition by embeddings for Lubin–Tate characters, over a
  base containing all conjugates of the local field. The comparison there is
  agreement on an open subgroup of inertia. The containment of conjugates is
  why the auxiliary field `L'` is used.

The exponent is stated in the Library's geometric-Frobenius convention, which
inverts Serre's arithmetic normalization of reciprocity.

Application context. Clozel (1991), §5.3, pp. 143–144, translates purity for
the coefficient-system weight. Harris (1999), proof of 5.7(i), pp. 313–314,
uses the scalar twist in the cohomology decomposition. Neither passage is
used for the labelled calculation itself.

Only the proposition is defined. The labelled geometric grades of the Hecke
multiplicity family are a separate statement. Combining the two exponents uses
`HarrisLabelledInverseTwistStatement`.
