# Brauer induction relative to an abelian normal subgroup, keeping a kernel

Lean module: `Langlands.LocalFactor.DeligneHenniartRefinedBrauer`.

## Source

P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981):

- Variante 2.3, printed p. 102 (PDF p. 14): for `G` an extension of `ℤ` by a finite group
  `G(0)`, `A ⊆ G(0)` abelian normal and `V` a representation with `V^A = 0`, one has
  `V = Σ nᵢ Ind_{Hᵢ}^G (χᵢ)` with `Hᵢ ⊇ A` of finite index and `χᵢ` nontrivial on `A`.
- Proof of Theorem 4.2, 4.5 (printed p. 110, PDF p. 22), and 4.8 (printed p. 111, PDF
  p. 23). There `V` is irreducible and is viewed as a representation of the quotient `G`
  of `W` by the part of inertia acting trivially on `V`, and 2.3 is applied to `G`. The
  characters `χᵢ` are then characters of subgroups of `G`, so as characters of the
  corresponding subgroups of `W` they are trivial on that part of inertia. This is what
  makes the conductor of each `χᵢ` computable in 4.5.

The Library's `WeilAbelianNormalBrauerStatement`
(`Langlands.LocalFactor.CommonClosureAbelianNormalBrauer`) states 2.3 on the actual Weil
subgroup `W_E` but does not record this triviality. This module adds it.

## Definitions

- `kernelInductionGenerators F E N K : Set (Virtual F E)`, for subgroups `N` and `K` of
  `W_E = weilSubgroup F E`. It is the set of classes
  `induce F E L h (ExactGrothendieckGroup.characterClass η)`, where:
  - `L` is a finite intermediate field with `E ≤ L` (`h`) and every element of `N` lies
    in `W_L`;
  - `η : W_L →ₜ* ℂˣ` is a continuous character with `η n ≠ 1` for some `n ∈ N`;
  - `η g = 1` for every `g ∈ W_L` whose image `weilInclusion F E L h g` in `W_E` lies in
    `K`.

  These are the generators of `abelianNormalInductionGenerators F E N` with the added
  condition that `η` is trivial on `K ∩ W_L`.

## Main theorem

`weilAbelianNormalBrauer_kernel F E N K hN hNI hKI A hc hi hcomm hfix hK`. The data are:

- a normal subgroup `N` of `W_E` contained in inertia `CommonClosureWeilDeligne.inertia F E`;
- a subgroup `K` of `W_E` contained in inertia;
- a continuous irreducible finite representation `A` of `W_E` such that the operators
  `A(n)`, `n ∈ N`, commute pairwise and have no common nonzero fixed vector, and
  `A(k) = 1` for every `k ∈ K`.

The conclusion: the class of `A` in `Virtual F E` lies in the integral span of
`kernelInductionGenerators F E N K`.

## Helper theorems

- `continuousTwist_mem_kernelSpan`: twisting by a continuous character of `W_E` that is
  trivial on `N` and on `K` preserves the span.
- `inflate_kernelGenerator_mem`, `inflate_mem_kernelSpan`: for a finite quotient
  `π : W_E → Q` with open kernel containing `K`, inflation along `π` sends the generators
  of the finite abelian normal Brauer span for `π N` into the span. It also sends the
  class of an `FDRep ℂ Q` without nonzero `π N`-fixed vectors, with `π N` abelian, into
  the span.
- `finiteImage_mem_kernelSpan`: the theorem for a continuous finite-image representation
  `B` trivial on `K`.

## Proof (as implemented)

The proof copies the proof of `weilAbelianNormalBrauer` and keeps track of `K` at each
step.

1. **Unramified twist.** `irreducible_finiteImage_unramifiedTwist` gives
   `A ≅ χ ⊗ B`. Here `B` is continuous with finite image and `χ` is a continuous character
   trivial on inertia. On inertia `B` agrees with `A` through the equivalence. So `B` is
   trivial on `K`, and on `N` its operators commute and have no common nonzero fixed
   vector.
2. **Finite quotient.** As in the Library proof, `π : W_E → Q = W_E ⧸ ker B` is a finite
   quotient with open kernel, and `B` descends to `Q`. Since `B` is trivial on `K`, the
   kernel of `π` contains `K`.
3. **Finite theorem.** `FiniteRep.abelianNormalBrauer` (DH81 2.2(ii)) writes the class of
   the descended representation as a combination of `Ind_S^Q χ'` with `π N ≤ S` and `χ'`
   nontrivial on `π N`.
4. **Inflation.** `exists_extension_of_le` identifies `π⁻¹ S` with `W_L`, and
   `inflate_induce_oneDimensional_apply` sends `Ind_S χ'` to `induce F E L h [η]` with
   `η(g) = χ'(π g)`. The extra condition holds: if the image of `g` in `W_E` lies in `K`,
   then `π` of it is `1`, so `η g = χ'(1) = 1`.
5. **Twist back.** `[A]` is the continuous twist of `[B]` by `χ`. Twisting
   `induce F E L h [η]` gives `induce F E L h [χ|_{W_L} · η]` (`continuousTwist_induce`,
   `continuousTwist_characterClass`). The product is still nontrivial on `N` and trivial
   on `K ∩ W_L`, since `χ` is trivial on inertia, which contains `N` and `K`.

## Provenance

The statement is DH81 2.3 on the actual Weil subgroup `W_E`, in the form used in 4.5 and
4.8 (cited above). There 2.3 is applied to the quotient of `W` by the part of inertia that
acts trivially, so the induced characters are trivial on it. Here `K` plays the role of
that part. The helper theorems are internal to this proof. They reuse the Library
constructions of `Langlands.LocalFactor.CommonClosureAbelianNormalBrauer` by Lean name:
`irreducible_finiteImage_unramifiedTwist`, `exists_galois_kernel`,
`exists_extension_of_le`, `inflate_induce_oneDimensional_apply` and
`ofRepresentation_fixed_eq_zero`.
