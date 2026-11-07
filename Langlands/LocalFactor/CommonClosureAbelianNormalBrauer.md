# Brauer induction relative to an abelian normal subgroup, on actual Weil groups

Lean module: `Langlands.LocalFactor.CommonClosureAbelianNormalBrauer`.

## Source

P. Deligne and G. Henniart, *Sur la variation, par torsion, des constantes locales
d'équations fonctionnelles de fonctions L*, Invent. Math. 64 (1981):

- Variante 2.3, printed p. 102 (PDF p. 14). `G` is an extension of `ℤ` by a finite group
  `G(0)`, `A ⊆ G(0)` is an abelian normal subgroup, and `V` is a representation. Then
  `V = Σ nᵢ Ind_{Hᵢ}^G (χᵢ)` with `Hᵢ` of finite index containing `A`. If `V^A = 0`, the
  characters `χᵢ` can be chosen nontrivial on `A`. The proof reduces to `V` irreducible.
  It writes `V` as a representation factoring through a finite quotient, tensored with a
  character trivial on `G(0)`, and applies 2.2.
- The proof of Theorem 4.2 in 4.5 (printed p. 110, PDF p. 22) uses 2.3 as follows. It
  takes `V` irreducible and `A` the last nonzero ramification group of the quotient of `W`
  by the part of inertia acting trivially; this group is abelian, normal, and acts without
  nonzero fixed vectors. Section 4.8 (printed p. 111, PDF p. 23) uses it the same way.

This module states and proves that use of 2.3 on the actual Weil subgroup
`W_E = weilSubgroup F E` of a finite intermediate field `E` of the common closure. It is
the form needed in 4.5 and 4.8.

## Definitions

- `abelianNormalInductionGenerators F E N : Set (Virtual F E)` is the set of classes
  `induce F E L h (ExactGrothendieckGroup.characterClass η)`. Here `L` is a finite
  intermediate field with `E ≤ L`, every element of `N` lies in `W_L`, and `η : W_L →ₜ* ℂˣ`
  is a continuous character with `η n ≠ 1` for some `n ∈ N`. These are the actual
  common-closure inductions `Ind_{W_L}^{W_E} η`.
- `WeilAbelianNormalBrauerStatement F : Prop` makes the following claim for every `E` and
  every normal subgroup `N` of `W_E` contained in its inertia subgroup
  (`CommonClosureWeilDeligne.inertia F E`). Let `A` be a continuous irreducible finite
  representation of `W_E` such that the operators `A(n)`, `n ∈ N`, commute pairwise and
  have no common nonzero fixed vector. Then the class of `A` in `Virtual F E` lies in the
  integral span of `abelianNormalInductionGenerators F E N`.

  Two hypotheses differ from DH81's formulation. "`A` abelian" becomes "the operators
  `A(n)` commute"; this is the abelianness of the image group used in 4.5 and 4.8.
  `A ⊆ G(0)` becomes `N ≤ inertia`.

## Main theorem

`Langlands.LocalFactor.CommonClosure.weilAbelianNormalBrauer F :
WeilAbelianNormalBrauerStatement F`.

## Proof (as implemented)

1. **Unramified twist** (`irreducible_finiteImage_unramifiedTwist`). This repeats the
   proof of the Library's `irreducible_finiteImage_twist`, recording one extra fact: the
   twisting character `χ`, the unramified character `localUnramifiedCharacter E z`
   transported to `W_E`, is trivial on inertia (`unramifiedCharacter_on_kernel`,
   `standaloneWeilEquiv_symm_mem_inertia`). So `A ≅ χ ⊗ B` with `B` continuous of finite
   image. Since `χ` is trivial on `N`, `B` agrees with `A` on `N` through the equivalence.
   Hence the operators `B(n)` commute and have no common nonzero fixed vector.
2. **Finite quotient** (`finiteImage_mem_abelianNormalSpan`). The kernel of `B` is open:
   it is closed (`isClosed_ker_of_isContinuous`) and `B` has finite range
   (`Weil.open_kernel_of_finite_range_of_closed`). The quotient
   `Q = W_E ⧸ ker B` is finite, since it injects into the range of `B`. Then `B` descends
   to `Q` through `QuotientGroup.lift`, and its coordinate model
   (`FiniteRep.ofRepresentation`) is an `FDRep ℂ Q`. The image `N.map π` is normal and
   abelian, since equal `B`-values give equal classes. The model has no nonzero
   `N.map π`-fixed vector (`ofRepresentation_fixed_eq_zero`).
3. **Finite theorem.** `FiniteRep.abelianNormalBrauer` (DH81 2.2(ii), proved in
   `Langlands.Representation.Finite.AbelianNormalBrauer`) puts the class of the model in
   the span of `Ind_S^Q χ'` with `N.map π ≤ S` and `χ'` nontrivial on `N.map π`.
4. **Inflation** (`inflate_mem_abelianNormalSpan`, `inflate_abelianNormalGenerator_mem`).
   Inflation along `π` sends the model's class to `[B]` (`inflate_ofClass`,
   `inflateEquiv`).
   - `exists_galois_kernel` gives an open normal `U` of the Galois group whose preimage
     lies in `ker B`.
   - `exists_extension_of_le` identifies `π⁻¹ S` with `W_L` for a finite `L ⊇ E`.
   - `inflate_induce_oneDimensional_apply` (the Library's
     `inflate_induce_oneDimensional` with the character made explicit) sends `Ind_S χ'`
     to `induce F E L h [η]`, where `η(w) = χ'(π w)`.

   The subgroup `W_L` contains `N`, because `π N ≤ S`. The character `η` is nontrivial on
   `N`, because `χ'` is nontrivial on `π N`.
5. **Twist back** (`continuousTwist_mem_abelianNormalSpan`). `[A]` is the continuous twist
   of `[B]` by `χ`. Twisting `induce F E L h [η]` by `χ` gives
   `induce F E L h [χ|_{W_L} · η]`, by `continuousTwist_induce` and
   `continuousTwist_characterClass`. The product character is still nontrivial on `N`,
   because `χ` is trivial on `N`.

## Provenance

The statement is the form of DH81 2.3 used in 4.5 and 4.8 (cited above), on the
Library's actual common-closure Weil subgroups. It has the reductions recorded there:
`V` irreducible, the twist trivial on `G(0)`, and the finite quotient. The helper
statements are internal to this proof:

- the finite-image case and its inflation lemmas;
- the explicit-character version of `inflate_induce_oneDimensional`;
- the unramified-twist refinement of `irreducible_finiteImage_twist`;
- the coordinate-model fixed-vector lemma.

They reuse published Library constructions by Lean name.
