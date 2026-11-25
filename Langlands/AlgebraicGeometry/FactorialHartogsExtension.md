# Hartogs extension across a point with factorial stalk

Module `Langlands.AlgebraicGeometry.FactorialHartogsExtension`, namespace
`Langlands.AlgebraicGeometry.FactorialHartogsExtension`. This is an internal supporting module
for the proof of `Langlands.GroupScheme.RankOneCentralCoverStatement` (`rankOneCentralCover` in
`Langlands.GroupScheme.Reductive.RankOneCentralCoverProof`). It is the section-extension form of the codimension statement
`FactorialAffineComplement.false_of_generization_chain`, and it uses the same algebraic input,
`FactorialLocalHartogs.exists_eq_of_forall_pow_mul`. This is the classical Hartogs property of
normal (here factorial) local rings of dimension at least two. The module proves it directly,
with no new literature source.

## Statements

- `exists_prime_of_generization_chain`: for points `y₀ ⤳ y₁ ⤳ z` of a scheme with
  `y₀ ≠ y₁` and `y₁ ≠ z`, the stalk at `z` has a prime ideal that is neither `⊥` nor the
  maximal ideal. The proof is the one in `false_of_generization_chain`: the point `y₁`
  corresponds to a prime of the stalk through `Scheme.fromSpecStalk`.
- `genericPoint_mem`: in an integral scheme the generic point lies in every nonempty open.
- `forall_pow_mul` (Hartogs condition). Let `X` be integral, `W` an open whose complement is
  the single point `z`, and `s ∈ Γ(X, W)`. For every nonzero `f` in the maximal ideal of the
  stalk at `z`, some power `fᵏ` times the image of `s` in the function field is the image of
  an element of the stalk.
- `restrict_surjective_of_generization_chain` (main theorem):

  ```
  theorem restrict_surjective_of_generization_chain {X : Scheme.{u}} [IsIntegral X]
      {W : X.Opens} {z y₀ y₁ : X}
      (hW : ∀ y : X, y ∉ W ↔ y = z) (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z) (hne₀₁ : y₀ ≠ y₁)
      (hne₁z : y₁ ≠ z) [UniqueFactorizationMonoid (X.presheaf.stalk z)] :
      Function.Surjective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op)
  ```

  So every section of the structure sheaf on `X ∖ {z}` is the restriction of a global
  section. Only integrality of `X` and factoriality of the stalk at `z` are assumed. No
  separatedness or Noetherian hypothesis is needed.

## The implemented proof

1. *Hartogs condition* (`forall_pow_mul`). Represent `f` by a section `g` on an affine open
   neighbourhood `A` of `z`. The basic open `D(g)` misses `z`, because `f` is not a unit, so
   `D(g) ⊆ W`. Since `f ≠ 0`, the generic point lies in `D(g)`. As `A` is affine,
   `Γ(X, D(g))` is the localization of `Γ(X, A)` at `g`
   (`IsAffineOpen.isLocalization_basicOpen`). Hence `s|_{D(g)} · gᵏ = a'|_{D(g)}` for some
   `a' ∈ Γ(X, A)`. Taking images in the function field gives `fᵏ · s = a` with `a` the germ
   of `a'` at `z`.
2. *Extension at `z`.* The point `y₁ ≠ z` lies in `W`, so `W` is nonempty. By
   `exists_prime_of_generization_chain` and `exists_eq_of_forall_pow_mul`, with the function
   field as the fraction field of the stalk at `z`, the image of `s` in the function field is
   the image of a germ `a` at `z`. Represent `a` by a section `t` on an open neighbourhood `V`
   of `z`.
3. *Agreement.* On any open `O` containing the generic point, the restrictions of `s` and `t`
   have the same image in the function field. That map is injective because `X` is integral
   (`Scheme.germToFunctionField_injective`). So `s` and `t` agree on `W ⊓ V`.
4. *Gluing.* `W` and `V` cover `X`, since `V` contains `z`. The sheaf gluing lemma
   `TopCat.Sheaf.existsUnique_gluing'`, applied to the family indexed by `Bool`, gives a
   global section restricting to `s` on `W`.
