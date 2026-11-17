# Lifting relative homomorphisms and prescribed conjugators

Let `H` and `G` be arbitrary group schemes over a scheme `S`. For a test scheme `T → S`, `conjugateRelative i g` composes an actual relative homomorphism `i : H_T → G_T` with the inner automorphism defined by the actual pulled-back point `g : T → G`. It extends conjugation from constant homomorphisms to arbitrary relative families. `evaluate_conjugateRelative` proves compatibility with every test-scheme restriction, and `conjugateRelative_one` proves that the identity point acts trivially.

`HasConjugatorLifting H G` is a morphism property on `Over S`. For `a : T′ → T`, it requires both:

- Every actual homomorphism `H_T′ → G_T′` lifts to one over `T`.
- Given two homomorphisms `i, j` over `T` and a specified point `g₀` over `T′` conjugating the restriction of `i` to the restriction of `j`, there is a point `g` over `T` restricting exactly to `g₀` and conjugating `i` to `j`.

The second condition prescribes the reducing conjugator, which makes the property closed under composition without an extra point-lifting assumption in the composition proof. The module proves composition closure, the property for all isomorphisms, and the corresponding `IsMultiplicative` and `RespectsIso` instances. No smoothness, affineness, multiplicative-type or nilpotence hypotheses enter these formal constructions. Such hypotheses are needed to establish the property for infinitesimal closed immersions; no such result is asserted here.

The restriction proof tests equality on all scheme-valued points and uses the Library's family-point equivalence to compare direct and iterated pullbacks. Its compatibility with multiplication, inverses and constant points identifies the two conjugations. Composition lifts a relative homomorphism in two steps; for conjugators it first lifts the specified point and conjugacy to the intermediate test scheme, then lifts both to the original one. For an isomorphism of tests, evaluation along its inverse provides the lifts and restriction naturality gives the conjugacy equation.

This module is an internal construction derived from the Library's `HomScheme.Universal`, `HomScheme.ConjugationMap`, actual inner automorphisms and family-point pullback comparisons. It transcribes no new literature theorem and changes no published statement. The companion auxiliary module `Langlands.CommutativeAlgebra.NilpotentQuotientProperty` supplies a generic nilpotent-quotient induction, independently of group schemes.
