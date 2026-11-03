# Proof of the Noetherian finiteness inputs for image generation

`noetherianImageGenerationFiniteness` proves
`NoetherianImageGenerationFinitenessStatement.{u}` from
`Langlands.GroupScheme.ImageGenerationNoetherianStatement`, in an arbitrary
universe `u`. The statement is the conjunction of two propositions, and the
proof builds the conjunction from one proof of each.

For `NoetherianPrimeChainStabilizationStatement`, the proof introduces the
Noetherian commutative ring `A`, the sequence `p : ℕ → Ideal A`, its antitonicity
and the primality of every term. It then applies
`exists_forall_eq_of_antitone_isPrime` from
`Langlands.GroupScheme.ImageGenerationNoetherian`. That lemma returns `N` with
`p m = p N` for every `m ≥ N`. Its proof picks `N` minimizing the Krull height
of `p n`.

For `NoetherianAffineClosedEndomorphismStatement`, the proof introduces the
affine, locally Noetherian scheme `X`, the morphism `φ : X ⟶ X` and the
hypothesis `IsClosedImmersion φ`. The target takes this hypothesis as an explicit
argument, but the published helper `isIso_of_isClosedImmersion_endo` takes it as a
typeclass instance. The proof therefore adds the hypothesis to the local context
as an instance before applying the helper. The helper shows that `φ` induces a
surjective, hence bijective, endomorphism of the Noetherian ring of global
sections. It then concludes with Mathlib's affine criterion for closed
immersions.

The target keeps all of its hypotheses: there is no field, finite-dimensionality,
reducedness or irreducibility assumption. The helper lemmas, written by
Worker 1378, are imported from the Library and not reproved here; this module
only fits them to the target's argument form.
