# Degrees of the Mumford homomorphisms of `L ^ n ⊗ f^* L`

`Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. The hypotheses are the ample Mumford presentation of `Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`, without its additivity witness, rational-inverse instance, characteristic-zero assumption and relative dimension. The statement quantifies over:

- the Rosati construction prerequisites `P : Prerequisites.{u}`;
- an algebraically closed field `k : Type u`;
- an abelian scheme `A` over `Spec k` with dual witnesses `W : DualData A`;
- a homomorphism `lam : A ⟶ W.dual P` to the existing actual dual;
- an actual line bundle `L` on `A`, a base line bundle `B` with its evaluation isomorphism `evaluationB`, and a line bundle `M` with the evaluation isomorphism `evaluation` for the normalized family.

It assumes that `L.IsAmple` holds and that `(groupHom lam).hom.hom` equals `mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation P.square W.hasDual`. So `lam` is the actual Mumford homomorphism `φ_L` of `L`.

For every actual endomorphism `f : A ⟶ A`, write `f^∨` for the existing actual dual homomorphism `dualAbelianSchemeMapFromEvaluation … f : W.dual P ⟶ W.dual P` formed with the witnesses of `W` on both sides. Set

`ψ_n = n • lam + f ≫ lam ≫ f^∨ : A ⟶ W.dual P`,

where `n • lam` is the natural-number multiple in the additive group of homomorphisms and `≫` is composition, written in diagrammatic order. The conclusion is that there is `n₀ : ℕ` such that for every `n ≥ n₀`:

1. `ψ_n` is an isogeny (`IsIsogeny`, the Library's finite, flat and surjective predicate);
2. at every point `y` of `(W.dual P).X.left`, the rank `(hom ψ_n).finrank y`, cast to `ℚ`, equals the square of `coherentEulerSequence A.X.hom ((LineBundle.pullback (hom f)).obj L).obj _ L n`.

The last quantity is the actual coherent Euler characteristic of `f^* L ⊗ L ^ n`, where `f^* L` is formed with the actual `LineBundle.pullback` functor along the underlying morphism of `f`.

## Provenance

This is a derived statement. In classical notation it says that for `n ≫ 0` the homomorphism `n φ_L + f^∨ φ_L f` is an isogeny of degree `χ(f^* L ⊗ L^n)^2`. The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers. The intended argument combines the following facts.

- `φ_L(a)` is the class of `t_a^* L ⊗ L^{-1}`, and `φ_L` is a homomorphism (Remark 6.8, p. 10). Directly from this formula, `φ_{L ⊗ N} = φ_L + φ_N`, and `φ_{f^* L} = f^∨ ∘ φ_L ∘ f` because `f ∘ t_a = t_{f(a)} ∘ f`. Hence `ψ_n` is the Mumford homomorphism of `L ^ n ⊗ f^* L`.
- For ample `L`, the line bundle `L ^ n ⊗ f^* L` is ample once `n` is large. For an ample line bundle the Mumford homomorphism is an isogeny (Section 11, p. 17).
- Theorem 13.3(a), p. 25: the degree of `φ_N` is `χ(N)^2`.
- Section 8, p. 12: the degree of an isogeny is the rank of the pushforward of the structure sheaf. Conclusion 2 uses this rank in the form of Mathlib's `finrank`.

The Library already proves the Riemann–Roch degree formula for a finite flat ample Mumford map (`Langlands.AbelianScheme.AlgClosedFieldAmpleMumfordEulerSquareStatement`). The remaining geometric inputs are the identification of `ψ_n` with the Mumford map of `L ^ n ⊗ f^* L`, ampleness of that bundle for large `n`, and the isogeny property.

## Purpose

This statement, together with `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantStatement`, is intended as an input to the proof of `Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`. Comparing the coefficients of `n ^ (2g)` and `n ^ (2g - 1)` in the resulting polynomial identity yields the trace formula. This file does not state or prove that reduction.
