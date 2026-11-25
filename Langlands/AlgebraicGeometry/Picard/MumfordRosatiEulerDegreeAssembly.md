# Degrees of `n • λ + f^∨ λ f` from the Euler-characteristic square formula

Lean module: `Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeAssembly`, namespace
`Langlands.AbelianScheme.MumfordPicardClass`.

This module proves the content of the statement
`Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement` for explicit data, as the theorem
`eulerDegree`. The module `MumfordRosatiEulerDegreeProof` applies it to the statement.

## Provenance

The argument is the one recorded in the statement's provenance. By Milne, *Abelian
Varieties* (1986 article, author revision January 2, 2022; registered source
`milne-abelian-varieties-1986-author-2022`), Remark 6.8, p.10, the formula
`φ_L(a) = t_a^*L ⊗ L⁻¹` makes `n • φ_L + f^∨ ∘ φ_L ∘ f` the Mumford homomorphism of
`f^*L ⊗ L^n`. That bundle is ample for large `n`. Its Mumford homomorphism is an isogeny
(Section 10, p.17), and its degree is `χ(f^*L ⊗ L^n)²` (Theorem 13.3(a), p.25). The Lean
proof assembles published Library results and the helper modules
`MumfordMapPicardClass` and `AmpleMumfordMapIsogeny`.

## Declarations

### `powLineBundle L n` (definition) and `classOf_powLineBundle`

`powLineBundle L n` is the line bundle with carrier `tensorPow L.obj n`, the iterated tensor
power used by `coherentEulerSequence`. Its local freeness is the published
`tensorPow_isLocallyFreeRankOne`. `classOf_powLineBundle` states that its Picard class is
`n • [L]`. Proof: induction on `n`. `tensorPow L.obj 0` is the structure sheaf, of class `0`.
`tensorPow L.obj (n+1) = L ⊗ tensorPow L.obj n`, and `LineBundle.classOf_tensor` applies.

### `eulerDegree`

**Statement.** The hypotheses are those of `MumfordEulerDegreeStatement`: Rosati
prerequisites `P`, an algebraically closed field `k`, an abelian scheme `A` over `Spec k` with
dual data `W`, a homomorphism `lam : A ⟶ W.dual P`, an ample line bundle `L` with
normalization data `B`, `evaluationB`, an inverse `M` with `evaluation`, the equation
`(groupHom lam).hom.hom = mumfordSchemeMapOfLineBundle …`, and an endomorphism `f`. The
conclusion is: there is `n₀` such that for all `n ≥ n₀`, `ψ_n = n • lam + f ≫ lam ≫ f^∨` (with
`f^∨ = dualAbelianSchemeMapFromEvaluation … f`) is an isogeny, and at every point `y` of the
dual, `((hom ψ_n).finrank y : ℚ) = coherentEulerSequence A.X.hom (f^*L).obj _ L n ^ 2`.

**Proof.**

1. *Ampleness.* The published `amplePowerTwist`, applied to `H = L` and `N = f^*L`, gives `n₀`
   such that for `n ≥ n₀` every line bundle with carrier isomorphic to `f^*L ⊗ L^n` is ample.
   Put `L' = LineBundle.tensor P.preservation (f^*L) (powLineBundle L n)`.
2. *A presentation of `L'`.* `e^*L'` is trivial on `Spec k` (`fieldLineBundleTriviality`).
   Take `B'` trivial, with `evaluationB'` the right unitor followed by that trivialization.
   `LineBundle.exists_tensorObj_iso_structureSheaf` gives an inverse `M'` of the normalized
   bundle, with its evaluation `ev'`.
3. *`ψ_n` is the Mumford map of `L'`.* By `pointClass_injective` it suffices to compare
   classes. The underlying morphism of `ψ_n` is `λ^n * (f ≫ λ ≫ f^∨)` (`hom_add_eq_mul`,
   `hom_nsmul_eq_pow`). Its class is `n • cl(λ) + cl(f ≫ λ ≫ f^∨)` (`pointClass_mul`,
   `pointClass_pow`). The underlying morphism of `f^∨` is
   `dualSchemeMap homPicardZeroPullback f` (`dualAbelianSchemeMapFromEvaluation_hom`). By
   `pointClass_mumfordSchemeMapOfLineBundle`, `classOf_mumfordFamily` and
   `pointClass_comp_mumford_comp_dual`, the two sides are
   `n • (m^*[L] - p₁^*[L] - p₂^*[L]) + (m^*[f^*L] - p₁^*[f^*L] - p₂^*[f^*L])` and
   `m^*[L'] - p₁^*[L'] - p₂^*[L']`, with `[L'] = [f^*L] + n • [L]` (`classOf_powLineBundle`).
   Pullbacks are additive, and an identity in an arbitrary additive commutative group,
   proved by `abel`, finishes.
4. *Isogeny.* `AmpleMumfordIsogeny.isIsogeny` applies to `ψ_n` with the presentation of step 2.
5. *Degree.* The published `algClosedFieldAmpleMumfordEulerSquare`, with finite cohomology from
   `smoothProperLineBundleFiniteCohomology` and finiteness and flatness from step 4, gives
   `χ(L')² = (hom ψ_n).finrank y` in `ℤ`. By definition, `coherentEulerSequence … n` is the
   Euler characteristic of `f^*L ⊗ tensorPow L.obj n`, the carrier of `L'`. Casting to `ℚ`
   finishes.

The proof raises `maxHeartbeats` and `synthInstance.maxHeartbeats` because elaboration over the
Library's Picard groups is slow.

`powLineBundle` abbreviates the existing `Langlands.AbelianScheme.MultiplicationTwist.powLB`.
