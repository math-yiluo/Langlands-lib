# Proof: every actual adelic automorphic form has uniformly moderate growth

Module `Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthProof`. The theorem

```lean
theorem Langlands.Automorphic.GroupSchemeFunctions.adelicAutomorphicUniformGrowth :
    AdelicAutomorphicUniformGrowthStatement.{u}
```

proves the Library statement `AdelicAutomorphicUniformGrowthStatement` (module
`GroupSchemeAutomorphicUniformGrowthStatement`) at an arbitrary universe `u`. Unfolded, the
statement is

```lean
∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N d : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho →
    CompactIwasawa.IsMaximalCompact Kinf → 0 < N →
    ∀ f : FinitePlotSmoothRationalFunctions F G,
      IsAdelicAutomorphicForm F G Kinf rho hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) f →
        HasAdelicUniformModerateGrowth F G rho hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) f
```

In words: let `G` be a connected reductive affine group scheme over a number field `F`, smooth
of relative dimension `d`, let `Kinf` be a maximal compact subgroup of the infinite adelic
points and let `rho` be a closed matrix representation of size `N > 0`. Every original finite
plot-smooth rational function `f` that is `Kinf`-finite, finite under the centre of the actual
enveloping algebra and of moderate growth for the source norm of `rho` has uniformly moderate
growth: there is one real `r` such that for every element `a` of the actual enveloping algebra
some positive `C` bounds `‖(adelicEnvelopingAction a f)(g)‖` by `C * ‖g‖ ^ r` at every adelic
point `g`.

## Proof as implemented

The proof is a single term that combines three Library theorems.

1. `adelicAutomorphicUniformGrowthReduction.{u}` (module
   `GroupSchemeAutomorphicUniformGrowthReductionProof`) proves
   `AdelicAutomorphicUniformGrowthReductionStatement.{u}`, the implication
   `LieGroupEllipticInteriorEstimateStatement.{u, u} → AdelicAdaptedCasimirStatement.{u} →
   AdelicAutomorphicUniformGrowthStatement.{u}`.
2. `Langlands.Geometry.Manifold.lieGroupEllipticInteriorEstimate` (module
   `Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof`) proves
   `LieGroupEllipticInteriorEstimateStatement.{u, v}` for all universes. It is the interior
   estimate for elliptic left-invariant word operators on a Lie group: a smooth solution of an
   elliptic word equation has every word derivative at the identity bounded by a constant times
   its supremum on a fixed compact set. It is used at `u, u`, the universes of the model space
   `smoothModel F d` and of `InfiniteAdelicGroupPoints F G` for `F : Type u`.
3. `adelicAdaptedCasimir` (module `GroupSchemeAdaptedCasimirProof`) proves
   `AdelicAdaptedCasimirStatement.{u}`: the tangent Lie algebra of the infinite adelic points is
   spanned by vectors `X i`, those with `i ∈ J` tangent to smooth curves in `Kinf`, such that
   `∑ i, X i ^ 2 - 2 • ∑ j ∈ J, X j ^ 2` is central in the actual enveloping algebra.

Applying the reduction to the two proofs gives the statement. The reduction does the analysis:
the Casimir element gives an elliptic equation satisfied by every left translate of the form,
the interior estimate bounds every derivative at `g` by the supremum of the form near `g`, and
the moderate-growth bound with the submultiplicativity of the height gives one exponent for all
derivatives (see the page of `GroupSchemeAutomorphicUniformGrowthReductionProof`).

## Declarations

- `adelicAutomorphicUniformGrowth : AdelicAutomorphicUniformGrowthStatement.{u}` (theorem).

## Provenance

C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf` (printed page = PDF page + 17):

- I.2.3, printed p. 25: "`φ` and its derivatives have uniformly moderate growth if
  `∃ r ∈ ℝ, ∀ X ∈ 𝒰, ∃ c_X ∈ ℝ, ∀ g ∈ G, |δ(X)φ(g)| ≤ c_X ‖g‖^r`", the quantifier order of
  `HasAdelicUniformModerateGrowth`.
- I.2.5, Lemma (a), printed p. 27: for a smooth compactly supported `f` and `φ` of moderate
  growth, `δ(f)φ` and its derivatives have uniformly moderate growth.
- I.2.17, printed pp. 37–39: automorphic forms (conditions (i)–(iv): moderate growth,
  smoothness, `K`-finiteness, `𝔷`-finiteness); after the lemma citing Harish-Chandra (a
  compactly supported `f` with `δ(f)φ = φ`, printed p. 38) the text concludes on printed
  pp. 38–39 that for all `P` and all automorphic `φ`, "`φ` and its derivatives have moderate
  growth". The theorem here is the case `P = G` of that conclusion for the Library's actual
  adelic forms. The proof in the Library replaces the convolution identity `δ(f)φ = φ` by the
  elliptic interior estimate applied to the adapted Casimir element.
