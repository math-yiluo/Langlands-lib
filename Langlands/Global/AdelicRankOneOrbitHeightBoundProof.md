# The rank-one parabolic rational-orbit height bound

Author: Worker 17. Coauthor of the helper modules: Worker 5253 (the line-character
dominance bound in `Langlands.Global.AdelicMinimalParabolicLineBound`).

This module proves the Library proposition
`Langlands.Global.RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement`
(module `Langlands.Global.AdelicRankOneOrbitHeightBound`). The proof is the final
composition step of Springer's §3.6 argument (T. A. Springer, *Reduction theory over global
fields*, 1994, §3.4–§3.6, printed pp. 215–216; registered source
`springer-1994-reduction-global-fields`).

## Statement

The main theorem is

`theorem rankOneParabolicRationalOrbitHeightBound : RankOneParabolicRationalOrbitHeightBoundStatement.{u}`

in the namespace `Langlands.Global.RepresentationGrowth`. Its type is exactly the target
statement and it has no hypotheses. Unfolded, it says the following. Let `F : Type u` be a
number field and `G` an affine, locally finite type, connected reductive group scheme over
`F`. Let `iF : TF → G` be a maximal split torus with a generic cocharacter `νF` whose simple
relative roots form a singleton `{αF}`. Let `ρ` be a matrix representation with a
coordinate line `j` whose exact stabilizer is the minimal standard parabolic `P(νF)`. Then
the orbit height of `Pi.single j 1` is uniformly bounded on `G(𝔸_F)¹` after a rational right
translate (`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)`).

The module also contains two intermediate theorems with the same conclusion. Each of their
hypotheses is a published Library proposition:

- `rankOneParabolicRationalOrbitHeightBound_of_springerInputs (hF hO hM hT)`, where
  - `hF : SplitAdelicFundamentalSetStatement.{u}` is Springer's fundamental-set property (F)
    for split groups (module `Langlands.Global.AdelicSplitFundamentalSet`);
  - `hO : SplitSiegelOverlapStatement.{u}` is Springer's Proposition 2.6 for split groups
    (module `Langlands.Global.AdelicSplitSiegelOverlap`);
  - `hM : SplitGaloisOverlapMatchingStatement.{u}` is Springer's §3.5 factorization over a
    Galois splitting field, with Galois inverse-orbit matching of the maximal parabolic
    attached to a small simple root (module `Langlands.Global.AdelicGaloisOverlapMatching`).
    It is itself an implication from `hF` and `hO`;
  - `hT : GaloisBorelTwistingStatement.{u}` says that every connected reductive group over a
    number field has a finite Galois split maximal model with a generic cocharacter and a
    Galois twisting of its split Borel pair (Springer §3.4; module
    `Langlands.Global.AdelicGaloisBorelTwisting`).
- `rankOneParabolicRationalOrbitHeightBound_of_galoisInputs (hM hT)`, which has only the
  hypotheses `hM` and `hT`.

The main theorem discharges all four hypotheses with published Library proofs:

| Hypothesis | Published proof | Module |
| --- | --- | --- |
| `hF` | `Langlands.Global.AdelicSiegelFactors.splitAdelicFundamentalSet` | `Langlands.Global.AdelicSplitFundamentalSetFromCover` |
| `hO` | `Langlands.Global.AdelicSiegelFactors.splitSiegelOverlap` | `Langlands.Global.AdelicSplitSiegelOverlapProof` |
| `hM` | `Langlands.Global.AdelicGaloisUnit.splitGaloisOverlapMatching` | `Langlands.Global.AdelicGaloisOverlapMatchingProof` |
| `hT` | `Langlands.Global.AdelicGaloisUnit.galoisBorelTwisting_of galoisTwistNormOne galoisTwistSubgroup` | `Langlands.Global.AdelicGaloisBorelTwistingProof`, `Langlands.Global.AdelicGaloisTwistSubgroupProof` |

For `hT`, `galoisBorelTwisting_of` derives `GaloisBorelTwistingStatement` from Lemma S1
(`GaloisTwistNormOneStatement`) and Lemma S2 (`GaloisTwistSubgroupStatement`), and
`galoisTwistNormOne` and `galoisTwistSubgroup` prove these two lemmas.

Provenance: derived. The decomposition into these four inputs follows Springer: §3.4
supplies the twisting `ŵ_s`, §3.5 the factorization `g = x t u γ` over the splitting field
and the dichotomy on the simple roots, and §3.6 the height estimate in semisimple rank one.
Springer proves Proposition 2.6 in §2 (printed p.213) and (F) for split groups in
§3.2–§3.3 (printed p.214), before the Galois argument of §3.4–§3.6. In the intermediate
theorems these split results are the hypotheses `hF` and `hO`.

## Proof

`rankOneParabolicRationalOrbitHeightBound_of_springerInputs hF hO hM hT`:

Fix the data of the target statement: `F`, `G` (with `[IsAffineHom G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`), `hG : IsConnectedReductive G`, `TF`, `iF`, `hiF`, `νF`,
`hνF`, `αF`, `hαF`, `n`, `ρ`, `j` and `hstab`.

1. The instance `IsAffine G.X.left` is `isAffine_of_isAffineHom G.X.hom`, as in the
   statements of `hT` and `hM`.
2. `hT F G hG` gives a finite Galois split maximal model `D` of `G`
   (`FiniteGaloisSplitMaximalModel`). Its carrier `L = D.carrier` is a finite Galois
   extension of `F` with a split maximal torus `D.inclusion : D.torus → G_L`. `hT` also
   gives a generic cocharacter `ν` (`hν : IsGenericCocharacter D.inclusion ν`) and a Galois
   twisting `htw : HasGaloisBorelTwisting F L G D.torus D.inclusion ν`. The instance
   `NumberField L` is `NumberField.of_module_finite F L`, as in both statements.
3. `hM hF hO F G hG D ν hν htw` gives
   `HasTwistedOverlapMatching F L G D.torus D.inclusion ν`.
4. The core theorem
   `Langlands.Global.AdelicGaloisUnit.hasUniformNormOneRationalOrbitHeightBound_of_twistedOverlapMatching`
   (helper module `Langlands.Global.AdelicRankOneGaloisOrbitHeight`) takes exactly the body
   of `HasTwistedOverlapMatching`, which unfolds definitionally. It is applied with
   `T := D.torus` and `i := D.inclusion`, together with:
   - `D.isConnectedReductive hG`: connected reductivity of `G_L`;
   - `D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus`: the inclusion is a maximal
     split torus (Library lemma `IsMaximalTorus.isMaximalSplitTorus`);
   - `D.isMaximalTorus`: the inclusion is a maximal torus;
   - the original data `hG`, `iF`, `hiF`, `νF`, `hνF`, `αF`, `hαF`, `ρ`, `j` and `hstab`.

   Its conclusion is the required bound.

`rankOneParabolicRationalOrbitHeightBound_of_galoisInputs hM hT` is
`rankOneParabolicRationalOrbitHeightBound_of_springerInputs splitAdelicFundamentalSet
splitSiegelOverlap hM hT`.

`rankOneParabolicRationalOrbitHeightBound` is
`rankOneParabolicRationalOrbitHeightBound_of_galoisInputs splitGaloisOverlapMatching
(galoisBorelTwisting_of galoisTwistNormOne galoisTwistSubgroup)`.

All three theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Helper modules

The core theorem and its prerequisites are in these modules, each with its own Markdown:

- `Langlands.GroupScheme.Rational.RankOneParabolicConjugacy`: conjugacy of proper rational
  parabolics in rank one, and the coset lemma `h P(ν) h⁻¹ ≤ P ⇒ h ∈ P(k)`.
- `Langlands.GroupScheme.Rational.RankOneGaloisParabolicDescent`: descent of the
  Galois-matched parabolic over `L` to a proper rational parabolic over `F`, and the
  conjugator `m₀` into it.
- `Langlands.Global.AdelicGaloisSubsetDescent`: compact representatives of compact subsets
  of quotients, and their use for scalar extension.
- `Langlands.Global.PrimitiveAdelicHeightInclusion`: `H_L(ι x) = H_F(x)^[L:F]`.
- `Langlands.Global.AdelicScalarExtensionOrbitHeight`: adelic matrices and orbit heights
  under `scalarExtensionNormOneMap`.
- `Langlands.GroupScheme.Rational.MinimalParabolicLineCharacter` and
  `Langlands.Global.AdelicMinimalParabolicLineBound` (Worker 5253): a uniform bound for the
  line character of the minimal standard parabolic on bounded-root torus points.
- `Langlands.Global.AdelicRankOneGaloisOrbitHeight`: Springer's §3.6 estimate in both cases
  of the §3.5 dichotomy, and the core theorem.
