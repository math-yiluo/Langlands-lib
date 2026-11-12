# Modular characters of the actual rational-point group and its standard parabolics

Module `Langlands.Representation.Aubert.General.RationalParabolicModulusProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Result

`rationalParabolicModulus : RationalParabolicModulusStatement.{u}` proves the
published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalParabolicModulusStatement`
(module `Langlands.Representation.Aubert.General.RationalParabolicModulusStatement`)
for every universe `u`, under exactly its premises. Let `k` be a nonarchimedean
local field, `G` a connected reductive group over `k`, `i : T.toGrp ⟶ G` a maximal
split torus, `ν` a generic cocharacter and `I` a finite set of simple roots. Give
`RationalPoint k G.X` its published point topology, and assume the statement's
premises: local compactness, the nonarchimedean group property, Hausdorffness,
`StandardCocharacterStatement`, closedness of `unipotent i ν I` and
`parabolic i ν I`, and continuity of the Levi projection. The theorem then gives
both conclusions:

1. Mathlib's `Measure.modularCharacter` on `G(k) = RationalPoint k G.X` is
   identically `1`.
2. On the actual standard parabolic `P = parabolic i ν I`, Mathlib's modular
   character equals `HaarModulus.closedRestrictCharacter` of the conjugation
   action of `P` on its unipotent radical `U = unipotent i ν I`.

No premise is added, and the statement's Lean/Markdown pair and its imports are
unchanged.

## Proof

The proof is a single term that composes three published, proved Library results:

1. `rationalParabolicModulus_of_reductiveUnimodularity` (module
   `Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction`)
   derives the exact `RationalParabolicModulusStatement` from two proposition
   inputs: `RationalReductiveUnimodularityStatement` and
   `GroupScheme.DynamicCentralizerReductiveStatement`. At each input it applies the
   unimodularity input to `G` for the first conclusion. For the second, it takes
   local compactness of the literal Levi from the closed equalizer of the
   continuous projection. It then transfers unimodularity of the connected
   reductive standard Levi representative to `levi i ν I`, and finishes with
   `standardParabolic_modularCharacter_of_levi`.
2. The first input is `rationalReductiveUnimodularity` (module
   `Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof`).
   That proof bounds the modular character by the Haar scaling factor of
   `det Ad(g)`, and this determinant is `1` for connected reductive groups.
3. The second input is `Langlands.GroupScheme.dynamicCentralizerReductive` (module
   `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`). It shows that dynamic
   centralizers, and so the standard Levi representatives, are connected reductive.

The theorem's axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal assembly of Library results. The statement's Markdown cites Renard,
*Représentations des groupes réductifs p-adiques* (2026), V.5.4: the Proposition
that `G` is unimodular and the Lemma computing the modular function of a standard
parabolic. The implemented proof follows the Library proofs above. It does not
use the Cartan or Iwahori decomposition arguments of the source.
