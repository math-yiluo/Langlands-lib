# Proof of natural opposite-Jacquet duality on the actual rational-point group

Author: Worker 4046. Worker 127 wrote the assembly that this module uses.
That identity is from the previous project instance, and the draft was
carried over into this task. It was conditional, with the Haar reciprocity
identity as its only premise. This module replaces that premise with the
published proof.

Module `Langlands.Representation.Aubert.General.RationalJacquetDualityProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Result

`rationalNaturalJacquetDuality : RationalNaturalJacquetDualityStatement.{u, v}`
proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalNaturalJacquetDualityStatement`.
It holds at arbitrary independent universes `u` (field and group) and `v`
(carriers live in `max (u + 1) v`). The theorem has no parameters or premises
beyond those of the proposition. The proposition and its Markdown are unchanged.

The data are as follows. Let `k` be any nonarchimedean local field, including
positive characteristic. Let `G` be any connected reductive group over `k`,
`i` an actual maximal split torus and `ν` a generic cocharacter. Give `G(k)`
the canonical `pointTopology` with the displayed local compactness,
nonarchimedean and Hausdorff hypotheses, and assume the displayed
`StandardCocharacterStatement`. Let `I` be any finite simple-root subset,
possibly empty, whose standard radical `unipotent i ν I` is closed. Let `ζ` be
any standard cocharacter for `rootSet i ν I`. Write `rP` and `rO` for the
statement's two `jacquetFunctor`s, on the standard decomposition and on the
inverse-cocharacter opposite decomposition with the same literal Levi
`levi i ν I`.

The conclusion is the following. There is one family of isomorphisms
`E A hA : rP.obj A.contragredient ≅ (rO.obj A).contragredient`, defined for
all admissible smooth complex representations `A` of `G(k)`. For every actual
morphism `f : A ⟶ B` of admissible objects it satisfies

`rP.map (contragredientHom f) ≫ (E A hA).hom =
(E B hB).hom ≫ contragredientHom (rO.map f)`.

## Implemented proof

The proof is one application of a published generic theorem. All of its
inputs come from published results.

1. *Instances.* After introducing the field and group data, the proof
   installs `hG.isAffineHom` and `hi.isSplitSubtorus.mono` and gives `G(k)`
   `pointTopology`, exactly as the statement binds them. It then introduces the
   topology instances and the remaining data `ν, hν, hStandard, I, hU, ζ, hζ`.
2. *Central contracting point and basis.* The published theorem
   `rationalOppositeIwahoriBasisStatement`
   (module `RationalOppositeIwahoriBasisProof`) is applied to the same
   arguments. It gives `g : G(k)` and two facts:
   - `hc : ∀ m ∈ levi i ν I, m * g = g * m`;
   - `hb : Jacquet.HasOppositeIwahoriContractionBasis (unipotent i ν I)
     (levi i ν I) (oppositeUnipotent i ζ) g`.

   The second says that arbitrarily small compact open subgroups contract in
   both orientations, under `g` and `g⁻¹`.
3. *Generic duality.* The published theorem
   `exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus`
   (module `IwahoriNaturalJacquetDuality`) is applied with
   `U = unipotent i ν I`, `M = levi i ν I` and `O = oppositeUnipotent i ζ`.
   Its arguments are:
   - `hU`: the statement's closedness hypothesis;
   - `hO`: `isClosed_oppositeUnipotent_localField i ζ`;
   - `hMU`: the `.levi_le_normalizer` field of
     `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I`;
   - `hMO`: the `.levi_le_normalizer` field of
     `opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ`;
   - `g`, `hc` and `hb` from step 2;
   - `hδ`: the published `rationalOppositeHaarReciprocity`
     (module `RationalOppositeHaarReciprocityProof`), applied to the same
     arguments. It states that for every `m : levi i ν I`, the actual Haar
     characters `closedRestrictCharacter` of the two radicals multiply to `1`.
     It uses exactly the closedness and normalizer witnesses listed above.
4. *Exact match.* The generic conclusion is stated for
   `normalizedJacquetFunctor U M hU hMU` and `normalizedJacquetFunctor O M hO hMO`.
   `General.jacquetFunctor h hU` is an `abbrev` for
   `normalizedJacquetFunctor U M hU h.levi_le_normalizer`. So the generic
   conclusion is definitionally the target's existential, with `rP` and `rO`
   unfolded, and `exact` closes the goal. The universes are the generic
   theorem's `uG := u` and `uV := max (u + 1) v`.

No basis, reciprocity, stable-pairing, splitting or duality hypothesis is
added. The family is defined on all admissible objects, and the naturality
square holds for every actual morphism.

## Imported ingredients

- `exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus`
  (Worker 1004, with Worker 127 and Worker 937). For an abstract locally
  compact nonarchimedean group it builds the stable evaluation pairing between
  `U`-coinvariants of `A∨` and `O`-coinvariants of `A`, from a common
  Levi-central contracting element. Admissibility makes the relevant fixed
  spaces finite-dimensional. On these the Fitting splitting gives stable
  images and kernels in both orientations. The pairing is transported to the
  normalized functors, using the reciprocity of the inverse-half Haar
  characters. Naturality follows from naturality of the stable pairing.
- `rationalOppositeIwahoriBasisStatement` (Worker 1045, with Worker 1374's
  cocharacter contracting point). It identifies `M`, `U` and `O` with the
  rational points of `Z(χ)`, `U(χ)` and `U(χ⁻¹)` for
  `χ = groupHom ζ ≫ i`. It takes a point `g` of `Z(χ)(k)`, central there,
  whose powers contract `U(χ)(k)` and whose inverse powers contract
  `U(χ⁻¹)(k)`. An abstract criterion then gives the two-sided basis, using
  unique opposite factorization and the open cell.
- `rationalOppositeHaarReciprocity` (Worker 4204). It writes the three
  subgroups as dynamic subgroups of the inverse cocharacter of
  `groupHom ζ ≫ i`. It then applies
  `dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`, whose two
  structural premises it discharges unconditionally.

This module re-proves none of these. See their own Markdown for details.

## Dependency audit

The audit recursively collected every constant used by the type and value of
`rationalNaturalJacquetDuality`, transitively. The final run reached 130219
constants, 23889 of them in `Langlands`, in 2032 project modules. Most of
these come from the algebraic-group structure theory behind the reciprocity
proof.

No parabolic-induction, cuspidal-support, representation-classification,
geometric-lemma or Frobenius/second-adjointness module or theorem occurs. The
name matches are of other kinds:

- *Linear independence.* Group-scheme results such as
  `GroupScheme.CharacterUnits.linearIndependent_unit` and
  `Descent.galoisFunctions_linearIndependent` (via Mathlib's Dedekind
  `linearIndependent_monoidHom`). These concern characters of tori and Galois
  descent, not characters of smooth representations.
- *Adjunctions.* Algebraic-geometry adjunctions:
  `FaithfullyFlatCoalgebraDescent.coinvariantsAdjunction` and the
  `Spec ⊣ Γ` adjunction.
- *Name collisions.* `classify` names are coordinate classifying maps.
  `adjoint` names are adjoint representations of group schemes, or the
  operator adjoints `Jacquet.compressedAction_adjoint` of finite averaging
  operators under evaluation.

So the proof is unconditional and does not route through the representation
theory that later uses this duality.

## Provenance

The mathematical source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
registered as `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`. The
relevant results are:

- Proposition III.5.5 and III.5.7 on page 7: canonical stable-image lifts and
  their compatibility with averaging;
- III.6.2 on page 7 and III.6.3 on page 8: the pairing of `V_N` with
  `(V∨)_{N̄}`, and its identification as the contragredient over the common
  Levi.

Applying III.6.3 with the opposite parabolic as the initial one gives the
orientation `rP(A∨) ≅ (rO(A))∨`. The coherent naturality square is derived;
the statement's Markdown explains its provenance. The implemented route
follows Casselman's stable-pairing argument in the abstract generic theorem.
This module adds only the specialization to the actual rational-point
subgroups and the identification of the functors.
