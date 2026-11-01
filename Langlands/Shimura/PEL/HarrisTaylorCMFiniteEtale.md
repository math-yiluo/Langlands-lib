# Proper CM transitions and finite etale realizations

This module derives properness of every original represented CM transition
from the projective witnesses already present in exact representability.
An etale original transition is consequently finite and defines an object
of the existing finite etale category. For a normal inclusion, the module
bundles the original residual action in that category and removes the
separate finiteness premise from the existing small etale torsor adapter.
Etaleness, scheme surjectivity and invertibility of the exact residual
comparison remain separate premises.

## The exact schemes and original transitions

Fix a family `R` of the existing `CMLevelRepresentation` witnesses. Write

```
X_U = (representedCMSchemeTower ... R).obj U,
s_U = (R U).base.obj.hom : X_U ⟶ Spec F,
f_k = (representedCMSchemeTower ... R).map k : X_U ⟶ X_V
```

for an original small-level transporter `k : U ⟶ V`.
The representing witness contains an admissible scheme over `Spec F`,
smoothness, an actual projective-space closed immersion and a natural
isomorphism from lifted Yoneda to the fixed normalized CM class presheaf.
The tower recovers its maps by fully faithful Yoneda preimage. In
particular `f_k` is the original transporter transition, and the imported
equation `representedCMSchemeTower_over` is

```
f_k ≫ s_V = s_U.
```

No unrelated schemes or extra transition maps are supplied here.
The properness and finiteness results apply to all transporter arrows,
including translating elements, rather than only subgroup inclusions.

## Properness and finiteness from the actual projective witnesses

`representedCMLevel_isProper` proves `IsProper s_U`. It unpacks the
existing `IsHProjective` witness as a natural number `m`, a closed
immersion `i` into the project's polynomial projective space over `F`,
and the factorization of `s_U` as `i` followed by
`projectiveSpaceToSpec F m`. The existing
`Langlands.AlgebraicGeometry.projectiveSpaceToSpec_isProper` instance
proves properness of that particular structural map. Composition with the
closed immersion proves properness of `s_U`.

`representedCMSchemeTower_map_isProper` proves `IsProper f_k`.
The displayed equation identifies `f_k ≫ s_V` with the proper map
`s_U`. The target structural map `s_V` is proper, hence separated.
Mathlib's `IsProper.of_comp` cancels this separated second factor.
Smoothness of the witnesses is not needed for this step.

Under `Etale f_k`, `representedCMSchemeTower_map_isFinite` proves
`IsFinite f_k`. The proof explicitly applies the already published lemma
`Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale`, from
`Langlands.AbelianScheme.TorsionFiniteEtale`. Mathlib's
`IsFinite.of_isProper_of_locallyQuasiFinite`, in
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`, then proves finiteness.
No finiteness hypothesis or geometric-fiber counting premise is added.
The module does not prove `Etale f_k`.

`representedCMFiniteEtaleTransition` packages `f_k` as an object of
`Langlands.AlgebraicGeometry.FiniteEtale.Cover X_V` under that same
etaleness premise. This existing category is the full subcategory of
`Over X_V` with predicate `IsFinite Y.hom ∧ Etale Y.hom`.
Despite the name `Cover`, the predicate does not require surjectivity.
The lemmas `representedCMFiniteEtaleTransition_left` and
`representedCMFiniteEtaleTransition_hom` are definitional equalities:
the object has original source `X_U` and original structural map `f_k`.

## Normal projection, closed residual graphs and finite etale action

Now fix small levels `V ≤ U`, with the subgroup of `U` induced by `V`
normal in `U`. Write

```
p = representedCMNormalProjection ... R U V hVU : X_V ⟶ X_U,
Q = SmallCMResidualGroup D U V,
ρ = representedCMNormalQuotientAction ... R U V hVU.
```

The map `p` is the tower map at `smallCMInclusion D hVU`.
The residual group is the actual quotient
`U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup`.
The inclusion identifies its denominator with `V` inside `U`.
Normality in the entire finite adelic group is not required.
The existing action uses the inverse-right convention: a representative
`g` acts through the original transporter with element `g⁻¹`.
This converts right frame composition to Mathlib's left categorical
action in the existing opposite finite adelic group.

`representedCMNormalProjection_isProper` specializes properness to `p`.
`representedCMNormalProjection_isFinite` derives `IsFinite p` from
`Etale p` by the same properness and local quasi-finiteness argument.

The imported residual graph has first projection identity and second
projection `ρ(g)` into the actual kernel pair `X_V ×[X_U] X_V`.
`representedCMNormalGraph_isClosedImmersion` proves each such graph is
a closed immersion. Its composite with the first pullback projection
is identity, hence a closed immersion. That projection is separated,
being a base change of the proper, hence separated, map `p`.
`IsClosedImmersion.of_comp` cancels the separated second factor.
This graph result needs no etaleness assumption and does not assert
invertibility of the map from the residual-indexed coproduct.

Under `Etale p`, `representedCMNormalFiniteEtaleAction` constructs

```
Action (Langlands.AlgebraicGeometry.FiniteEtale.Cover X_U) Q.
```

Its object is `cover p`, using the derived finiteness of `p`.
Each action morphism is the original `ρ(g)`, bundled over `X_U` by
the already proved equation `ρ(g) ≫ p = p` and then included in the
full subcategory. Extensionality in that subcategory and in `Over X_U`
reduces the identity and multiplication laws to those of the original
action.

The three lemmas `representedCMNormalFiniteEtaleAction_left`,
`representedCMNormalFiniteEtaleAction_hom` and
`representedCMNormalFiniteEtaleAction_ρ_left` are definitional equalities:
the underlying fine scheme is `X_V`, the structural map is `p`,
and each underlying action map is exactly `ρ(g)`.
The finite etale packaging introduces no new action laws or
surjectivity assertion.

## The existing torsor adapter with derived finiteness

Let `κ` denote the previously constructed
`representedCMNormalKernelComparison`, from the actual scheme coproduct
of copies of `X_V` indexed by `Q` to the actual kernel pair of `p`.
On summand `g` it is the original residual graph.

`representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_projective`
retains precisely the following geometric premises:

- `Etale p`;
- `IsIso κ`;
- `Function.Surjective p` on the underlying scheme points.

It concludes the existing
`Coefficients.IsFiniteGeometricTorsor X_U (representedCMNormalEtaleAction ...)`.
This target uses the already constructed action in `X_U.Etale`.
It requires a finite acting group, a finite and surjective structural map
and unique translation on each fiber of separably closed field-valued
points. Etaleness is part of the action object's category.
The proof applies the preceding module's exact adapter; the new
properness and etaleness instances discharge its separate finiteness
premise. That adapter uses the existing finiteness theorem for `Q` and
the unique field-valued transport theorem derived from `IsIso κ`.
The present module does not reprove or assume its transport conclusion.

For `q : CMRepresentabilityStatement ...`,
`cmNormalFiniteEtaleAction` supplies the finite etale action for
`chosenCMLevelRepresentation ... q`. These are exactly the witnesses used
in the existing `cmSchemeTower`, so its structural map is that tower's
original forgetting.
`cmNormalEtaleAction_isFiniteGeometricTorsor_of_projective` gives the
same reduced-premise torsor implication for the existing
`cmNormalEtaleAction` on those chosen witnesses. The choice comes from
the exact existing representability target and does not prove it.

## Source, inputs and remaining obligations

The original source is Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91,
especially p.91, one-based PDF pp.98–99. It is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage specifies the locally Noetherian moduli problem and
pairing-compatible adelic frame orbits; it states smooth projective
representability, finite etale forgetting, right frame composition and
the normal-level Galois-cover assertion with group `U/V`.
The present properness, conditional finiteness, closed-graph and
categorical constructions are derived prerequisites for those
assertions. The implemented proof uses the existing polynomial
projective-space properness theorem and Mathlib's form of Zariski's main
theorem, rather than a proof attributed verbatim to the source.

The arithmetic parameters remain the totally real number field `E`,
CM number field `F` quadratic over `E`, central simple unitary datum `D`,
imaginary quadratic field `L` inside `F`, embedding `τ₀` and the
CM-compatible Harris signature charts `C`. All named prerequisites remain
explicit: pullback-tensor preservation, composition, unit coherence,
associativity, unitor comparison and symmetry; Picard-zero pullback
stability, Mumford-square and universal base change; duality naturality,
polarization base change, relative finite Weil transition, the rational
profinite-integer/adele comparison and torsion finite etaleness.

The representing witnesses still lie in the existing
`ComponentwiseAdmissibleCMBaseCategory` over `Spec F`.
Its local Noetherian, connected-component and geometric-point
prerequisites are retained. This module does not extend the
represented test category or establish existence of those witnesses.
In particular, the projective witnesses are explicit inputs at each
level; no universal projectivity claim is made for arbitrary central
simple unitary data.

Applicable exact representability under the source's division and global
conditions, comparison with the original moduli problem, etaleness and
scheme surjectivity of original forgetting, and invertibility of the exact
`κ` remain proof obligations. The new finiteness result is conditional on
etaleness and the representing witnesses.
Canonical-model comparison, uniformization, coefficient local systems
and their descent comparison are not proved here.

All code and prose in this pair are by Worker 57. The pinned environment
is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
