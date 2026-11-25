# Proof: lifts of a continuous action are compatible with morphisms over the base

The theorem
`Langlands.Analytic.SaturatedAtlasPresentation.quasiEtaleLiftCompatibility`
proves the unchanged published statement
`QuasiEtaleLiftCompatibilityStatement.{u, v, z} K` for every complete
ultrametric normed field `K`, universe-polymorphically. Its hypotheses are
exactly those of the statement. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Route

The proof follows the deduction recorded in
`QuasiEtaleLiftCompatibilityStatement.md`. The uniqueness in Berkovich's Key
Lemma 7.2 (*Vanishing cycles for formal schemes*, 1994, §7, printed p.560) is
proved for commutative squares with `g = 1_V`. It is then applied to `p` and to
the morphisms `(b g).hom ≫ f` and `f ≫ (a g).hom`, which both lie over
`q ≫ (ρ g).hom`.

The uniqueness is proved by a different route from Berkovich's. Berkovich
reduces the commutative case to the cartesian one and uses a generalized
Krasner lemma (his Lemmas 6.6 and 7.3–7.4). Here unramifiedness is used
directly through an annihilator of the Kähler differentials and a
Cayley–Hamilton argument on the diagonal ideal. The proof is spread over
helper modules in `Langlands/Geometry/Analytic/QuasiEtaleRigidity/`, each with
its own Markdown:

1. `DiagonalAnnihilator`, `UnramifiedRigidity`: two bounded maps out of an
   unramified algebra of finite type, agreeing on the base and spectrally close
   on finitely many generators relative to `|e|ⁿ`, are equal.
2. `StrongNearComposition`, `StrongNearPostcomposition`: precomposition of
   `IsNear`; merging finitely many witnesses into common strong numerators;
   postcomposition with a morphism whose preimage of the test domain is
   compact (`exists_isNear_postcomp`).
3. `RigidityTransport`, `RefinementGluing`, `ChartCoverRigidity`: rigidity over
   a set, its transport along monomorphisms, gluing equality of strong maps
   along a source refinement, and rigidity from a finite chart cover.
4. `EtaleRigidity`: rigidity of étale strong maps over compact analytic
   domains, from the unramified finite pieces of `HasAllPiecesAt`.
5. `QuasiEtaleRigid`: `isRigid_of_quasiEtale`, the uniqueness for a
   quasi-étale `p` with compact source.
6. `LiftCompatibilityDeduction`: `exists_open_subgroup_intertwining`, the
   open-subgroup argument from rigidity of `p` and a postcomposition property
   of `f`.

## The final step

After introducing the data, the theorem applies
`exists_open_subgroup_intertwining` with:

- `hfpq : f ≫ p = q`;
- rigidity of `p`, from `isRigid_of_quasiEtale p hp hU`;
- for each test triple `τ` on `U`, a finite set `E` of test triples on `V` such
  that `IsNear σ φ (𝟙 V)` for all `σ ∈ E` implies `IsNear τ (φ ≫ f) f`.

`E` is obtained from `exists_isNear_postcomp f τ`. Its compactness hypothesis
holds: `τ.locus` is compact, hence closed in the Hausdorff space of `U`. Its
preimage under the continuous map of `f` is therefore closed in the compact
space of `V`, hence compact. The conclusion
`IsNear τ (φ ≫ f) (𝟙 V ≫ f)` is rewritten with `Category.id_comp`.

Three hypotheses of the statement are not used: that `X` is Hausdorff, that
`ρ` is continuous, and that `q` is quasi-étale. Continuity enters only through
the lifts `a` and `b`, whose actions are continuous by definition of
`ActionLift`. Compactness of `V` and Hausdorffness of `U` are used in the final
step above. Compactness and Hausdorffness of `U` are used in
`isRigid_of_quasiEtale`.
