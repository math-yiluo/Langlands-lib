# Proper maps on actual arithmetic-level model points

`Langlands.Global.adelicLevelModelProperMap` proves exactly
`Langlands.Global.AdelicLevelModelProperMapStatement` in arbitrary common
universe `u`. Its two public component theorems prove the function-field and
number-field clauses, respectively. The statement isolates the chosen-model
arithmetic-level ingredient of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed p.11, Proposition 4.4, first two
paragraphs of its proof. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The proof uses the actual outside-`S` integer rings, arithmetic level rings,
relative scheme points, scalar base changes and level-model point topologies
named in the statement. Both models may be nonaffine. Properness of the
model morphism and the separated finite-type target imply that the source is
also separated and of finite type: rewrite its structure morphism as the
composition of the given morphism and the target structure morphism, then use
stability under composition. The function-field clause retains finite
constants, the specified compatible finite rational-function-field extension
without a separability premise, and every finite `S`, including empty `S`.
The number-field clause retains every infinite completion independently of
the finite set `S`.

For a coefficient ring `R`, the local models are the actual pullbacks
`ringBaseChange C R X` and `ringBaseChange C R Y`. Three private helpers
derive their local finite type, quasi-compactness and separatedness from
stability under base change. Two further helpers establish properness of
postcomposition on their local point spaces, each carrying the independent
`schemePointTopology`.

For a nondiscrete locally compact Hausdorff topological field, the
base-changed scheme morphism is proper by
`MorphismProperty.overPullbackMap`. Apply the imported
`schemePointLocalProperness_proof` to this actual morphism and the
separated finite-type local models. For a compact Hausdorff local
topological ring with open units, the finite-type source scheme is
quasi-compact over its affine base, and hence its underlying scheme space
is compact. The imported `schemePointCompactness_proof` makes its actual
point space compact. Separatedness gives a Hausdorff target point space by
`t2Space_schemePointTopology`, while `schemePointContinuity_proof` gives
continuity of postcomposition. `Continuous.isProperMap` then gives the
integral-factor conclusion. This second helper needs no identification of
integral points with field points.

The proof supplies nondiscreteness at every field factor. A nontrivially
normed field cannot be discrete, since `NormedField.exists_one_lt_norm`
contradicts `NormedDivisionRing.norm_le_one_of_discrete`. At curve places,
the nontrivial discrete rank-one valuation yields a compatible nontrivially
normed field through `Valued.toNontriviallyNormedField`; the same
construction uses the existing rank-one instance at finite number-field
places. At infinite places, the isometric embedding of the completion into
the complex numbers shows that the norm of `2` is `2`, contradicting the
same discrete norm bound. These arguments concern the original completion
topologies.

At curve places, the imported function-field completion results provide
local compactness of the fields and compactness of the completed integer
rings. At finite number-field places, compactness and openness of the
integer subring provide local compactness of the additive field; the
integer-ring subtype itself is compact. Infinite completions have their
existing local-compactness instances. The imported `adelicLocalFactorUnits`
supplies open units for every factor, and the Hausdorff and topological-ring
instances come from the actual completions and their integer subrings.
Thus the appropriate local helper applies at each factor.

For each arithmetic clause, `IsProperMap.pi_map` makes the product of the
local point maps proper. The imported finite-type level coordinate
homeomorphisms identify the actual source and target level point spaces
with these products. A private naturality lemma combines the definition of
coefficient restriction with `ringPointBaseChangeEquiv_natural`: applying a
coordinate to postcomposition by the model morphism equals
postcomposition by its local base change after applying that coordinate.
Function extensionality identifies the proper product map composed with
the source coordinate homeomorphism with the target coordinate map
composed with the stated level point map. The target homeomorphism's
inducing property proves continuity of the level point map, and
`isProperMap_of_comp_of_inj` transfers properness back to it. No step
requires `S` to be nonempty.

The final theorem assembles the two component theorems into the exact
statement conjunction. This proves properness for already chosen proper
integer-ring models. Existence of such models for arbitrary proper
field morphisms, the valuative preimage equality, the passage to full adelic
points and the eventual stabilization assertion of Proposition 4.4 remain
separate obligations. In particular, the proof avoids the erroneous
identification of arbitrary target integral and field points discussed in
the statement's Markdown.
