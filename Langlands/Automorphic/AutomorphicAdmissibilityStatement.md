# Harish-Chandra finiteness and admissibility of automorphic representations of `GL_n`

Author: Worker 3657. Statement contribution to task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1.

**Scope.** This module `Langlands.Automorphic.AutomorphicAdmissibilityStatement`
makes three definitions and states three propositions. It proves nothing.
Everything is for `GL_n` over a number field `F`.

Definitions:

- `Langlands.Automorphic.centerAnnihilatedForms`;
- `Langlands.Automorphic.annihilatedFormMultiplicitySpace`;
- `Langlands.Automorphic.OperatorSubquotient.IsJointlyAdmissible`.

Propositions:

- `Langlands.Automorphic.HarishChandraFinitenessStatement` (Borel–Jacquet
  §4.3 (i));
- `Langlands.Automorphic.GeneratedFormAdmissibilityStatement` (Borel–Jacquet
  Proposition 4.5, (1) ⇒ (4));
- `Langlands.Automorphic.IrreducibleSubquotientAdmissibilityStatement`
  (Borel–Jacquet §4.6).

The module also has six `local instance` declarations. They put the additive
group structure `Submodule.addCommGroup` on the Library's function spaces
and realization carriers, as `OperatorSubquotient.lean` does. They are local
to this file. Library vocabulary used:

- `AutomorphicForms`, `automorphicFiniteRightAction`
  (`Langlands/Automorphic/Forms.lean`), `automorphicCompactRightAction`
  (`CompactAction.lean`), `automorphicEnvelopingAction`
  (`FullOperatorAction.lean`);
- `ArchimedeanGL.EnvelopingCenter`, the center of the complex universal
  enveloping algebra `ArchimedeanGL.EnvelopingAlgebra` of the real Lie
  algebra of `G_∞ = ∏_{v | ∞} GL_n(F_v)`
  (`Langlands/Global/ArchimedeanLieAlgebra.lean`);
- `standardInfiniteCompact`, the standard orthogonal/unitary maximal compact
  subgroup `K_∞` of `G_∞` (`Langlands/Global/ArchimedeanCompact.lean`);
- `jointMultiplicitySpace` and `Langlands.IsJointlyAdmissible`
  (`Langlands/Automorphic/UnitaryContragredientCriterion.lean`), and
  `OperatorRealization.IsJointlyAdmissible` from the same file;
- `generatedFormOperatorRealization` (`FullOperatorRealization.lean`);
- `OperatorSubquotient` with `finiteRepresentation`, `compactRepresentation`
  and `IsIrreducible` (`OperatorSubquotient.lean`).

**Why it is here.** This task builds the GL_n part (L4) of the global
automorphic library. That an automorphic representation is admissible is a
basic input of it. The proof route of the published
`IsobaricStrongMultiplicityOneStatement` needs it (its Markdown §5, step 3),
and so does every reading of an irreducible operator subquotient as a
restricted tensor product of local components. Until now the Library has
joint admissibility only for cuspidal realizations with unitary central
character (§6).

**Proof targets.** Later proof tasks should prove the three Library
statements. Each has the single universe parameter `u` of the number field.

## 1. Sources

"p." is the printed page and "PDF" the one-based page of the registered file.
In this volume, printed page = PDF page + 5.

| Source ID | SHA-256 | Locators used |
|---|---|---|
| `borel-jacquet-1979-automorphic` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` | Hecke algebra `ℋ(G(ℝ), K)` and its idempotents, §1.1, p.189 (PDF 184); automorphic forms of type `(ξ, J)`, §1.3, and `K`-finiteness, §1.5 (1), p.190 (PDF 185); Theorem 1.7 (Harish-Chandra), p.191 (PDF 186); Lemma 2.1 and §2.2, p.193 (PDF 188); `ℋ = ℋ_∞ ⊗ ℋ_f` and the idempotent `ξ_L`, §3.2, and simple elements, §4.1, p.194 (PDF 189); §4.2 (a)–(d), the type `(ξ, J, K_∞)` and the reduction to `ξ_f = ξ_L`, and §4.3 (i), p.195 (PDF 190); Proposition 4.5 and §4.6, p.196 (PDF 191) |

The registered file is the Corvallis volume, Part I; the article is printed
pp.189–202.

**What Borel and Jacquet state.** Here `G` is a connected reductive group
over the number field `F` and `K_∞` a fixed maximal compact subgroup of
`G_∞`. §4.1 (p.194): an element `ξ ∈ ℋ` is *simple* if it is of the form
`ξ = ξ_∞ ⊗ ξ_f` with `ξ_f ∈ ℋ_f` and `ξ_∞` an idempotent in `ℋ_∞`. By §1.1
(p.189) an idempotent is a finite sum of the measures on the maximal compact
subgroup attached, through their characters, to irreducible representations
of it. So `f * ξ_∞ = f` says that `f` lies in the sum of finitely many
`K_∞`-isotypic components for right translation. By
§3.2 (p.194), `ξ_L` is the normalized characteristic function of a compact
open subgroup `L` of `G(𝔸_f)`, and `f * ξ_L = f` exactly when `f` is right
invariant under `L`.

§4.2 (p.195) lists the conditions on a smooth function `f` on `G(𝔸)`:

> (a) `f(γ · x) = f(x)` (`γ ∈ G(F)`, `x ∈ G(𝔸)`).
> (b) There is a simple element `ξ ∈ ℋ` such that `f * ξ = f`.
> (c) There is an ideal `J` of finite codimension of `Z(𝔤_∞)` which
> annihilates `f`.
> (d) For each `y ∈ G(𝔸_f)`, the function `x ↦ f(x · y)` on `G_∞` is slowly
> increasing.
>
> We shall sometimes say that `f` is then of type `(ξ, J, K_∞)`. We let
> `𝒜(ξ, J, K_∞)` be the space of automorphic forms of type `(ξ, J, K_∞)`.
>
> There exists a compact open subgroup `L` of `G(𝔸_f)` such that
> `ξ_f * ξ_L = ξ_f`. Then `𝒜(ξ, J, K_∞) ⊂ 𝒜(ξ_∞ ⊗ ξ_L, J, K_∞)`.

§4.3 (p.195) assumes `ξ = ξ_∞ ⊗ ξ_L`, writes `𝒜(ξ_∞ ⊗ ξ_L, J, K_∞)` as a
finite direct sum of spaces `𝒜(Γ_c, ξ_∞, J, K_∞)` of automorphic forms on
`G_∞` for arithmetic subgroups `Γ_c`, and concludes:

> In particular, 1.6, 1.7 imply:
> (i) The space `𝒜(ξ, J, K_∞)` is finite dimensional.

Theorem 1.7 (p.191) is the finite dimensionality of `𝒜(Γ, ξ, J, K)` on a
real group: "This theorem is due to Harish-Chandra."

Proposition 4.5 and §4.6 (p.196):

> 4.5. PROPOSITION. Let `f` be a smooth function on `G(𝔸)` satisfying
> 4.2(a), (b), (d). Then the following conditions are equivalent: (1) `f` is
> an automorphic form. (2) For each infinite place `v`, the space `f * ℋ_v`
> is an admissible `ℋ_v`-module. (3) For each place `v ∈ V`, the space
> `f * ℋ_v` is an admissible `ℋ_v`-module. (4) The space `f * ℋ` is an
> admissible `ℋ`-module.
>
> PROOF. The implications (4) ⇒ (3) ⇒ (2) ⇒ (1) are obvious; (1) ⇒ (4)
> follows from 4.3(i).
>
> 4.6. *Automorphic representations.* An irreducible representation of `ℋ`
> is automorphic (resp. cuspidal) if it is isomorphic to a subquotient of a
> representation of `ℋ` in the space of automorphic (resp. cusp) forms on
> `G(𝔸)`. It follows from 4.5 that such a representation is always
> admissible.

## 2. The definitions

Fix a number field `F` and `n : ℕ`. `AutomorphicForms F n` is the Library's
space of automorphic forms on `GL_n(𝔸_F)`. By
`isAutomorphicForm_iff_source_conditions` (`Forms.lean`) its elements are the
continuous functions on `GL_n(F)\GL_n(𝔸_F)` that are smooth at infinity,
right invariant under a compact open subgroup of `GL_n(𝔸_f)`, right
`K_∞`-finite, annihilated by an ideal of finite codimension of the center of
the enveloping algebra, and of moderate growth. These are Borel–Jacquet's
conditions 4.2 (a)–(d) for `G = GL_n`, as `Forms.md` explains. (Condition
(b) is right `K_∞`-finiteness together with right invariance under a compact
open subgroup, by §1.5 (1) and the reduction to `ξ_f = ξ_L` quoted above.)

- **`centerAnnihilatedForms F n J`**, for an ideal
  `J : Ideal (ArchimedeanGL.EnvelopingCenter F n)`, is the subspace of
  automorphic forms `f` with `automorphicEnvelopingAction F n z f = 0` for
  every `z ∈ J`. The operator `automorphicEnvelopingAction` is the action of
  the enveloping algebra by right differentiation at the infinite places.
  On the slice of a form at a finite adele it is the center action of
  `isAutomorphicForm_iff_source_conditions`
  (`finiteSmoothCenterAction` and `finiteSmoothSlice_centerAction` in
  `Langlands/Automorphic/EnvelopingAction.lean`). So this is the space of
  automorphic forms that `J` annihilates, condition 4.2 (c) with the given
  `J`.
- **`annihilatedFormMultiplicitySpace F n J L σ`**, for a subgroup `L` of
  `GL_n(𝔸_f)` and a representation `σ` of `K_∞` on `Fin m → ℂ`, is the space
  of linear maps `φ : (Fin m → ℂ) → AutomorphicForms F n` that lie in
  `jointMultiplicitySpace (automorphicFiniteRightAction F n)
  (automorphicCompactRightAction F n) L σ` and take all their values in
  `centerAnnihilatedForms F n J`. By the definition of
  `jointMultiplicitySpace` these are the `K_∞`-equivariant maps from `σ` into
  the automorphic forms that are right invariant under `L` and annihilated by
  `J`. In symbols, `Hom_{K_∞}(σ, 𝒜^L ∩ ker J)`.
- **`OperatorSubquotient.IsJointlyAdmissible Q`** is
  `Langlands.IsJointlyAdmissible Q.finiteRepresentation
  Q.compactRepresentation`: for every open subgroup `L` of `GL_n(𝔸_f)`, every
  `m` and every representation `σ` of `K_∞` on `Fin m → ℂ`, the space of
  `K_∞`-equivariant maps from `σ` into the `L`-fixed vectors of the quotient
  `Q.Space` is finite-dimensional. This is the predicate
  `OperatorRealization.IsJointlyAdmissible` of
  `UnitaryContragredientCriterion.lean`, transferred from realizations to
  operator subquotients.

`UnitaryContragredientCriterion.md` (§Joint admissibility) explains why this
Hom form of admissibility is the usual one: for every open `L` and every
irreducible continuous representation `τ` of `K_∞`, the `τ`-isotypic part of
`V^L` is finite-dimensional. That equivalence is background and is not
proved in Lean. The Hom form allows any finite-dimensional `σ`, without
continuity or irreducibility.

## 3. `HarishChandraFinitenessStatement`, matched with §4.3 (i)

The statement says: for every number field `F`, every `n`, every ideal `J`
of `ArchimedeanGL.EnvelopingCenter F n` with
`Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)` (finite
codimension), every open subgroup `L` of `GL_n(𝔸_f)`, every `m` and every
representation `σ` of `K_∞` on `Fin m → ℂ`,
`annihilatedFormMultiplicitySpace F n J L σ` is finite-dimensional.

The match with §4.3 (i) for `G = GL_n`:

- **The ideal.** Borel–Jacquet's `J` is an ideal of finite codimension of
  `Z(𝔤_∞)`. Finite codimension is phrased as in
  `isAutomorphicForm_iff_source_conditions`.
- **The finite type `ξ = ξ_∞ ⊗ ξ_L`.** Borel–Jacquet fix `ξ_L` for a compact
  open `L` and an idempotent `ξ_∞`, that is, a finite set `T` of
  `K_∞`-types. Then `𝒜(ξ_∞ ⊗ ξ_L, J, K_∞)` is the sum of the `τ`-isotypic
  parts, `τ ∈ T`, of `𝒜^L ∩ ker J`. The Lean statement instead bounds
  `Hom_{K_∞}(σ, 𝒜^L ∩ ker J)` for one finite-dimensional `σ` at a time, and
  allows any open `L`.
- **Equivalence of the two forms (background, not proved).** Assume §4.3 (i)
  and let `L` be open. `L` contains a compact open `L₀`
  (`OperatorRealization.exists_compact_openSubgroup_le`), and
  `𝒜^L ⊆ 𝒜^{L₀}`. The image of a `K_∞`-map `φ` out of `σ` is a
  finite-dimensional `K_∞`-stable space of smooth functions, on which `K_∞`
  acts continuously. Its irreducible constituents are among the finitely many
  composition factors of `σ`, so `φ` takes values in the space
  `𝒜(ξ_∞ ⊗ ξ_{L₀}, J, K_∞)` for the idempotent `ξ_∞` of those types. That
  space is finite-dimensional, and so is the space of all such `φ`.
  Conversely, the `τ`-isotypic part of `𝒜^L ∩ ker J` is the image of
  `Hom_{K_∞}(τ, 𝒜^L ∩ ker J) ⊗ τ`, so the Lean statement for each `τ ∈ T`
  gives §4.3 (i).
- **The group.** Only `G = GL_n` and the Library's standard `K_∞` are
  treated. Borel–Jacquet's `G` is any connected reductive group and `K_∞` any
  maximal compact subgroup of `G_∞`.

So the Lean statement is §4.3 (i) for `GL_n`, in the Hom form explained
above. Borel–Jacquet derive it from Harish-Chandra's Theorem 1.7 through the
decomposition 4.3 (2) over the finite set `C` of double coset
representatives.

## 4. `GeneratedFormAdmissibilityStatement`, matched with Proposition 4.5

The statement says: for every number field `F`, every `n` and every
`f : AutomorphicForms F n`,
`(generatedFormOperatorRealization F n f).IsJointlyAdmissible`.

- **The module `f * ℋ`.** `generatedFormOperatorRealization F n f` is the
  smallest Library operator realization containing `f`
  (`mem_generatedFormOperatorRealization`,
  `generatedFormOperatorRealization_le_iff`). That is, it is the smallest
  subspace containing `f` and stable under right translation by `GL_n(𝔸_f)`,
  right translation by `K_∞` and the enveloping algebra (the generators of
  `automorphicOperatorAlgebra`, `OperatorCore.lean`). Borel–Jacquet's
  `f * ℋ` with `ℋ = ℋ_∞ ⊗ ℋ_f` (§3.2) is the same space. Convolution with
  `ℋ_f` gives the span of the finite adelic translates of `f`.
  `ℋ_∞ = U(𝔤) ⊗_{U(𝔨)} A_K` (§1.1) gives the `(𝔤, K_∞)`-module generated,
  and for a `K_∞`-finite `f` convolution with the finite measures `A_K`
  spans the same space as the `K_∞`-translates. This identification is
  background.
- **Admissibility.** "`f * ℋ` is an admissible `ℋ`-module" means that each
  simple idempotent `ξ_∞ ⊗ ξ_L` cuts out a finite-dimensional space. That
  space is the sum of finitely many `K_∞`-isotypic parts of the `L`-fixed
  vectors. By §2 this is the joint admissibility of the realization
  (background).
- **The hypothesis.** Borel–Jacquet assume 4.2 (a), (b), (d) and (1), "`f`
  is an automorphic form". The Lean `f` is an element of `AutomorphicForms`,
  which is these conditions (§2).
- **Direction.** Only (1) ⇒ (4) is stated. The converse implications and
  conditions (2), (3) at single places are not stated.

## 5. `IrreducibleSubquotientAdmissibilityStatement`, matched with §4.6

The statement says: for every number field `F`, every `n` and every
`Q : OperatorSubquotient F n` with `Q.IsIrreducible`,
`Q.IsJointlyAdmissible`.

- **Automorphic representations.** An `OperatorSubquotient` is a Library
  operator realization `Q.upper` inside the automorphic forms together with
  an invariant subspace `Q.lower` of it, with the operators acting on
  `Q.Space = Q.upper / Q.lower`. By the identification of `ℋ`-stable
  subspaces in §4 (background), these are the `ℋ`-subquotients of the space
  of automorphic forms in Borel–Jacquet's §4.6. `Q.IsIrreducible` is
  `Q.representation.IsIrreducible` for the whole operator algebra. This is
  Mathlib's `Representation.IsIrreducible`, `IsSimpleOrder` of the
  subrepresentations: the quotient is nonzero and has no other invariant
  subspaces. So an irreducible operator subquotient is an automorphic
  representation in Borel–Jacquet's sense. Conversely, their automorphic
  representations are by definition isomorphic to such subquotients.
- **The conclusion.** "Always admissible" is `Q.IsJointlyAdmissible`, in the
  Hom form of §2.
- **Bundled form.** For `T : IrreducibleOperatorSubquotient F r`
  (`IrreducibleOperatorSubquotient.lean`) the statement applies to
  `T.subquotient` with `T.irreducible`.
- Cusp forms (the "resp. cuspidal" case) need no separate statement. A
  subquotient of a space of cusp forms is in particular an operator
  subquotient.

## 6. Relation to the Library

- **`OperatorRealization.IsJointlyAdmissible`**
  (`UnitaryContragredientCriterion.lean`) is the predicate in
  `GeneratedFormAdmissibilityStatement`. For a realization `S`, the operator
  subquotient with `upper = S` and `lower = ⊥` has the same finite and
  compact actions up to the isomorphism `S ≅ S/⊥`. This comparison is not
  proved here.
- **`CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness`**
  (`Langlands/Automorphic/CuspidalAdmissible/JointAdmissibility.lean`) proves
  that every cuspidal realization with unitary central character is jointly
  admissible, given `PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement`.
  The Library proves that hypothesis (`siegelSetGLFiniteness`,
  `Langlands/Global/AdelicGLSiegelFinitenessProof.lean`), and
  `cuspidalUnitaryContragredientExistence` combines the two. That theorem
  assumes cuspidality and a unitary central character, and says nothing
  about other automorphic representations.
  `IrreducibleSubquotientAdmissibilityStatement` covers all irreducible
  operator subquotients.
- **`ArchimedeanGL.generatedCompactTypeFiniteness`**
  (`Langlands/Global/ArchimedeanGeneratedCompactTypeFinitenessProof.lean`)
  proves `GeneratedCompactTypeFinitenessStatement`: for a `K_∞`-finite and
  center-finite smooth function on `G_∞`, each `K_∞`-type of the
  `(𝔤, K_∞)`-module it generates is finite-dimensional. This is Borel–Jacquet
  Lemma 2.1 (p.193) on one archimedean slice. It does not give
  `HarishChandraFinitenessStatement`. Harish-Chandra's finiteness bounds all
  automorphic forms of a given type at once, and that needs reduction theory
  (Theorem 1.7). Lemma 2.1 bounds only the module generated by one function.
- A search of the Library for `HarishChandra` in `Langlands/Automorphic` and
  `Langlands/Global` found only the cuspidal admissibility files above. The
  `Langlands/Representation/CuspidalSupport/HarishChandra*` modules are about
  the Harish-Chandra homomorphism for `p`-adic groups and are unrelated.

## 7. Proof routes (for the proof tasks; not part of the statements)

1. **`HarishChandraFinitenessStatement`.** Borel–Jacquet's route: reduce to
   compact open `L` and to finitely many `K_∞`-types (§3). Decompose
   `𝒜^L ∩ ker J` over the finite set of double cosets
   `GL_n(F)\GL_n(𝔸)/G_∞ L` (§4.3 (2)), and apply Harish-Chandra's Theorem
   1.7 to each arithmetic subgroup `Γ_c`. Theorem 1.7 itself needs reduction
   theory (Siegel sets, whose finiteness the Library has in
   `siegelSetGLFiniteness`) and the Harish-Chandra argument of Borel–Jacquet's
   reference [11, Theorem 1].
2. **`GeneratedFormAdmissibilityStatement` from
   `HarishChandraFinitenessStatement`.** Let `f` be annihilated by `J` of
   finite codimension. `J` lies in the center and is fixed by `Ad(K_∞)`
   (for `GL_n` the center of the enveloping algebra is fixed by the adjoint
   action of the connected complex group). So `J` annihilates every vector of
   the generated realization. The `L`-fixed vectors of the realization are
   then contained in `𝒜^L ∩ ker J`, and its multiplicity spaces embed into
   `annihilatedFormMultiplicitySpace F n J L σ`. This is Borel–Jacquet's
   proof of (1) ⇒ (4).
3. **`IrreducibleSubquotientAdmissibilityStatement` from
   `GeneratedFormAdmissibilityStatement`.** Choose `f ∈ Q.upper` not in
   `Q.lower`. The generated realization of `f` lies in `Q.upper`
   (`generatedFormOperatorRealization_le_iff`), and its image in the
   irreducible `Q.Space` is nonzero, hence everything. A quotient of a jointly
   admissible module is jointly admissible. Reduce to compact open `L`. Then
   averaging over `L` lifts `L`-fixed vectors of the quotient to `L`-fixed
   vectors, and isotypic projections for `K_∞` commute with the quotient map.
   This is Borel–Jacquet's "It follows from 4.5".

## 8. Not asserted

- the converse implications (4) ⇒ (3) ⇒ (2) ⇒ (1) of Proposition 4.5, or
  conditions (2) and (3) at single places;
- §4.3 (ii)–(iv), the finite dimensionality of cusp forms of a given type
  (§4.4), or anything about square-integrable forms;
- the equivalence between the Hom form of admissibility and the isotypic form
  (§2), or between `f * ℋ` and the generated realization (§4);
- any factorization of an automorphic representation into local components;
- anything for groups other than `GL_n`, for a maximal compact subgroup
  other than `standardInfiniteCompact`, or for function fields.

## 9. Provenance

These are source statements: Borel–Jacquet (1979) §4.3 (i), Proposition 4.5
(1) ⇒ (4), and the admissibility claim of §4.6, for `G = GL_n` over a number
field. The following choices belong to this formalization:

- admissibility is the Hom form `IsJointlyAdmissible` of the Library (all
  finite-dimensional `σ`, all open `L`) instead of Borel–Jacquet's simple
  idempotents (§2, §3);
- §4.3 (i) is stated through `annihilatedFormMultiplicitySpace`, with the
  finite-codimension condition on `J` phrased as in
  `isAutomorphicForm_iff_source_conditions`;
- `f * ℋ` is the Library's `generatedFormOperatorRealization`;
- an automorphic representation is an irreducible `OperatorSubquotient`;
- the definition `OperatorSubquotient.IsJointlyAdmissible` is new here. It is
  the existing realization predicate applied to the actions on the quotient.

The Lean file was checked with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors and no warnings. The
three statements are `def`s returning `Prop`, each with the universe
parameter `u`.
