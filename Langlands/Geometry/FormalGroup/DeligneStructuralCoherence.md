# Identity and composition for structural graded base change

This module constructs canonical identity and composition isomorphisms for
structural pullback of the graded tangent sheaf in Deligne's preliminary
four-data package. These are isomorphisms of the actual graded sheaves,
preserving the actual Pi operator and homogeneous subsheaves. Their
naturality, associativity and two identity equations are proved.

The source context is V. G. Drinfeld, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed p.109 (PDF p.3), final paragraph
defining the data eta, T, u, r, continuing on printed p.110 (PDF p.4).
There T is a cyclically graded structural-module sheaf whose homogeneous
components are invertible. The construction here is derived sheaf
infrastructure for that definition; these comparison formulas are not
claimed as separately stated results of the paper. Proposition 2.4,
Section 2 B, printed p.110 (PDF p.4), additionally identifies base change
of data attached to special formal modules. That identification is not
asserted here.

## Objects and hypotheses

The scheme constructions use same-universe schemes S, S', S'' and S''',
a positive natural number d, and a global section a of the structure
sheaf on S. `GradedPiSheaf d S.sheaf (schemeScalar S a)` has an actual
structural-module sheaf M, an operator Pi with Pi^d equal to scalar
multiplication by a, and an internal homogeneous decomposition indexed by
`ZMod d`. Scheme morphisms are arbitrary; no flatness or nilpotence
assumption is needed for these comparisons.

The imported `GradedPiSheaf.pullback f` is structural module pullback.
Its homogeneous components are the sectionwise ranges of the pulled
split component inclusions. `pullbackComponentIso f i` identifies the
structural pullback of the original component with this range subsheaf.
The present construction therefore compares actual subsheaves rather
than asking for independent certificates of grading preservation.

## Constructing graded isomorphisms

The generic constructor `GradedPiSheaf.isoOfComponents` works on a site.
It takes an isomorphism e of the underlying module sheaves, its Pi
commutation equation, actual component isomorphisms c_i, and the squares

`c_i.hom ≫ inclusion_N,i = inclusion_M,i ≫ e.hom`.

Evaluating these squares on sections proves homogeneity of e. Cancellation
of the invertible total map derives the inverse inclusion squares and
the inverse Pi equation, hence proves homogeneity and Pi compatibility
of e inverse. Both inverse identities follow from the corresponding
identities for e. The lemma `isoOfComponents_hom_componentMap` proves
that restriction of the resulting homogeneous map is precisely the
supplied component map, by evaluation of the square and subtype
extensionality.

`pullbackComponentIso_hom_inclusion` records the defining inclusion
square of the range comparison. `pullbackComponentIso_inv_inclusion`
deduces the inverse square by cancellation of its isomorphism.

## Identity and composition

`pullbackIdComponentIso` first inverts the range comparison for identity
pullback and then applies `Scheme.Modules.pullbackId` to the original
component. Naturality of the latter isomorphism proves its inclusion
square. The generic constructor gives

`pullbackIdIso : M.pullback (𝟙 S) ≅ M`.

Its total module isomorphism is exactly the structural pullback identity
isomorphism. Its Pi square is naturality of that isomorphism for M.pi.
`pullbackIdNatIso` proves naturality for every actual graded morphism.

For f : S' → S and g : S'' → S', `pullbackCompComponentIso` composes four
actual isomorphisms: the inverse range comparison for g, pullback by g
of the inverse range comparison for f, the structural composition
comparison on the original component, and the range comparison for
g ≫ f. The inclusion square follows by naturality of the structural
comparison, preservation of composition by pullback, and the two range
inclusion squares. This produces

`pullbackCompIso f g : (M.pullback f).pullback g ≅ M.pullback (g ≫ f)`.

Its underlying map is exactly `Scheme.Modules.pullbackComp g f` on
M.module. `pullbackCompNatIso` proves naturality for graded morphisms.
The global coefficient sections for iterated and composite pullback,
and for identity pullback, agree definitionally.

## Coherence proofs and scope

`pullbackCompIso_assoc` equates the two composites from triple pullback
to pullback along h ≫ g ≫ f. `pullbackCompIso_id_left` identifies
composition with the identity on S with pullback of the original
identity comparison. `pullbackCompIso_id_right` identifies composition
with the identity on S' with the identity comparison on M.pullback f.
Each proof uses extensionality for isomorphisms, graded morphisms and
Pi-compatible morphisms, reducing the goal to the corresponding actual
`SheafOfModules.pullback_assoc`, `pullback_id_comp` or `pullback_comp_id`
identity.

These constructions also apply to the graded sheaf underlying a
`LinePiSheaf`; the current module does not assemble a separate category
of line objects. Coherence for the ordinary inverse-image flat lattice,
the full rational frame, u, or the four-data isomorphism-class maps is
not established here. Admissibility transport, the admissible Nilp
functor, the integral determinant comparison, the normalized PGL action,
the special-formal-module comparison of Proposition 2.4 and
representability remain separate obligations.
