# Affine representation of actual line-bundle Hom presheaves

`ProperLineBundleHomRepresentabilityStatement.{u}` states the following
rank-one proper-Hom result. For a proper flat locally finitely presented
morphism `f : X → S`, any scheme `T` over `S`, and two actual line bundles
`L` and `M` on `T ×_S X`, there is an actual scheme `H` affine and locally
of finite presentation over `T` representing all module homomorphisms
between their ordinary pullbacks. This module states the proposition and
does not prove it.

The represented presheaf is the published
`CoherentSheaves.intrinsicModuleHomPresheaf` for the projection
`T ×_S X → T` and the underlying module sheaves `L.of.obj` and `M.of.obj`.
Its values include every module map, including zero maps, and are not
restricted to isomorphisms. Representation is a natural isomorphism on
the full slice `Over T.left`, with the published coherent restrictions
and explicit value-universe lift. All empty, nonreduced, nonnoetherian
and non-quasi-compact tests are retained.

No projectivity, smoothness, reducedness, connectedness, section, or
global-functions hypothesis is present. The base and parameter scheme
are arbitrary. Flatness of `f` is explicit; the Picard atlas application
has this hypothesis because its ambient scheme lies over a field.
Affine local finite presentation is finite presentation since affine
morphisms are quasi-compact and separated.

## Source derivation

This is a rank-one specialization of Stacks Project, Section 99.3,
Situation 99.3.1 and Proposition 99.3.10 (Tag 08K6), in the registered
source `stacks-hom-functor-08js-2026-11-02`. The complete retained
`08JS.html`, including the proofs and two typo-only comments, was read.
The source folder SHA-256 is
`2d60cda5ae13d9daa5c318ca4cd199e47a3a00b39f5062492b2207f7b56432c4`.

Apply the proposition to `T ×_S X → T` and the two line-bundle modules.
Properness, flatness and local finite presentation survive base change;
properness also supplies quasi-compactness and separatedness, hence the
finite-presentation hypothesis of the source. A line bundle is a
finitely presented quasi-coherent module. A line bundle on a flat scheme
over `T` is flat over `T`, as recorded in the published line-bundle
flatness and coherent-family inclusion constructions. Properness of the
ambient projection supplies proper support of the target. Thus the
source yields a representing algebraic space affine of finite
presentation over `T`; an affine algebraic space over a scheme is a
scheme. This last passage and the comparison with the entire imported
presheaf remain proof obligations.

## Role in the Picard atlas

This focused statement keeps the full coherent-source Hom result
separate. Its intended proof may use the published finite projective
Čech representative for locally trivial modules over a noetherian base,
applied to `L` dual tensor `M`, followed by noetherian approximation and
descent. These are remaining proof obligations, rather than conclusions
of this statement. No perfect-approximation theorem or general
coherent-family atlas is a premise.

For a flat ambient morphism, the published
`PicardGroupoid.relativeToFamily` sends each actual line bundle to its
flat finitely presented coherent family without changing its underlying
module. The natural isomorphism
`CoherentSheaves.FamilyGroupoid.homPresheafIntrinsicIso` identifies the
corresponding coherent-family Hom presheaf with the presheaf used here.
Consequently this statement is suited to the inverse-equation
construction of line-bundle Isom schemes. It supplies neither an Isom
representation proof nor a Picard-stack atlas.
