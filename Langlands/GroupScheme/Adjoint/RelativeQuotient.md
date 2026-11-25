# Supplied relative adjoint quotients and their inner actions

This is an internal interface and adapter built from published Library
definitions and descent theorems. It does not assert existence of a quotient.
Its purpose is to supply the integral and generic action compatibility needed
by the integral inner-isomorphism torsor construction.

## The supplied quotient

For any scheme `S` in universe `u`, group schemes `G, A` over `S`, and actual
group-scheme homomorphism `q : G ⟶ A`, `IsRelativeAdjointQuotient q` is the
conjunction, packaged as a proposition structure, of `IsReductive G`,
`IsReductive A`, and `RelativeRoot.IsFppfQuotient (center G) q`.
The last condition means that the underlying scheme morphism is flat,
surjective and locally of finite presentation, and that the range of the
actual kernel inclusion equals the full scheme-theoretic centre of `G` on
every test scheme. Surjectivity concerns the underlying spaces; rational
points need not lift.

There are no assumptions on the base, and no smoothness assumption on the
centre. The quotient need not be finite. The predicate deliberately reuses
the existing full-centre quotient condition rather than adding new
universal-property premises.

## Implemented adapters

`quasiCompact` follows from affineness of the structure morphisms of `G`
and `A`: the composite of `q` with the structure map of `A` is the structure
map of `G`, and `A` is quasi-separated over `S`.
`kernelCenter` uses separatedness of `A` and the full kernel-range equality
to obtain the closed actual centre representative.

`innerAction` descends conjugation along the resulting fpqc morphism using
`AutomorphicAction.quotientAction`. Central kernel points act trivially by
the published `conjugation_kernelActsTrivially` theorem. The descended
action is an actual morphism of schemes, acts by group automorphisms, and
is defined on every relative test scheme, including points without a global
lift along `q`. `innerAction_restrict` recovers conjugation after restriction
along `q`; `innerAction_unique` derives uniqueness from fpqc descent.

`baseChange` combines reductivity under arbitrary base change with
`RelativeRoot.IsFppfQuotient.baseChange_center`. `innerAction_baseChange`
uses the uniqueness just proved: restriction of the pulled-back action is
pulled-back conjugation, which is conjugation after base change.

`fieldQuotient` applies to every field `k : Type u` and every actual morphism
`Spec k ⟶ S`, not just residue fields. Reductivity supplies connected
reductive source and target fibres. The published
`centerQuotientCenterTrivial` theorem gives trivial full target centre, and
`isAdjointQuotient_of_fppf_kernel_range` supplies `IsAdjointQuotient` with
both its group and scheme universal properties. Its centre is the actual
kernel, without replacing it by a reduced subgroup or by rational points.
`innerAction_fieldQuotient` identifies the pulled-back relative action with
this field quotient's published `IsAdjointQuotient.innerAction`; both are
the descent of the same conjugation action. Proof irrelevance identifies
the choices of proofs in these constructions.

## Provenance and scope

All claims here are internal consequences of the imported published Lean
results, as described above; no new literature assertion is made.
In particular, no relative quotient, relative automorphism scheme, outer
isomorphism component or torsor is constructed by this module. Existence
of a relative quotient and of the required torsor are proved separately,
by `relativeAdjointQuotientExistence` (`Adjoint.RelativeExistenceProof`)
and `genericInnerIsomorphismTorsorExistence`
(`Reductive.GenericInnerIsomorphismTorsorExistenceProof`). The original
`GenericInnerIsomorphismTorsorExistenceStatement` and its dependencies are
unchanged.
