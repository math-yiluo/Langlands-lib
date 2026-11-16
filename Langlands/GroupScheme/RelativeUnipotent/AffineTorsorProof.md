# Affine torsors under finite vector-bundle group series

Worker 595, with the vector-bundle cocycle constructions of Workers 645 and 682.

`Langlands.GroupScheme.relativeUnipotentAffineTorsor` proves exactly the published
`Langlands.GroupScheme.RelativeUnipotentAffineTorsorStatement.{u}` in every universe
`u`. For every affine scheme `S`, every smooth affine group scheme `U` over `S`
supplied with `RelativeUnipotent.HasFiniteVectorBundleSeries U`, and every actual
fpqc `U`-torsor `X`, it produces a scheme morphism `s : S ⟶ X.left` satisfying
`s ≫ X.hom = 𝟙 S`. The lawful action is supplied by `ModObj U.X X`; the torsor
conditions are flatness, surjectivity and quasi-compactness of `X.hom` and
invertibility of the actual shear `ModObj.leftSMul U.X X`.

The implemented proof composes two internal results. First,
`RelativeUnipotent.HasFiniteVectorBundleSeries.cocyclesVanish` proves vanishing
on every affine test base change and every affine flat surjective cover. Its
induction uses the supplied actual vector-bundle normal series, the affine
vanishing theorem for sections of quasi-coherent sheaves, and the
kernel/quotient cocycle reduction. In particular, the successive quotients are
actual additive groups of finite locally free module sheaves with natural
section coordinates; they need not be globally free and their local ranks may
vary.

Second, `RelativeUnipotent.AffineCocycle.exists_section_of_cocyclesVanish_at_base`
extracts a section of the original torsor from that vanishing. Quasi-compactness
over the affine base permits an affine flat surjective cover with a local
torsor point. The identity-base-change comparison supplies a primitive in the
original acting group. Correcting the local point by that primitive makes it
invariant, and effective-epimorphism descent gives the claimed section. Thus
neither a section nor a cocycle-vanishing premise is added to the target.

This proof is an internal deduction from `VectorBundleSeriesCocycle` and
`AffineCocycleReduction`, using the unchanged statement and its geometric series
predicate. The original motivation is the affine cohomology argument in Brian
Conrad, *Reductive group schemes* (2014), Corollary 5.4.8, p.179, as recorded in
the statement's source correspondence. The implementation proves the actual
fpqc torsor conclusion directly by affine cocycle descent, so it needs no
comparison with degree-one étale cohomology.

The base may be non-noetherian or disconnected. No field of definition, global
free basis, chosen series length, or affine total space of the torsor is
assumed. The radical filtration and the construction of the relative Levi
moduli torsor are separate obligations; this result alone does not prove
`RelativeLeviAffineExistenceStatement`. No statement or imported pair is changed.
