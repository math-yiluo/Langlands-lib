# Tensor-admissible intersections inside one full local domain

Worker 1685 constructs the literal intersection of two full local domains `U`
and `V` when both have actual inclusions into one full local domain `Z` of an
arbitrary indexed affinoid atlas. The coefficient, ambient-space and original-index
universes are independent. The field is complete, normed and ultrametric;
arbitrary positive radii, trivial valuations, nonreduced and zero quotients, and
empty domains remain in scope. No Hausdorff assumption on the ambient space is
used.

This is an internal derived construction from the published full local-domain
category, unconditional domain localization and actual domain intersections,
together with `AffinoidPushoutAdmissibility`. Its source context is the local
closed-intersection step in Berkovich, *Étale cohomology for Non-Archimedean
Analytic Spaces* (1993), Lemma 1.2.12, printed p.20 / PDF p.17, registered as
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The genuine tensor and admissibility conventions are inherited from the imported
constructions, following Berkovich, *Spectral Theory and Analytic Geometry over
Non-Archimedean Fields* (1990), §1.1, printed pp.11–12 / PDF pp.25–26, registered
as `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

For an actual inclusion `f : U ⟶ Z`, `f.relativeDomain` has exactly `U.algebra`
as algebra and exactly `f.restriction` as its structural map over `Z.algebra`.
Its locus is the entire inverse image `Z.ambientMap ⁻¹' U.locus`; the inclusion's
proved full representation supplies the full-test factorization property.
`Z.extend D` extends an inner full domain through `Z.domain`, retaining the inner
algebra and composing actual structural maps into `Z`'s original chart. Its
ambient locus is `Z.ambientMap '' D.locus`. Its actual inclusion into `Z` retains
exactly `D.baseMap`.
The extension and its locus formula reuse `LocalDomain.extend` and
`LocalDomain.extend_locus` from `SaturatedAtlasDomainClosure`.

Given `f : U ⟶ Z` and `g : V ⟶ Z`, `interOver f g` extends the actual pushout
intersection `f.relativeDomain.inter g.relativeDomain`. Its algebra is therefore
the unchanged actual pushout of the two original restrictions. The literal-locus
proof uses containment in `Z`, the range formula for `Z.ambientMap`, and the
two inverse-image loci.

`interOverLeft` and `interOverRight` are the canonical full-domain inclusions
constructed from that literal intersection equality. Their restrictions are
proved equal to the two actual pushout quotient legs: thinness identifies their
composites into `Z`, and full-representation cancellation identifies the entire
bounded maps. Applying the admissible genuine tensor-to-pushout construction
then proves `interOver_tensor_isAdmissibleEpi`, including surjectivity and positive
two-sided comparison with the actual quotient seminorm. No open mapping theorem
or nontrivial-valuation assumption is used.

`exists_tensorAdmissible_intersection_of_common_container` packages exactly the
full local-domain intersection and actual canonical inclusion tensor map for this
common-container case. A special subset need only be a finite union of suitable
charts and need not itself be a full local domain. Consequently this result does
not prove the full special-set intersection statement: global closed-immersion
descent across that finite cover remains required.
