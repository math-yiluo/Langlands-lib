# Intrinsic existence of integral relative-root reflections

`Langlands.GroupScheme.RelativeRootReflectionExistenceStatement` is an unproved
proposition at arbitrary universe `u`. For a connected reductive group scheme
over any field and an actual maximal split torus `i : T → G`, it asserts the
existence of `RelativeRootReflectionData i`. For every actual relative root
`a`, this data consists of:

- An actual integral cocharacter `a∨ : Gm → T`.
- A rational point `nₐ` in the already defined `normalizerPoints i`.
- The equality `latticePairing T a a∨ = 2`.
- The formula `weylAction i nₐ χ = χ - latticePairing T χ a∨ • a` for every
  character `χ` of `T`, including characters outside the relative root span.

The proposition also requires each `nₐ` to belong to the actual subgroup
functor `RelativeRoot.kernelCentralizer i a` at `Spec k`. By
`RelativeRoot.mem_kernelCentralizer`, this means that its pullback commutes
with every point of the scheme-theoretic character kernel on every test
scheme and every refinement. In particular, the kernel includes its possible
nonsmooth part. The root is not required to be primitive or indivisible.
The ambient group is not required to be split, quasi-split, or defined over
a perfect field, and there is no characteristic restriction.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`,
Lemma C.2.14 and the ensuing discussion (printed pp.601–602, PDF pp.627–628),
and the proof of Theorem C.2.15, Step 2 (printed pp.604–605, PDF pp.630–631).
The discussion constructs a rational normalizing point inside the connected
centralizer of the full kernel. Step 2 factors the torus endomorphism
`t ↦ t/rₐ(t)` through the actual character `a : T → Gm`. The resulting
cocharacter pairs to two with `a` and gives the displayed integral formula.
The source involution is its own inverse, so the formula agrees with the
Library's inverse-precomposition convention for `weylAction`.

This target is the connected reductive specialization of that source
construction, packaged using the existing actual lattices, rational-point
normalizer, and all-test kernel centralizer. Choosing such data for every
root imposes no compatibility between different choices beyond the stated
laws. The statement also permits an empty root set.

No existence proof is supplied in this file. In particular, the statement
does not assume `HasRelativeRootSystem`, root negation, a coroot assignment,
or rational Bruhat decomposition as an extra hypothesis. It does not assert
generation of the actual normalizer quotient by these representatives, or
faithfulness on the relative root span. Those remain additional obligations
for the full `RelativeRootSystemStatement`. The published conditional
construction in `RootReflectionAssembly` consumes the reflection data once
this existence target has been proved.
