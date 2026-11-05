# Rational contracting points and central isogenies

This internal construction proves rational-point lifting for the actual
central isogeny supplied to it. Let `k` be any field of arbitrary universe
`u`, let `q : C → G` be a central isogeny, and suppose the underlying schemes
of `C` and `G` are separated. Let `χ : Gm_k → G` be a cocharacter. Every
`k`-point of the dynamic identity-limit subgroup `Dynamic.unipotent χ` has a
`k`-point lift through `q`.

For a point `g`, choose its orbit extension `e` with zero value equal to the
identity. The existing `CommutatorDescent.hom` sends the pair `(χ(t), g)`
to a punctured affine-line curve in `C`. Its composite with `q` is
`χ(t) g χ(t)⁻¹ g⁻¹`, which extends as `e` times the inverse constant curve
`g`. A central isogeny is finite, flat and surjective, so the commutator
descent applies and `q` is proper. The relative proper affine-line lifting
lemma extends the punctured curve in `C` while retaining that exact composite.
At zero the composite has value `g⁻¹`. Inverting the zero value of the lifted
curve therefore produces a point of `C(k)` mapping to `g`.

`Dynamic.exists_lift_of_mem_unipotent` implements this argument.
`Dynamic.centralIsogenyLift` chooses such an actual rational lift, and
`Dynamic.centralIsogenyLift_comp` states its literal composite with `q`.
The choice is a point, with no claim that these choices form a group
homomorphism or are unique.

This unit derives its result from the Library's all-test commutator descent
and the relative proper extension helper. Its conclusion concerns the
identity field-valued test scheme only. It neither asserts general
rational-point surjectivity of central isogenies nor lifting on arbitrary
test schemes. For the affine Iwahori–Tits application, contraction inside
the actual derived group must still be established for the ambient root
points before applying this result to its simply connected cover.
