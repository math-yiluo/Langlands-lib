# Universal commutator families beginning with a pointed morphism

Author: Worker 1431.

This is an internal reduction toward the reverse implication of
`UnipotentWoundCriterionStatement`, motivated by the commutator reduction in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition B.3.2, printed pp.572–573, one-based PDF pp.598–599. The source is
registered as `conrad-gabber-prasad-2015-pseudo-reductive`. Its Appendix B
assumes positive characteristic. The elementary construction here works over
every field because its hypotheses supply the required uniform nilpotence.

Starting with an actual morphism `f : V ⟶ G.X`, `source G V n` adjoins `n`
copies of the ambient group to the source. The morphism `word f n` brackets
`f` successively with these universal parameters. No choice of rational group
points or density assumption is used. On every relative scheme test the word
lies in the corresponding abstract lower central term. Therefore uniform
nilpotence kills the family at a finite index. If `f` is nontrivial, the least
vanishing index has a nontrivial predecessor. The vanishing next word says
exactly that this predecessor's entire image belongs to the all-test,
all-refinement centre.

When `f` sends a supplied rational basepoint to the identity, each word has a
rational basepoint with identity value. More strongly, `basepointSection`
sets only the initial variable to its basepoint and retains all the group
parameters; its composite with each word is identically the identity.

`exists_central_generatedImage` assumes a smooth connected affine ambient
group over a field and an affine geometrically integral source locally of
finite type, expressed by `ImageGeneration.FinitePowerGood`. The sources keep
these geometric properties by the published smooth connected geometry and
finite-product lemmas. Pointed image generation constructs a
`GeneratedImage` of the last nontrivial word. Closed-envelope minimality puts
its inclusion in the centre. The word factors through that inclusion, so its
nontriviality also proves that the generated subgroup is nontrivial. The
result includes smoothness, affineness, geometric connectedness and
connectedness. `GeneratedImage` itself contains the closed subgroup inclusion
and its factorization. Cancellation against that inclusion proves that the
factor retains the whole basepoint-section identity.

`exists_central_generatedImage_of_not_hasConstantAffineLineMaps` specializes
this construction to a smooth connected affine unipotent actual group over
any field. Failure of affine-line constancy gives a morphism whose normalized
difference is nontrivial. The affine line supplies the required geometric
properties, and the published unipotent all-test nilpotence theorem supplies
the bound. The output retains this original morphism and a nontrivial central
word family whose factor is the identity on the entire zero section.

This reduction retains a family with group parameters, rather than producing
a central nonconstant ground-field affine-line map. It does not construct a
vector subgroup, prove separable invariance of woundness, or establish the
full criterion. Those additional structural steps remain necessary.
