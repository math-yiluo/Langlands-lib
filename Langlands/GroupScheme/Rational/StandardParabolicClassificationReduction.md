# Conditional assembly of standard-parabolic classification

This is derived infrastructure for
`StandardParabolicClassificationStatement`. It supplies the uniqueness
bookkeeping and conditional assembly of the exact local conclusion. It does
not prove the global statement or any structural input.

`SubgroupFunctor.existsUnique_conjugacy_index_of_rigidity` works over an
arbitrary scheme with an arbitrary family of subgroup functors. Assume that
the family is injective and that two rationally conjugate members of the
family are equal. If a subgroup functor is rationally conjugate to some member,
the index of such a member is unique. For two witnesses, symmetry and
transitivity of rational conjugacy make the representatives conjugate.
Rigidity makes them equal; injectivity makes their indices equal.

`standardParabolicClassification_of_local_inputs` specializes to the actual
standard subgroup functors over an arbitrary field. Its four explicit inputs
are:

- Every dynamic parabolic containing the fixed dynamic parabolic
  `P(groupHom ν ≫ i)` is a standard functor.
- Every dynamic parabolic can be rationally conjugated to one containing that
  fixed functor.
- The standard-functor family on subsets of `simpleRelativeRoots i ν` is
  injective.
- Rationally conjugate standard functors are equal on every test scheme.

For a cocharacter `zeta`, movement supplies `g`, and standardness identifies
`P(zeta ≫ Int(g))` with a standard functor. Published dynamic functoriality
then gives exactly
`P(zeta) = (standardParabolic i ν J).comap (G.innerIso g).hom`.
The abstract lemma proves uniqueness of `J`. The first input supplies the
other clause unchanged. Thus the conclusion has exactly the local two-clause
formula in the published target, with the same direction of `comap`.

`standardParabolicConjugacyIndex` uses classical indefinite description to
choose an actual subset of the simple roots, bundled with its rational
conjugacy witness and uniqueness certificate. It retains explicit injectivity,
rigidity, and representative-existence premises. It does not choose a unique
conjugating point.

The only ambient assumption in the standard-functor specialization is
`IsAffineHom G.X.hom`, needed to define the published relative roots.
Reductivity, maximal splitness, and genericity are not inferred here; they
belong to future proofs of the explicit structural inputs. No root
nonemptiness, properness, characteristic, perfectness, or splitness restriction
is introduced. Empty simple-root sets and improper parabolics are included
whenever the inputs hold.

The proof is an internal derivation from the published rational-conjugacy
equivalence laws and dynamic isomorphism functoriality, so it makes no external
literature claim. In particular, injectivity alone does not provide conjugacy
rigidity. The four structural inputs remain separate obligations for the
unconditional classification theorem.
