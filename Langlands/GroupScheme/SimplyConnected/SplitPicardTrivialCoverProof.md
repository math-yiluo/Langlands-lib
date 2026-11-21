# A Picard-trivial central cover of a split semisimple group

`Langlands.GroupScheme.splitSemisimplePicardTrivialCover` proves the unchanged
Library proposition `Langlands.GroupScheme.SplitSemisimplePicardTrivialCoverStatement.{u}`.
For every field `k : Type u` and semisimple group scheme `G` over `Spec k` with
a split maximal torus, there is a central isogeny `π : C ⟶ G` from a
semisimple group scheme `C` such that every line bundle on `C.X.left` is
isomorphic to `LineBundle.trivial C.X.left`. There is no restriction on the
characteristic or perfectness of `k`, or on smoothness of the kernel.

This is the split semisimple case of Iversen's theorem, as stated in Milne,
*Algebraic Groups* (2017), Proposition 18.22, printed pp. 392–393 (PDF pp. 408–409).
The [statement's documentation](SplitPicardInputsStatement.md) compares the scope
and conventions with the original.

## Implemented proof

The proof applies `splitSemisimplePicardTrivialCover_of_factorial` to the
published theorem `splitSimplyConnectedFactorial`. The latter establishes that
the coordinate ring of a simply connected group with a split maximal torus is a
unique factorization domain, using the big cell and rank-one translates
([factoriality proof](SplitFactorialProof.md)). This route does not appeal to
Milne's character–Picard sequence or to the Picard-trivial cover theorem.

The [reduction](SplitPicardTrivialCoverReduction.md) takes the simply connected
central cover `π : C ⟶ G` and lifts the given split maximal torus to `C`.
Factoriality makes the Picard group of `Γ(C.X.left, ⊤)` trivial. Affineness
then gives an isomorphism from each actual line bundle on `C.X.left` to its
trivial line bundle, via `C.X.left ≅ Spec Γ(C.X.left, ⊤)` and pullback. The
existential witness is simply connected, although the target only requires it
to be semisimple.
