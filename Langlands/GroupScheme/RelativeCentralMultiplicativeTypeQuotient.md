# Central multiplicative-type quotients over arbitrary bases

Worker 644 and Worker 587.

`relativeCentralMultiplicativeTypeQuotient.{u}` proves exactly the unchanged
Library proposition `RelativeCentralMultiplicativeTypeQuotientStatement.{u}`.
For every base scheme `S`, a smooth affine group scheme `G` over `S` with
connected geometric fibers, and a closed central inclusion `z : Z → G` with
`Z` of relative multiplicative type, it constructs a group scheme `Q` over
`S` and a homomorphism `q : G → Q`. The structure map of `Q` is affine and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q` holds: the actual
projection is flat, surjective and locally finitely presented, and the range
of its actual kernel inclusion equals the range of `z` on every relative
scheme test. The base may be non-affine, non-quasi-compact and non-Noetherian;
torsion characters and non-smooth or non-reduced kernels are allowed. Neither
an action nor a quotient is supplied as an assumption.

The implemented proof first proves `affineDiagonalizableModelQuotient`. Over
`Spec R` with a given closed normal inclusion `D_R(M) → G` and finitely
generated abelian character group `M`, it applies the explicit constructions
in `DiagonalizableFppfQuotient`: the quotient is the spectrum of the actual
degree-zero coordinate algebra, with its descended group structure. Closedness
of the actual translation graph gives strong grading; the strong-grading
tensor isomorphism gives the torsor relation and faithful flatness; the
relation gives the all-test coset criterion. Local finite presentation comes
from the integer model of `D_R(M)`, arbitrary base change and fpqc descent
through the relation square. The normal quotient construction identifies the
full actual kernel. No smoothness of either group is used for this direct
model.

The final theorem applies
`relativeCentralMultiplicativeTypeQuotient_of_affineDiagonalizableModel` to
that unconditional model proof. This transport first handles arbitrary affine
base schemes and isomorphic diagonalizable kernels. On an affine base, an
fppf splitting cover has a finite affine refinement, giving an affine fpqc
cover; effective affine descent then yields the quotient by a
multiplicative-type kernel. Over arbitrary bases the construction glues on
the affine open cover, with the common-kernel comparison providing the
compatible local identifications. Centrality supplies normality. This
reduction retains the full kernel on all tests and does not require the
smoothness or connectedness assumptions that are present in the target.

The proof route implements the quotient construction cited in Conrad,
*Reductive group schemes* (2014), proof of Lemma 3.3.2, p.98 (SGA 3, Exposé
VIII, Theorem 5.1 and Exposé IX, §2.3). The Lean theorem proves precisely the
Library statement; it makes no assertion of reductivity of `Q` or finite
presentation of `Q → S`.
