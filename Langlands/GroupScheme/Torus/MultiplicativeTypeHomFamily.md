# Rigidity of multiplicative-type families over a connected algebraic group

Workers 798, 329 and 3502.

`HomFamily.ofMorphism ψ T g q` evaluates a morphism `ψ : G × Q → N` at
the pair of points `(g,q)`. This construction is defined over an arbitrary
base scheme. `isHomFamily_ofMorphism` proves that multiplicativity in `q`
on all tests makes this a natural homomorphism family.

`HomFamily.eq_one_of_multiplicativeType` derives rigidity for families of
homomorphisms from a group `Q` of multiplicative type to a possibly different
group `N` of multiplicative type, parametrized by a connected algebraic group
`G`. It assumes the published proposition `DiagonalizableRigidityStatement`
as an explicit hypothesis. It does not supply a proof of that proposition.

The actor `G` is a group scheme of finite type over an arbitrary field `k`
with connected underlying space. The family `F T g q` is defined on every
scheme test `T` and is multiplicative in `q` and natural in `T`, exactly as
specified by `HomFamily.IsHomFamily`. The conclusion is
`F T g q = F T 1 q`. No action or homomorphism law in `g` is assumed.

The proof uses `IsMultiplicativeType.exists_common_splitting` to choose one
field extension splitting both `Q` and `N`. It then applies
`HomFamily.eq_one_of_commonSplitting` from
[HomFamilyFieldRigidity](HomFamilyFieldRigidity.md). That result applies the
supplied diagonalizable rigidity over the extension field and reflects the
equality through the flat surjective projection of each pulled-back scheme
test. Geometric connectedness of the parameter is supplied by the published
finite-type connected-group theorem. This preserves nonsmooth source and
target groups and allows a nonaffine parameter group.

`lift_eq_one_of_multiplicativeType` gives the same result for a scheme morphism
`ψ : G × Q → N` which is multiplicative in `Q` on all scheme tests. Its natural
family is `F T g q := lift g q ≫ ψ`; naturality is composition with the pair
of points. The identity test point `1 : T → G` is the constant family of the
identity section of `G`.

These are derived consequences of the supplied rigidity proposition and the
cited Library constructions. The original source for diagonalizable rigidity
is Milne, *Algebraic Groups* (2017), Theorem 12.36, printed p.243, as recorded
in [DiagonalizableRigidityStatement](DiagonalizableRigidityStatement.md).
Worker 3502 supplied the common-splitting module; Worker 329 supplied the
action descent argument generalized in the family support module.
