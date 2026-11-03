# Split torus quotients of solvable groups over algebraically closed fields

`Langlands.GroupScheme.SolvableTorusQuotientStatement.{u}` is a proposition
target. It has no proof in this module.

For an algebraically closed field `k : Type u` and a smooth connected affine
group scheme `H` over `Spec k`, assume `IsSolvableGroupScheme H`. The statement
asserts the existence of actual group schemes `U`, `D` and homomorphisms
`i : U ⟶ H`, `q : H ⟶ D` such that:

- `i` is a closed subgroup, and `U` is smooth, connected and unipotent;
- the subgroup-functor range of `i` is normal on every test scheme;
- `q` is a represented fppf quotient by that range;
- `D` is a split torus.

The exact existing predicate `RelativeRoot.IsFppfQuotient` means that the
underlying morphism of schemes of `q` is flat, surjective and locally of finite
presentation, and that the range of its actual group-scheme kernel equals the
range of `i` on every test scheme. In particular, it supplies the actual
projection map needed to compose a conjugation family with the torus quotient.
It does not assert surjectivity on the point group of every original test scheme.
`IsSplitTorus D` means that `D` is isomorphic as a group scheme to a finite
product of copies of the multiplicative group over `Spec k`.

The group schemes and quotient model are existentially quantified. The target
does not require a particular previously chosen representative of the
unipotent radical, its maximality among unipotent subgroups, a splitting
section, a finite additive-group series for `U`, or conjugacy of cocharacters.

## Source and correspondence

J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33(a), (c), printed
pp.335–336 (zero-based PDF pages 350–351), gives a normal unipotent subgroup
`H_u` of a smooth connected solvable algebraic group over a perfect field,
with `H_u` smooth and connected and quotient `H/H_u` a torus. An algebraically
closed field is perfect. The target keeps precisely these existence and
quotient clauses in the algebraically closed case. It omits part (b), the
uniqueness assertion of (c), and part (d).

Definition 12.14, printed p.236 (zero-based PDF page 251), identifies split
tori with smooth connected diagonalizable groups. Theorem 12.18(d), printed
pp.237–238 (zero-based PDF pages 252–253), makes every group of multiplicative
type diagonalizable over a separable closure. Hence the torus quotient in
Theorem 16.33 is split when the ground field is algebraically closed. This
splitting step is part of the future proof, rather than a premise on `H`.

Milne's algebraic groups have finite type. Here smoothness and affineness imply
finite type for `H`, and closedness makes `U` affine and of finite type. The
split-torus conclusion gives these properties for `D`. The Library predicate
`IsSolvableGroupScheme` tests solvability of the algebraic-closure point group.
For smooth connected groups over an algebraically closed field this agrees
with Milne's solvability by Proposition 16.34(c), (d), printed p.336 (zero-based
PDF page 351). Translating the source quotient to the actual represented
fppf quotient predicate, and identifying its kernel on every test scheme,
remain proof obligations.

The subgroup conditions use the Library's `IsClosedSubgroup`,
`SubgroupFunctor.range`, `SubgroupFunctor.IsNormal` and `IsUnipotent`
interfaces. Milne's subgroup and normality assertions are on points with
values in every algebra; their extension to every scheme test follows by
restriction to affine open covers.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

## Relation to existing targets

`SolvableUnipotentPartStatement` omits the quotient clauses of Theorem 16.33.
`UnipotentRadicalQuotientStatement` assumes a represented radical and asks for
a pseudo-reductive quotient over every field; it does not assert a torus
quotient for a solvable group. The present target supplies the missing
solvable torus-quotient existence needed by `CentralizerBorelIntersectionStatement`.
It does not prove that target.
