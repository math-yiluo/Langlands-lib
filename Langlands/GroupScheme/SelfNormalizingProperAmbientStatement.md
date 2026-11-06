# A proper ambient scheme for self-normalizing homogeneous spaces

`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement.{u}` concerns
every commutative ring `R : Type u`. Let `G` be an actual smooth affine group
scheme over `Spec R` with geometrically connected fibres, and let `i : H ⟶ G`
be a smooth closed subgroup with geometrically connected fibres. Assume the
all-test equality `(range i).normalizer = range i`. The assertion supplies an
actual scheme `Y` over `Spec R` and a morphism `r : G.X ⟶ Y` such that `Y`
is proper and locally of finite presentation over `Spec R`, and for every
`T : Over (Spec R)` and `g h : T ⟶ G.X`,

```
g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T.
```

Properness supplies quasi-compactness and separatedness, so the local finite
presentation condition makes `Y` a proper scheme of finite presentation.
The assertion retains all rings and every test scheme, including nonreduced
tests. The map into `Y` need not be surjective. Properness of a quotient is
not asserted, and no quotient or ambient representation is a premise.

The statement is derived from the finite-jet construction in the proof of
Brian Conrad, *Reductive group schemes* (2014), Theorem 2.3.6(1), printed and
one-based PDF pp.72–74, together with Proposition 2.1.6 and its proof,
pp.61–62. The registered source is
`conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
For smooth group fibres over a field, connectedness implies geometric
connectedness. The formulation with a proper ambient scheme is a consequence
of the source's construction over an affine base, rather than the literal
wording of Theorem 2.3.6(1).

The source first reduces to a Noetherian base. For sufficiently high finite
identity neighbourhoods `H_n ⊂ G_n`, the stabilizer `N_G(H_n)` equals `H`.
The coordinate modules of these neighbourhoods are finite locally free.
Conjugation therefore gives an orbit map from `G` to the Grassmannian of
quotients of the coordinate module of `G_n` with the rank of that of `H_n`.
The Grassmannian is proper of finite presentation, and the all-test stabilizer
is exactly `H`. Equality of orbit images gives the right-coset equivalence.
Over the affine Noetherian base, quasi-compactness makes the stabilization
index uniform; locally constant ranks have finitely many values and can be
handled on their clopen strata. Noetherian approximation over the original
affine base and base change then give the stated assertion for arbitrary
rings. Descent of the group and subgroup data, geometric connectedness,
self-normalization, the exact stabilizer and the ambient scheme properties
are all retained proof obligations. The Lie algebra alone is insufficient in
arbitrary characteristic.

This module defines a proposition only. The proper ambient scheme enables a
separate argument for properness of an embedded supplied quotient, but neither
that argument nor unconditional parabolic quotient existence is proved here.
