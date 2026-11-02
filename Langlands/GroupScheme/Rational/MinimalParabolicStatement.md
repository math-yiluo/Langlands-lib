# Statements on minimal rational parabolic subgroups

Author: Worker 1262.

This module states three structural results for actual connected reductive
group schemes over an arbitrary field `k : Type u`. They are proposition
definitions, with no proofs supplied. No splitness, perfectness, characteristic,
or cardinality restriction is imposed on the ground field.

The original source is Borel and Tits, *Groupes réductifs* (1965), source ID
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The relevant passages are 4.13(b), printed p.90 (PDF p.37), 4.15 and 4.16,
printed pp.90–92 (PDF pp.37–39).

`GenericMinimalParabolicStatement` says that if `i : T.toGrp ⟶ G` is a
maximal split torus and `ν` is generic for its actual relative roots, then
`Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)` is a minimal rational
parabolic functor. In particular, the conclusion includes representability
by a geometric parabolic subgroup, through `IsMinimalParabolicFunctor`.
It also compares every smaller parabolic on every test scheme. This is the
derived dynamic formulation of 4.15(a) and the minimality characterization
4.16: genericity selects a positive system of relative roots for the maximal
split torus. Identifying that root-theoretic parabolic with the published
dynamic functor is a proof obligation, not a hypothesis or a definition in
this module. The affine instance used to define genericity comes from the
connected reductive hypothesis.

`MinimalParabolicConjugacyStatement` is 4.13(b) in the published subgroup
scheme language. For any actual minimal parabolics `j : P ⟶ G` and
`j' : P' ⟶ G`, it asks for `g : G(k)` and an actual group scheme isomorphism
`e : P ≅ P'` such that
`j ≫ (G.innerIso g).hom = e.hom ≫ j'`. Thus conjugacy holds as subgroup
schemes, including all test points. The source treats finite fields
separately in its proof; the statement here includes them.

`ParabolicContainsMinimalStatement` asks for an actual minimal parabolic
`j' : Q ⟶ G` whose all-test range is contained in that of any given
parabolic `j : P ⟶ G`. This is the existence step used explicitly at the
start of the implication (iv) to (i) in the proof of 4.16, and in the
reduction to minimal parabolics in 4.18. Its provenance is derived: the
source uses this minimal-element consequence of the finite-dimensional
parabolic structure without isolating it as a numbered theorem. Proving
this existence step in the actual group scheme API remains required.

The minimality predicates are imported from `Rational.MinimalParabolic`;
the relative roots, genericity, and dynamic functor are the constructions
already used by `RationalBruhatStatement`. No rational-point inclusion
criterion replaces the existing all-test subgroup order.
