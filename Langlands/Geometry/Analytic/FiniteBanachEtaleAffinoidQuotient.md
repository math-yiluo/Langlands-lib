# Affinoid realizations of finite étale relation quotients

`finiteEtaleAffinoidQuotientOfFiniteBanach` takes a finite Banach,
algebraically finite étale bounded map `f : A → B` of presented
affinoid algebras over a complete ultrametric normed field. The two
algebraically finite étale bounded relation maps `B ⇉ C` agree on
`A`, their images generate `C` as a ring, and they induce an
equivalence relation on maps out of `B` to every test ring in the
universe of the affinoid algebras. The construction returns a
`FiniteBanachEtaleAffinoidQuotient` together with finite Banach witnesses
for its two maps. The field may have trivial norm.

The two `A`-algebra maps have an equalizer `D` finite étale over `A`
by `equalizerAlgebraFiniteEtale`. The equalizer inherits its norm
from `B` and is closed by continuity of the two maps. The finite étale
relation maps are finite projective over `B` because `B` is Noetherian.
Applying `invariantRingQuotient` to `D → B` gives projectivity and
faithful flatness of `B` over `D` and the pushout square of ordinary
commutative rings with corner `D` and relation maps `B ⇉ C`.

Before choosing an affinoid presentation of `D`, apply
`BoundedAlgHom.IsFiniteBanach.of_faithfullyFlat_comp_of_projective`
to `A → D → B`. The `D`-linear retraction it uses sends a
generating tuple for `A → B` to one for `A → D`. The coefficient
bound uses the bounded inclusion `D → B`. The resulting finite
Banach map `A → D` and the inherited bound on `‖1‖` allow
`FiniteBanachPresentation.exists_presentation` to realize `D` by
a presented affinoid algebra `P` with a bounded equivalence `P ≃ D`.

The maps `A → P → B` factor `f`. Bounded transport along the
equivalence gives finite Banach structure on `A → P`, and cancellation
from `f` gives it on `P → B`. The ring isomorphism from `P` to `D`
transports the pushout by `IsPushout.of_iso'` and the faithful flatness
by composition. Unramifiedness of `P → B` follows from that of `A → B`.
Finiteness over the Noetherian affinoid algebra `P` gives finite
presentation, and hence the cover is algebraically finite étale.
`coverMap_spectrum_surjective_of_isFiniteBanach` applies bounded lying
over to the injective finite Banach cover.

Over a nontrivially normed field, `finiteBanachEtaleAffinoidQuotientOfFiniteness` obtains
finite Banach structure on `f` from algebraic finiteness using the
open mapping theorem. The separate lemmas on finiteness and spectrum
surjectivity of its quotient maps also use that implication.

This is a derived affinoid realization of the algebraic equalizer and
invariant-ring results. The construction combines the ring pushout
with the finite Banach affinoid presentation theorem. The quotient
record concerns the resulting algebras and maps.
