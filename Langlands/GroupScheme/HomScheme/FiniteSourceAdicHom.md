# Adic Hom comparison for a finite group source

`FiniteSourceAdicHomStatement.{u}` formalizes SGA 3, Exposé XV,
Proposition 1.6(a), Gille–Polo recomposition, PDF p. 4. Restriction from an
actual finite group scheme to its successive adic thickenings over a
complete noetherian local base gives a bijection between group
homomorphisms to an arbitrary target group scheme and compatible systems
of homomorphisms on those thickenings.

The proof identifies actual base changes of the finite source with the
spectra of quotients by powers of the extended maximal ideal. It applies
finite-algebra adic effectivity to lift the underlying scheme morphisms.
The structure map is detected on the thickenings, so this lift lives over
the base. Preservation of the unit and product is detected on the
thickenings of the base and the finite two-fold source, respectively.
Naturality of the monoidal comparison makes these equations the supplied
group homomorphism identities on each level. Uniqueness follows from
uniqueness of the underlying scheme map.

The maps on quotient spectra and their pullback property come from `AdicQuotientBaseChange`.
