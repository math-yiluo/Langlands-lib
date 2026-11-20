# Uniform adic avatars of algebraic CM Hecke characters

`AlgebraicHeckeCharacterAvatarStatement` uses the existing
`Harris.IsAlgebraic` condition that the infinity type is integral. It
asserts one coefficient number field `L`, one embedding `ι : L →+* ℂ`,
one finite set `S` equal to the support of the finite conductor, and one
family of values `a v : Lˣ`. For every finite place `λ` of `L`, the avatar
is a continuous `LambdaAdicCharacter K L λ`, with the actual absolute
Galois group and actual coefficient completion. At every `v ∉ S`, the
value `a v` matches the Hecke character at an actual uniformizer. At
those places of different residue characteristic from `λ`, the avatar
kills actual inertia and sends every geometric Frobenius lift to the
image of `a v` in `L_λ`. The theorem
`IsUniformHeckeAvatar.isLambdaAdicRealization` gives the existing
realization predicate at each coefficient place with this same `S`.

`AlgebraicHeckeAvatarAssemblyStatement` exposes the four construction
inputs. Obtain the finite part and choose the local uniformizers once.
The value `a v` is the lifted finite part on the corresponding one-place
idele. For each `λ`, apply the finite lift and inverse limit with the
exceptional set enlarged by the finite set of places of `K` over the
rational prime of `λ`. That set is finite by finiteness of primes above a
nonzero rational prime. The corrected integral character agrees off
that rational prime with the embedded finite part, so it kills the local
integral units for `v ∉ S` there. This verifies the finite lifting input
at every congruence level. Finally compose the integral avatar with the
units inclusion into `L_λ` and use its geometric comparison at the
chosen uniformizer to obtain the common values.

## Sources and consumers

The construction follows Serre, *Abelian l-Adic Representations and
Elliptic Curves*, Chapter II §§2.3, 2.5 and 2.7, pp. II-10–II-12,
II-18–II-20 and II-23–II-24. The agreement with `IsLambdaAdicRealization`
fixes the convention that a uniformizer matches geometric Frobenius.
Clozel 1991 §5.3, pp. 143–144, uses a central correction that can have
nonzero weight. Task 7864 uses the avatar of this algebraic correction as
part of its coefficient-field and twist comparison. For the rank-one
unitary endpoint of Task 6698, the same avatar supplies the family and
Frobenius comparison. That endpoint also asks for weight-zero purity of
every conjugate of `a v`, a separate arithmetic assertion.

Serre source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
Clozel source ID `clozel-1991-selfdual-galois` (SHA-256
`9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`).
