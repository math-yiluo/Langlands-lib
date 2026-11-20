# Finite geometrically normalized idele-character lifts

`FiniteGeometricArtinLifting` gives a unique continuous character of the
actual absolute Galois group with values in the same finite discrete
abelian coefficient group as the given idele-class character `ξ`. The
finite set `S` contains every place where `ξ` is nontrivial on integral local
units. At every `v ∉ S`, `MatchesGeometricArtinOutside` asks for triviality
on actual inertia and matching of every geometric lift with every actual
uniformizer. The Galois restriction is the one in
`LambdaAdicCharacter.atFinitePlace`.

`FiniteHeckeAvatarLiftStatement` explicitly assumes clause 3 of the
published `FiniteAbelianClassFieldStatement`, the local-unit ramification
criterion, and the restriction comparison for actual finite abelian
subfields. A continuous homomorphism to a finite discrete group has an open
kernel of finite index. Clause 3 already supplies a continuous surjective
arithmetically normalized Artin map `ρ` with precisely this kernel. Thus
`ξ = θ ∘ ρ` for a homomorphism `θ` from the finite Galois group to the
coefficient group. Take the lift to be `g ↦ θ((g|E)⁻¹)`. At every good
place, `ρ` kills local integral units because `ξ` does. The criterion
makes the extension unramified there, and the finite restriction comparison
kills actual inertia and identifies `g⁻¹|E` with `ρ(π)`. Hence the lift
of geometric Frobenius has value `ξ(π)`.

The existence part consumes neither a separate choice of Artin map from
clause 1 nor the finite-index, kernel-rigidity or complex finite-order
character clauses. For uniqueness, the two competing finite-valued
characters factor together through the finite abelian subfield fixed by
their common open normal kernel. Apply the published
`chebotarevPrimeRealizationStatement` to the inverse of each finite Galois
group element. Choose a uniformizer and a geometric lift at the resulting
unramified prime outside `S`. The finite restriction comparison and
uniqueness of arithmetic Frobenius identify the image of that lift with
the chosen element. The two characters therefore coincide. This argument
provides uniqueness for the finite reductions of the avatar and is also
valid after changing the finite coefficient group by a homomorphism.

## Source and provenance

Serre, *Abelian l-Adic Representations and Elliptic Curves*, Chapter II
§2.3, pp. II-11–II-12, obtains the Galois character from the idelic
correction and computes its unramified Frobenius value and inertia action.
Milne, *Class Field Theory*, v4.03, Chapter V §5, pp. 178–181, supplies the
finite local-global Artin comparison and the prescribed-kernel theorem.
The finite quotient decomposition and the finite Galois uniqueness argument
form a derived route to the same comparison with geometric normalization.

Serre source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
Milne source ID `milne-2020-class-field-theory` (SHA-256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`).
