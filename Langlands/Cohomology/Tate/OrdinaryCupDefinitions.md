# The ordinary cup on actual group cohomology

This module constructs `Langlands.Tate.ordinaryCup` from the explicit
inhomogeneous cochain cup and its proved differential Leibniz identity.
The coefficient ring `R`, group `G`, and representations `A`, `B`, `C`
share an arbitrary universe `u`. The assumptions are `CommRing R`,
`Group G`, and an equivariant bilinear `φ : Pairing A B C`.
There is no finiteness or flatness assumption.

## Construction and representative

`ordinaryCupCocycles φ p q` restricts `ordinaryCochainCup φ p q` to
Mathlib's actual cocycle modules. It uses `OrdinaryCup.onCocycles`;
the required cycle-preservation proof is supplied by
`OrdinaryCup.cycles_of_leibniz` applied to `ordinaryCochainCup_d φ`.
Thus cycle preservation is discharged by a proved identity.

`i_ordinaryCupCocycles` identifies the underlying cochain with the
cochain cup of the two included cocycles. The pointwise certificate
`ordinaryCupCocycles_apply` states, for `x : Fin (p + q) → G`,

```text
iCocycles C (p + q) (ordinaryCupCocycles φ p q a b) x =
  φ.bilinear (iCocycles A p a (fun i => x (Fin.castAdd q i)))
    (B.ρ ((List.ofFn (fun i : Fin p => x (Fin.castAdd q i))).prod)
      (iCocycles B q b (fun j => x (Fin.natAdd p j)))).
```

The front `p` entries go to the first cocycle; the last `q` entries go
to the second. The product of the front entries, in increasing order,
acts on the second value. In degree `p = 0` this product is `1`.
The inclusion certificate follows from `OrdinaryCup.i_onCocycles`;
the tuple formula then follows from `ordinaryCochainCup_apply`.

For all natural degrees `p`, `q`, the operation is an actual bilinear map

```text
ordinaryCup φ p q :
  groupCohomology A p →ₗ[R] groupCohomology B q →ₗ[R]
    groupCohomology C (p + q).
```

Its definition specializes `OrdinaryCup.fromLeibniz` to
`ordinaryCochainCup φ` and `ordinaryCochainCup_d φ`. That helper derives
actual boundary witnesses in each variable from the signed Leibniz
identity and descends through the two actual homology cokernels. In
positive degrees, the left witness is the cup with a primitive, and
the right witness is `(-1 : R)^p` times the cup with a primitive.
The degree-zero incoming differential is zero. No cycle-preservation,
boundary-vanishing, or Leibniz hypothesis remains as an input to
`ordinaryCup`.

`ordinaryCup_π_π` is the construction certificate

```text
ordinaryCup φ p q (π A p a) (π B q b) =
  π C (p + q) (ordinaryCupCocycles φ p q a b).
```

It is the specialization of `OrdinaryCup.fromLeibniz_π_π`.
Together with `ordinaryCupCocycles_apply`, it identifies the product
class with the displayed inhomogeneous representative.

## Provenance and scope

This module is an internal specialization of the cochain construction
in `OrdinaryCochainCup` and the homology descent in `OrdinaryCupLeibniz`
and `OrdinaryCupDescent`. The new proofs apply the corresponding
construction certificates; they introduce no additional literature
claim.

The source conventions were checked in Serre, *Local Fields* (1979),
VII §3, pp. 112–113 (PDF pp. 118–119), for the inhomogeneous
differential, and VIII §3, pp. 131–132 (PDF pp. 137–138), for equivariant
pairings. Cartan–Eilenberg, *Homological Algebra* (1956), XII §4,
p. 242 (PDF p. 264), gives the signed cochain Leibniz rule and its
descent convention. That chapter's finite-group complete-resolution
context is not used as an assumption here: the imported cochain
identity is proved directly for an arbitrary group.

The construction concerns ordinary cohomology in nonnegative degrees.
The comparison with the dimension-shifted Tate cup and later
compatibility laws belong to separate tasks.
