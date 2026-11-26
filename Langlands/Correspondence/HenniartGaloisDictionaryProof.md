# The finite-image Weil–Galois orbit dictionary: proof

The module `Langlands.Correspondence.HenniartGaloisDictionaryProof` proves
`Langlands.Henniart.WeilGaloisDictionaryStatement`
([statement and conventions](HenniartGaloisDictionaryStatement.md)) as
`Langlands.Henniart.weilGaloisDictionary`, with three independent universe
parameters `uK`, `uΩ`, `uW` and no hypothesis on the characteristic of the local
field. It proves each conjunct separately:

| Conjunct | Theorem |
| --- | --- |
| `WeilGaloisTypeTwistStatement` | `weilGaloisTypeTwist` |
| `GaloisPullbackBijectionStatement` | `galoisPullbackBijection` |
| `GaloisPullbackTwistStatement` | `galoisPullbackTwist` |
| `WeilGaloisOrbitDictionaryStatement` | `weilGaloisOrbitDictionary` |

Throughout, `K` is a nonarchimedean local field, `Ω` a separable closure,
`G_K = Ω ≃ₐ[K] Ω` and `W_K = localWeilGroup K Ω`. Each final theorem introduces
`K` and `Ω` and supplies the instance `IsSepClosed Ω` as
`IsSepClosure.sep_closed K`, the same proof the statement uses. The class-level
work is in [HenniartGaloisPullback.md](HenniartGaloisPullback.md), whose relation
`IsGaloisPullbackBasis K Ω ⟨k+1, σ⟩ ⟨k+1, ρ⟩` is definitionally
`IsGaloisPullback K Ω σ ρ`; the general-field topology of `W_K` is in
[SepClosedTopology.md](../Weil/Local/SepClosedTopology.md).

## Twist invariance of the Weil invariants

These lemmas are in `Langlands.Henniart.LocalNumerical` and are public.

- `weilUnramifiedTwist_comm`, `weilUnramifiedTwist_inv_apply`: unramified
  twists of Weil classes commute, and the twist by `z⁻¹` inverts the twist by
  `z` (the published composition law
  `FiniteRepresentation.continuousIrreducibleTwistEquiv_mul` and the
  multiplicativity of `Weil.Local.unramifiedCharacterHom`).
- `weilTorsionNumber_weilUnramifiedTwist`: the torsion number is unchanged by an
  unramified twist. Since twists commute and are injective, `y` fixes the twist of
  `σ` by `z` exactly when `y` fixes `σ`, so the two stabilizers are the same set.
- `HasArtinConductor.weilUnramifiedTwist`,
  `hasArtinConductor_weilUnramifiedTwist_iff`,
  `hasWeilSwan_weilUnramifiedTwist_iff`: the Artin exponents, hence the Swan
  exponents, of a Weil class are those of its unramified twists. If `A` represents
  `σ` with a finite inertia presentation `P`, then the twist of `A` by
  `localUnramifiedCharacter K Ω z` represents the twisted class
  (`forget_continuousIrreducibleTwistEquiv`). The twisting character is trivial on
  degree zero, so the twisted representation restricts to the same
  representation `localInertiaRepresentation` of Weil inertia. The same finite
  Galois subextension therefore presents the twist, and the Artin expression
  `Ramification.Local.artinConductorOfQuotient` of a presentation depends only on
  that inertia representation, so the exponent is unchanged. The converse uses
  the twist by `z⁻¹`.

## The four conjuncts

- `weilGaloisTypeTwist` (Henniart 1980, §2.3, Corollary 3): for a rank-`k+1`
  Weil class, `exists_twist_isGaloisPullbackBasis` gives `z` and a Galois class
  whose pullback is the twist by `z`; the Galois class has rank `k+1` by
  `IsGaloisPullbackBasis.fst_eq`, which compares the ranks of the two underlying
  classes (restriction does not change the rank).
- `galoisPullbackBijection` (Henniart 1980, §2.1): existence of the pullback is
  `exists_isGaloisPullbackBasis`, uniqueness is
  `IsGaloisPullbackBasis.weil_unique`, and a Weil class determines the Galois
  class by `IsGaloisPullbackBasis.galois_unique`. `irreducibleBasis_mk_injective`
  passes between rank-tagged and rank-`k+1` classes.
- `galoisPullbackTwist` (Henniart 1988, Proposition 2.2(a) and §4.2). If
  `σ' = σ ⊗ z`, `IsGaloisPullbackBasis.exists_galoisUnramified_of_twist` gives a
  character in `galoisUnramifiedCharacters K Ω` carrying `ρ` to `ρ'`. If
  `ρ' = ρ ⊗ χ`, then `IsGaloisPullbackBasis.twist` shows that `σ ⊗ z`, with `z`
  the value of `χ` at the projected geometric Frobenius, is a pullback of `ρ'`,
  so it is `σ'` by uniqueness. The equality of torsion numbers is
  `weilTorsionNumber_eq_galoisTorsionNumber`: sending a Galois self-twist `χ` to
  `z = χ(proj Frob)` maps the Galois stabilizer of `ρ` to the Weil stabilizer of
  `σ` (by `IsGaloisPullbackBasis.twist` and uniqueness of pullbacks). It is
  injective because `χ ∘ proj` is the unramified character with parameter `z`
  (`galoisUnramifiedCharacter_comp_localProjection`) and two continuous characters
  agreeing on the dense image of the projection are equal
  (`DenseRange.equalizer`). It is surjective by
  `IsGaloisPullbackBasis.exists_galoisUnramified_of_twist` applied with `σ' = σ`.
  `Nat.card_congr` then gives the equality.
- `weilGaloisOrbitDictionary`. The equivalence is `weilGaloisOrbitEquiv K Ω`.
  Its forward map sends the Weil orbit of `b` to `galoisOrbitOfWeil K Ω b`, the
  Galois orbit of the Galois class of a chosen Galois-type twist of `b`. This
  does not depend on the twist or on the representative of the orbit
  (`galoisUnramifiedOrbitClass_eq_of_twist`): two Galois-type twists of classes in
  one Weil orbit differ by an unramified twist, so their Galois classes differ by
  an unramified Galois character. The inverse sends the Galois orbit of `c` to the
  Weil orbit of its pullback (`weilOrbitOfGalois K Ω`), independent of the
  representative by `IsGaloisPullbackBasis.twist`. The two composites are the
  identity because the Galois-type twist of `b` is the pullback of its Galois class
  and lies in the orbit of `b`, and the pullback of `c` is a Galois-type twist of
  itself with parameter `1`. Orbit equality is described by
  `Weil.unramifiedOrbitClass_eq_iff` on the Weil side and by
  `galoisUnramifiedOrbitClass_eq_iff` on the Galois side. The value on pullback
  pairs is `weilGaloisOrbitEquiv_apply`. For the strata,
  `weilGaloisOrbitEquiv_image_weilRefinedStratum` shows both inclusions: a Weil
  orbit containing `σ` with Swan exponent `s` and torsion number `f` is sent to the
  orbit of the Galois class `ρ` of a Galois-type twist `σ ⊗ z`; the twist has
  Swan exponent `s` and torsion number `f` by the twist-invariance lemmas, so `ρ`
  has Swan exponent `s` (through its pullback `σ ⊗ z`, as `HasGaloisSwan`
  requires) and torsion number `f`. Conversely, a Galois orbit in
  `galoisRefinedStratum K Ω k s f` is the image of the Weil orbit of the pullback
  witnessing `HasGaloisSwan`, whose torsion number equals that of `ρ`.

`weilGaloisDictionary` is the conjunction of the four theorems. The proofs use no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Route

The proof follows Henniart's arguments, with two changes of route. Finite order
of the twisting parameter in `galoisPullbackTwist` comes from the trivial action
of a power of Frobenius on both Galois representations, not from determinants.
The extension of a finite-order unramified character to `G_K` is obtained from
the published finite-image extension theorem in rank one, not from the
profinite completion of `ℤ`. Neither argument depends on the characteristic.

## Sources

- Guy Henniart, *Représentations du groupe de Weil d'un corps local*,
  L'Enseignement Math. 26 (1980), registered as
  `henniart-1980-weil-representations`: §2.1 and §2.3, Corollary 3, printed
  p. 158.
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS 21 (1988), registered as `henniart-1988-numerical`: §2.2 and
  Proposition 2.2(a), printed pp. 503–504; §4.2, printed p. 510.
