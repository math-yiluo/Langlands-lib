# Finiteness of locally quasi-finite groups of multiplicative type

This derived internal contribution proves that a locally quasi-finite group
of multiplicative type is finite over an arbitrary scheme. Its supporting
construction gives an actual finite-character presentation of a diagonalizable
group over a nonempty base. All declarations are universe-polymorphic in `u`.
Finite groups here may be non-smooth, and the base need not be reduced,
Noetherian, connected, or quasi-compact.

## Constructions and hypotheses

`FiniteDiagonalizableModel H` consists of an abelian group `characters : Type u`,
proof that this group is finite, and an actual group-scheme isomorphism
`H ≅ diagonalizable S characters`. It describes the full group scheme over its
given base, including all test schemes and any infinitesimal structure.

`IsDiagonalizable.nonempty_finiteModel` proves existence of this data from
`IsDiagonalizable H`, local quasi-finiteness of `H.X.hom`, and nonemptiness of
`S`. `IsDiagonalizable.finiteModel` chooses such a presentation. Its result
retains the character group and actual isomorphism, so it can be used for
further split calculations. `FiniteDiagonalizableModel.isFinite` transports
finiteness from that finite-character split model to `H`.

`IsDiagonalizable.isFinite` removes the nonemptiness restriction, and
`IsMultiplicativeType.isFinite` proves the arbitrary-base result. The latter
uses exactly the published relative multiplicative-type definition: an fppf
cover on which the group becomes diagonalizable with finitely generated
abelian character groups. Local quasi-finiteness is a hypothesis on the
structure map of the actual group.

## Implemented proof

`finite_characters_of_isFinite` works over any nonzero commutative ring `R`.
The coordinate algebra of `Diagonalizable.groupScheme R Λ` is the full
additive group algebra `AddMonoidAlgebra R Λ`. Finiteness of its spectrum map
means that this algebra is a finite `R`-module, using `IsFinite.SpecMap_iff`
and `RingHom.finite_algebraMap`. The standard group-algebra basis
`AddMonoidAlgebra.basis Λ R` and `Module.Finite.finite_basis` then give
`Finite Λ`.

For `finite_characters_of_locallyQuasiFinite`, choose a point of the nonempty
base and pass to its residue field. The actual diagonalizable base-change
isomorphisms identify this fibre with the diagonalizable group over that
field and preserve the same full character group. Local quasi-finiteness is
stable under base change and isomorphism. The fibre is affine, hence
quasi-compact, and its target is Artinian. Mathlib's
`IsFinite.of_locallyQuasiFinite` therefore makes the fibre finite. The preceding
basis argument makes `Λ` finite.

Conversely, `isFinite_diagonalizable` pulls back the existing
`Diagonalizable.isFinite` instance for a finite character group from
`Spec (ULift ℤ)` to the given scheme. The finite-model construction first
transports local quasi-finiteness along its supplied diagonalizable
isomorphism and then applies the residue-field calculation.

For an empty base, the target-local criterion
`IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict` has no points to
check. This proves the empty case without imposing a finite character group
on an arbitrary presentation over the empty scheme.

Finally, unpack the fppf splitting cover in `IsMultiplicativeType H`.
Local quasi-finiteness passes to every member of that cover, where the
diagonalizable result proves finiteness. The published fpqc descent instance
for finite morphisms, the fpqc-to-fppf descent instance, and
`FppfLocal.isLocalAtTarget_fppfPrecoverage` descend this finiteness to `S`.

## Provenance and use in the central-isogeny problem

This is a derived construction from the published Library definitions and
base-change isomorphisms, Mathlib's standard basis and Artinian-base theorem,
and the Library's fpqc descent proof. It is not presented as a new
source-level definition or a transcription of a literature proof.

For the fibrewise central-isogeny criterion, this result supplies global
finiteness once the actual kernel is proved to be of multiplicative type
and locally quasi-finite. It neither proves that kernel to be of
multiplicative type nor proves global centrality. Those structural
obligations and the exact whole-task criterion remain open.
