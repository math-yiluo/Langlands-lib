# Concrete supercuspidal class inclusion and relations

Author: Worker 7. This module places the published supercuspidal class space
inside the automorphic class space of `AutomorphicRelations`, and restricts the
automorphic relations to it. It is the automorphic domain of the
supercuspidal part of the local Langlands correspondence. It states no part of
LLC.

## Class space and inclusion

`SupercuspidalAutomorphicClass F n` is the published
`PadicField.SupercuspidalClass F n` at positive rank `n : ℕ+`. Its members are
isomorphism classes of irreducible admissible smooth complex representations
of `GL_n(F)` whose Jacquet coinvariants vanish for every proper block
parabolic subgroup and every conjugate of its unipotent radical. The field
and carrier universes stay independent. The upstream class constructor has
universe order `{uV, uF}`; the alias here exposes `{uF, uV}`, as
`AutomorphicClass` does. No finite-dimensionality, genericity or unitarity is
imposed.

`supercuspidalToAutomorphic` is the published forgetful map
`SupercuspidalClass.toSmoothDualClass` into the full class space, and
`supercuspidalToAutomorphic_injective` is its published injectivity theorem.
`IsSupercuspidalClass F π` means that `π` is in the image.
`isSupercuspidalClass_iff_existsUnique` says that a class in the image has
exactly one preimage; it does not say that every class is supercuspidal.

## Restricted relations

`SupercuspidalCentralActsBy`, `IsSupercuspidalCharacterTwist`,
`IsSupercuspidalSmoothDual` and `IsSupercuspidalRankOneCharacter` apply the
corresponding `AutomorphicRelations` predicate to the images of supercuspidal
classes. The operations are therefore the same as on the full class space.
The relations do not claim that a twist or smooth dual of a supercuspidal
class is supercuspidal. When the correspondence uses them, the existence of
an output is asserted explicitly in its statements.

`isSupercuspidalCharacterTwist_iff_eq_twist` connects the twist relation with
the published class map `SupercuspidalClass.twist` of
`Langlands.Representation.Classification.SupercuspidalTwist`, when the kernel
of `χ ∘ det` is open. Then `IsSupercuspidalCharacterTwist F χ π π'` holds
exactly when `π'` is the published twist of `π`. The determinant-kernel
hypothesis of that map is supplied by the published
`ker_determinant_le_ker_comp`. The proof combines the automorphic statement
`isCharacterTwist_iff_eq_twist`, the published compatibility
`toSmoothDualClass_twist` and injectivity of the inclusion. The open-kernel
hypothesis is the published adapter's own hypothesis; this module does not
prove it for every continuous `χ`. This module makes no statement about smooth
duals of supercuspidal classes, and it does not import the contragredient
results. That closure is the separate published statement
`Langlands.GeneralLinear.SupercuspidalContragredientStatement` of the
classification branch. It is proved by the published theorem
`Langlands.GeneralLinear.supercuspidalContragredient`
(`Representation/Classification/SupercuspidalContragredientProof`): the smooth
contragredient of a smooth representation is supercuspidal exactly when the
representation is, and, for admissible representations, irreducible exactly when
the representation is. With that theorem as its argument, the published
`Langlands.PadicField.SupercuspidalClass.contragredient` of
`Representation/Classification/SupercuspidalContragredient` is an involution of
`PadicField.SupercuspidalClass F n hn`; at `hn = n.pos` this is the class space
`SupercuspidalAutomorphicClass F n` used here. This module
does not prove an analogue of `isSupercuspidalCharacterTwist_iff_eq_twist`
relating `IsSupercuspidalSmoothDual` to that map.

## Sources and provenance

Henniart 2000, section 1.1, printed p.439 (PDF p.1), introduces the set
`A_F^0(n)` of isomorphism classes of smooth irreducible supercuspidal
representations of `GL_n(F)`. Section 1.2(1)–(3), printed p.440 (PDF p.2),
uses the central quasi-character, the twist by `χ ∘ det` and the
contragredient on these classes, and section 1.3, printed p.440, treats rank
one. Henniart 2002, section 1.1, printed p.588 (PDF p.2), defines the full
class set `A(n)` and its supercuspidal subset `A^0(n)`, which this module's
inclusion formalizes. Section 1.3, printed p.589 (PDF p.3), states the
irreducible-Weil/supercuspidal theorem, and sections 2.7–2.9, printed
pp.595–596 (PDF pp.9–10), give its extension to all classes. This file
formalizes the class inclusion and the restricted relations, not those
theorems.

- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

The Jacquet-vanishing definition of the imported class space agrees with
Bernstein–Zelevinsky 1977, sections 2.1–2.4, printed p.446 (PDF p.7), which
defines cuspidality by admissibility and vanishing of all proper Jacquet
modules (`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), and with
Casselman 1995, section 5.1, p.46
(`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`). Both
passages were read in the originals.

All imported class spaces, maps and lemmas are published Library
declarations of Worker 23's classification branch:
`Langlands.Representation.Classification.Supercuspidal` and
`Langlands.Representation.Classification.SupercuspidalTwist`. They are
imported, not copied.

## Validation

The module compiles in the project Lean service without errors or warnings,
together with `AutomorphicRelations` and `LocalConventions`. The relations
have no hypotheses beyond the field, the rank, the characters, the classes
and the scalars where applicable.
