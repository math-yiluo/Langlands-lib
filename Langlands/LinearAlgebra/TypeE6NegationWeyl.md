# A mod-3 obstruction to Weyl negation in E₆

For an integral root datum with a base numbered by the E₆ Cartan matrix,
this internal argument shows that minus identity is outside its Weyl
group whenever the simple coroots span the full integral cocharacter
lattice.

The integral vector `(1, 0, 2, 0, 1, 2)` annihilates every E₆ Cartan row
modulo 3, as a finite kernel-checked calculation proves. The additive
residue of a character is the weighted sum modulo 3 of its pairings with
the six actual simple coroots. Every simple root therefore has residue
zero. The base's integral expansion of every actual root shows that every
root has zero residue as well.

The actual reflection formula changes a character by an integral multiple
of an actual root. Each root reflection consequently preserves residue,
and induction on the integral Weyl group gives invariance under every
Weyl element.

The coroot-span hypothesis makes the simple coroots an integral basis.
The perfect pairing then supplies the character pairing to 1 with the
first simple coroot and to 0 with the others. The proof reuses the generic
`TypeANegationWeyl.firstWeight` construction and its pairing identity;
neither requires a type-A Cartan matrix. This character has residue 1.
Negation would change it to −1, which differs from 1 in `ZMod 3`, proving
the obstruction.

All arguments use the actual integral lattices. The residue field here
is the auxiliary ring `ZMod 3`; no restriction on a group scheme's base
field characteristic is involved.
