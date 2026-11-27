# The centre of a simply connected group of type `E_7` is `μ_2`

Module: `Langlands.GroupScheme.SimplyConnected.TypeE7CenterKernel`,
namespace `Langlands.GroupScheme`.

## Declarations

- `eq_self_of_natCard_eq_two`: in an additive group `X` with `Nat.card X = 2`,
  every injective additive endomorphism `f` satisfies `f x = x` for all `x`.
- `TitsIndexData.nonempty_center_iso_of_typeE7`: let `G` be an affine, locally
  finite-type group over a field `k : Type u`, `d : TitsIndexData G`, and
  `e : d.Vertex ≃ Fin 7` with `d.cartan a b = CartanMatrix.E 7 (e a) (e b)`. If `G` is
  simply connected, then for every scheme-theoretic centre `z : Z ⟶ G`
  (`IsSchemeTheoreticCenter z`),
  `Nonempty (Z ≅ splitRootsOfUnityProduct k (fun _ : PUnit.{u + 1} => 2))`.
  The right-hand side is the split product of roots-of-unity groups with one factor
  `μ_2` (module `Rational/CentralSplitTorsionCocycleLift`).

## Proof

The full centre is isomorphic to the toral centre of the Tits index
(`TitsIndexData.isoToralCenter`), a group of multiplicative type
(`toralCenter_isMultiplicativeType`). The number of its geometric characters is the
absolute value of the determinant of the numbered Cartan matrix
(`natCard_centerCharacter_eq_cartanDet`), which is `2` for `E_7`
(`CartanMatrix.E₇_det`). A group of prime order is cyclic, so the character group is
`ZMod 2`. Each element of the absolute Galois group acts on it by an injective
additive map, hence trivially (`eq_self_of_natCard_eq_two`). A multiplicative-type
group with constant character group `(PUnit → ZMod 2)` is the diagonalizable group of
that character group (`characterLattice.isoOfConstantAbsoluteEquiv`), which is the
power `μ_2^PUnit` (`HomScheme.FiniteDiagonalizable.diagonalizableIso`), that is,
`splitRootsOfUnityProduct k (fun _ => 2)`. The construction is that of
`HasNumberFieldCentralKernelModel.of_constant_character_coordinates`, written out to
keep the explicit model.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press,
1994), proof of Proposition 6.16, printed p. 335: for type `E_7`, `Z(G₀) = μ_2`.
