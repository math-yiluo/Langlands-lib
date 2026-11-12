# The type `C` root data of the split symplectic group in coordinates

This internal module restates the root data of the diagonal torus `t = diagonalTorus l k` of
the split symplectic group `SymplecticMatrix.groupScheme l k` over a field `k`. It uses the
coordinate characters `e_a` and cocharacters `e_a^∨` in the form used by a type `C`
almost-simplicity criterion. The inputs come from `SymplecticMatrix.RootSystem`,
`SymplecticMatrix.Roots` and `SymplecticMatrix.SimplyConnected`. Let `𝔻` be the split torus
`splitTorus.commGroupScheme (Spec k) (ULift l)`, the source of `t`. Roots are stated with the
Library's `relativeRoots t`, which is by definition `roots t`. Multiples `2 • χ` are
`ℕ`-multiples. No assumption is made on `l` or on the characteristic of `k`.

## Coordinate characters and cocharacters

* `coordChar l k a : characterLattice 𝔻` is the character with coordinates `Pi.single a 1`
  under the Library's `GeneralLinear.characterCoordEquiv l k`, i.e. `diag(t, t⁻¹) ↦ t_a`.
  `characterCoordEquiv_coordChar` restates the definition.
* `coordCochar l k a : cocharacterLattice 𝔻` is the cocharacter with coordinates
  `Pi.single a 1` under `GeneralLinear.cocharacterCoordEquiv l k`.
  `cocharacterCoordEquiv_coordCochar` restates the definition.
* `latticePairing_coordChar_coordCochar`: `⟨e_a, e_c^∨⟩ = if a = c then 1 else 0`. The pairing
  is the dot product of coordinates (`GeneralLinear.latticePairing_coord`).
* `two_smul_coordChar`: `2 • e_a` is the long root `longRoot l k a`.

## Roots and coroots

* `two_smul_coordChar_mem_roots`: each `2 • e_a` is a root (`longRoot_mem_roots`).
* `short_mem_roots`: for `a ≠ b`, both `e_b - e_a` and `-e_a - e_b` are roots. The first is
  `diffRoot l k b a`. The second is the negative of `sumRoot l k a b` (`neg_mem_roots`).
* `roots_typeC`: every root `χ` is `2 • e_a` or `-(2 • e_a)` for some `a`, or one of
  `e_b - e_a`, `-e_a - e_b`, `e_a + e_b` for some `a ≠ b`. Proof: by `mem_roots_iff`, the
  coordinates of `χ` are `w(x) - w(y)` with `x ≠ y`. The four cases for `x` and `y` in
  `l ⊕ l` give these forms. A case with equal indices gives `±2e_a`.
* `coroot_eq_coordCochar`: in a root datum `P` of `t`, if `P.root r = 2 • e_a`, then
  `P.coroot r = e_a^∨`. This is `cocharacterCoordEquiv_coroot_of_root_eq_longRoot`.

## Provenance

These are the standard type `C_l` roots and long coroots of `Sp_{2l}`, listed in Milne,
*Algebraic Groups* (2017), Summary 21.98 (printed p. 460). The module is internal. It only
repackages results of the earlier `SymplecticMatrix` modules in coordinate form.
