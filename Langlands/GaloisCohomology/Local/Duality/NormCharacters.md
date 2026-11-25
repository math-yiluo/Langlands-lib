# Norm groups of abelian extensions of a local field

`Langlands/GaloisCohomology/Local/Duality/NormCharacters.lean`, namespace
`Langlands.GaloisCohomology.Local`.

Two theorems of local class field theory for a finite abelian extension `L` of a nonarchimedean
local field `K` (Mathlib's `IsNonarchimedeanLocalField`, `K L : Type u` in any universe `u`),
obtained from the local Artin homomorphism `abelianArtinHom` of the bridge
`Langlands.ClassFieldTheory.Local.Artin.NormSubgroup` (onto, `abelianArtinHom_surjective`, with kernel
the norm group, `abelianArtinHom_ker`): NYLL's map in any universe
(`LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UniverseArtin.lean`), which comes from NYLL's local reciprocity law
(`LocalClassFieldTheory.abelianizationEquivNormQuotient`, `…/LocalReciprocity/Main.lean`), proved
there for every finite Galois extension of a nonarchimedean local field, in every characteristic.
The norm group is NYLL's `LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup K L`, the image
of `Algebra.norm K` on `Lˣ`.

## Declarations

- `galCommGroup K L`: the Galois group of an abelian extension as a commutative group.
- `reciprocityEquiv K L : Gal(L/K) ≃* Kˣ ⧸ N(Lˣ)` for `L/K` finite abelian: the inverse of the
  isomorphism `Kˣ ⧸ N(Lˣ) ≃* Gal(L/K)` induced by NYLL's Artin map. (NYLL's Artin map is normalized
  by the geometric Frobenius; nothing here depends on the normalization.)
- `index_fieldNormSubgroup_of_isAbelianGalois K L`: the **norm index** `[Kˣ : N(Lˣ)] = [L : K]`.
- `exists_norm_iff_mem_fieldNormSubgroup`, `exists_norm_of_eq`: being a norm from an intermediate
  field `E` of `Ω/F` is membership in its norm group.
- `eq_top_of_forall_exists_norm H hH hcomm h`: an open normal subgroup `H` of `Gal(Ω/F)` with
  abelian quotient such that every element of `Fˣ` is a norm from the fixed field of `H` is the
  whole group (`F` a local field, `Ω` a separable closure).

The existence theorem for subgroups containing `Kˣⁿ`
(`exists_isAbelianGalois_fieldNormSubgroup_eq`) is proved from local duality in
`Duality/Existence.lean`.

## Source and licence

`exists_norm_iff_mem_range_normUnits` (here `exists_norm_iff_mem_fieldNormSubgroup`),
`exists_norm_of_eq` and `eq_top_of_forall_exists_norm` are ported from
`src/GroundTheory/ProfiniteCohomology/LocalTateDuality/NormCharacters.lean` of the repository
`leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`. The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

The source proves `eq_top_of_forall_exists_norm` from its own norm index
(`index_range_normUnits_of_isAbelianGalois`, in its `LocalFields/NormCorrespondence.lean`, from
its own local class field theory with Lubin–Tate theory); here the norm index comes from the NYLL
copy's Artin map. The source's second theorem of this file, `exists_zmod_char_not_norm`
(which needs the existence theorem and the reciprocity isomorphism), is not taken: local duality
in degree one is proved here without it (see `Pairing.md`). `galCommGroup`, `reciprocityEquiv` and
`index_fieldNormSubgroup_of_isAbelianGalois` are new.

## References

- J.-P. Serre, *Local Fields*, chapter XI, §3, Theorem 1 (the reciprocity isomorphism of a class
  formation), p. 168, with chapter XIII, §4, Theorem 1 (the local class formation), p. 195.
- J. Neukirch, *Algebraic Number Theory*, chapter V, §1, Theorem (1.3) (the local reciprocity law),
  p. 320.
