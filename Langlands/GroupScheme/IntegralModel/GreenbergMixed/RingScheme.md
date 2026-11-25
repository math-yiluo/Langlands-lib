# Greenberg coefficient ring schemes (interface)

`GreenbergRingScheme R n` packages the coefficient functor used to build Greenberg
group schemes at congruence level `n` over a local ring `R` with residue field `k`
(KP Appendix A.4, the Greenberg functor). It is an internal interface of the proof of
`MixedCharacteristicGreenbergPointModelStatement`: the Witt-vector construction
provides an instance, and the group-scheme construction uses
only the fields below.

A structure `ℛ : GreenbergRingScheme R n` consists of

- `functor : CommAlgCat (CommRingCat.of k) ⥤ CommAlgCat (CommRingCat.of R)`, the ring
  scheme `B ↦ ℛ(B)`;
- `dim : ℕ` and natural coordinates `coord B : ℛ(B) ≃ (Fin dim → B)`, with every
  `k`-algebra map acting coordinatewise (`coord_map`); so `ℛ` is affine space as a
  functor of sets;
- `levelEquiv : ℛ(k) ≃ₐ[R] R ⧸ 𝔪ⁿ` (`congruenceRing R n`);
- ring homomorphisms `red B : ℛ(B) →+* B`, given by one fixed `k`-linear form in the
  coordinates (`red_coord`), sending `algebraMap R (ℛ B) r` to the residue class of `r`
  in `B` (`red_algebraMap`), and whose kernels are nilpotent ideals
  (`ker_red_nilpotent`);
- for every ideal `I` of `B` with `I ^ 2 = ⊥`, the kernel of `ℛ(B) → ℛ(B ⧸ I)` is a
  nilpotent ideal (`ker_map_nilpotent`).

For a complete DVR of mixed characteristic with perfect residue field, `ℛ(B)` is the
Greenberg ring: a product of truncated Witt vector rings `W_{m_i}(B)` with the
multiplication transported from `R ⧸ 𝔪ⁿ ≅ ⊕ W(k) ⧸ p^{m_i}`; `red` is the first Witt
component combined with the residue map.

Provenance: this is an internal interface derived from the Greenberg functor
construction (Greenberg, *Schemata over local rings*, Ann. of Math. 73 (1961); KP §A.4).
Only the listed properties are used downstream.
