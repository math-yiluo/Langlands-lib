# The Weil class of a finite unramified extension without a transfer hypothesis

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`.

For a finite unramified Galois extension `E/F` of `p`-adic fields, this module shows
that the actual Weil pushout class `finiteGaloisClass F E f hGal e he`
(`Langlands.Weil.Local.FiniteGaloisPushout`) is the explicit cyclic class of a base
unit of order one. Under an arithmetically normalized invariant family it is therefore
the fundamental class.

The Library already proves this as `finiteGaloisClass_eq_cyclicClass` and
`finiteGaloisClass_isFundamental_of_unramified` (Worker 1839,
`Langlands.Weil.Local.FiniteGaloisUnramified`). Those versions assume the unproved
transfer square `ExtensionWeilTransferReciprocityStatement` and a reciprocity
candidate for `F`. They use these only to identify the base unit with `e_F(Φ)`. The
versions here assume neither: the unit is shown to lie in `F` and to have order one
directly, and the normalization only needs some unit of order one.

This is the unramified case of Tate, *Number theoretic background* (1979), §1.2,
printed p.5 (PDF p.14): the class `α_{E/F}` of the Weil group extension is the
canonical (fundamental) class. For an unramified extension the fundamental class is the
cyclic class of a uniformizer for the arithmetic Frobenius coordinate. In the Library
this normalization is the hypothesis `InvariantFamily.ArithmeticNormalization`.

All declarations are in `Langlands.Weil.Local`.

## Definitions

Fix `f : F → E` with `E/F` Galois (`hGal`), a natural number `n ≠ 0`, and an arithmetic
unramified coordinate `χ : Gal(E/F) ≃* ZMod n` (`IsArithmeticUnramifiedCoordinate`).
Let `q : W_F → Gal(E/F)` be the finite Galois quotient, `Φ` the chosen geometric
Frobenius of `W_F` (`localGeometricFrobenius`), and `r` the inverse reciprocity of a
candidate `e` on `ker q` (`finiteGaloisKernelReciprocity`). By the Library lemma
`finiteGaloisQuotient_inv_localGeometricFrobenius`, `χ(q(Φ⁻¹)) = 1`.

- `frobeniusPowerKernel F E f hGal χ hχ` is the element `Φ^{-n}` of `ker q`. It is the
  Library's `powerKernel` for the generator `Φ⁻¹`.
- `frobeniusPowerKernel_reciprocity_mem_range`: if `e` satisfies the geometric relation,
  then `r(Φ^{-n})` lies in the image of `F` in `E`. Let `s(σ) = Φ^{-(χ σ)}` be the
  Library's power section (`frobeniusPowerSection`). For `σ ∈ Gal(E/F)`, `s(σ)` is a power
  of `Φ⁻¹`, so it commutes with `Φ^{-n}`, and the conjugate of `Φ^{-n}` by `s(σ)` is
  `Φ^{-n}`. The equivariance of `r` (`finiteGaloisKernelReciprocity_conjugateKernel`) and
  `q(s σ) = σ` give `σ • r(Φ^{-n}) = r(Φ^{-n})`.
  `IsGalois.mem_range_algebraMap_iff_fixed` concludes.
- `unramifiedFrobeniusUnit F E f hGal e he χ hχ : Fˣ` (definition) is the element of `F`
  whose image is `r(Φ^{-n})`, chosen from the previous membership. It is nonzero because
  `r(Φ^{-n})` is a unit.
- `units_map_unramifiedFrobeniusUnit`: its image in `Eˣ` is `r(Φ^{-n})`.

## `exists_finiteGaloisClass_eq_cyclicClass`

Data: `f : F → E` with `E/F` Galois (`hGal`), equal canonical ramification indices
(`hUnr`), a candidate `e` for `E` satisfying `GeometricWeilReciprocityRelation`, a
natural number `n ≠ 0` with `extensionDegree F E f = n`, and an arithmetic unramified
coordinate `χ : Gal(E/F) ≃* ZMod n` (`IsArithmeticUnramifiedCoordinate`). Conclusion:
there is `a ∈ Fˣ` (namely `unramifiedFrobeniusUnit F E f hGal e he χ hχ`) with
`ord_F a = 1` and

`finiteGaloisClass F E f hGal e he = cyclicClass F E χ a`.

Proof. Let `q : W_F → Gal(E/F)` be the finite Galois quotient, `Φ` the chosen
geometric Frobenius of `W_F` (`localGeometricFrobenius`), and `r` the inverse
reciprocity on `ker q`. By the Library lemma
`finiteGaloisQuotient_inv_localGeometricFrobenius`, `χ(q(Φ⁻¹)) = 1`. Use the Library's
power section `s(σ) = Φ^{-(χ σ)}` (`frobeniusPowerSection`), with kernel element
`k = Φ^{-n}` (`powerKernel`).

1. *The unit.* Let `a = unramifiedFrobeniusUnit F E f hGal e he χ hχ`, so that
   `algebraMap F E a = r(k)` with `k = Φ^{-n}` (`units_map_unramifiedFrobeniusUnit`).
2. *`ord_F a = 1`.* Write `k = ι(y)` with `y ∈ W_E`. Since `E/F` is unramified, the
   relative residue degree is `[E:F] = n`
   (`ramificationIndex_eq_iff_extensionResidueDegree_eq`). So
   `localDegreeInt_extensionWeilMap` gives `n · deg_E y = deg_F(Φ^{-n}) = -n`, hence
   `deg_E y = -1`. By the geometric order relation, `ord_E(e(y)) = deg_E y = -1`, and
   `r(k) = e(y)⁻¹` (`finiteGaloisKernelReciprocity_apply`) has order `1`. The second
   norm-order law (`relativeNormOrderLaws`), `e_F · ord_E(algebraMap a) = e_E · ord_F(a)`,
   with `e_F = e_E`, gives `ord_F a = 1`.
3. *The class.* `finiteGaloisClass_eq_of_section` computes the class with the section
   `s`. By `cocycle_powerSection` its factor cocycle is
   `(g, h) ↦ r(k)^{carry(χ g, χ h)}`. Since `r(k) = a` in `Eˣ`, this is the Library's
   `cyclicUnitCocycle F E χ a`.

## `finiteGaloisClass_isFundamental_of_unramified_of_order`

For `F, M` in one universe, `f : F → M` Galois with equal ramification indices, a
candidate `eM` for `M` satisfying the geometric relation, and an invariant family `J`
with `J.ArithmeticNormalization`:

`IsFundamentalClass F M (J.relative F M) (finiteGaloisClass F M f hM eM heM)`.

Proof. `arithmeticUnramifiedCoordinateExistence` gives an arithmetic coordinate `χ`
for `n = [M:F]`. By the previous theorem the class is `cyclicClass F M χ a` with
`ord_F a = 1`. Arithmetic normalization sends it to `1/n`
(`reciprocalClass [M:F]`), which is the definition of `IsFundamentalClass`.

## Provenance

The final statement is the unramified case of the identification of the Weil class
with the fundamental class in Tate (1979), §1.2, printed p.5. Its Lean statement is the
Library's `finiteGaloisClass_isFundamental_of_unramified` without the transfer and
base-field reciprocity hypotheses. The definitions `frobeniusPowerKernel` and
`unramifiedFrobeniusUnit`, the intermediate existence theorem and the proof route
(Galois-fixedness of `r(Φ^{-n})` and its order) are internal.
