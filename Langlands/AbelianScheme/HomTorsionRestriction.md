# Finite torsion restriction of integral Hom groups

`homTorsionRestriction T n` is the integer-linear map sending an actual
abelian-scheme homomorphism to its function on the existing level-`n` torsion
points of a test scheme `T`. It uses the pointwise group law on the existing
Hom group. Additivity follows from the group-scheme multiplication law.

For actual abelian schemes over `Spec k`, with `k` an algebraically closed
field of characteristic zero, `homTorsionRestriction_ker` identifies the
kernel of this map at the identity geometric point with the range of
integer multiplication by `n`, for every positive natural number `n`.
If a homomorphism kills all geometric torsion points, the published
`Tate.kernel_comp_eq_one_of_levelMap_eq_zero` shows that it kills the scheme
kernel of multiplication. The published finite étale multiplication isogeny
and `GroupScheme.IsogenyFactorization.lift` then divide the actual
homomorphism by `n`. Conversely, a multiple of `n` vanishes on `n`-torsion.
No rational or prime-adic approximation is used.

`torsionLevel_finite` obtains finiteness of each torsion-point set from
finite étale torsion and the published geometric-fiber finiteness theorem.
Thus the target function set of restriction is finite. The first
isomorphism theorem, together with the kernel calculation, proves

```lean
hom_modN_finite : Finite (ModN (A ⟶ B) n)
```

Here Mathlib's `ModN M n` is exactly the quotient of `M` by the range of
`LinearMap.lsmul ℤ M n`; no finite-generation assumption on `M` is required.

The auxiliary `field_nat_isUnit` transfers invertibility of a positive
integer in `k` to global sections through `Scheme.ΓSpecIso`.
The imported `Rosati.homToHom0_injective_of_charZero` specializes the published
`Tate.ofHom_injective` to show that actual Hom injects into its rationalization.
This injectivity only requires characteristic zero; algebraic closedness is
used in the geometric torsion arguments.

The provenance is a derived implementation of the torsion-division step in
J. S. Milne, *Abelian Varieties* (1986 article, author revision of 2 January
2022), Lemma 12.6, printed/PDF p.21. The lemma treats prime powers; the
implemented proof applies the same factorization argument to any positive
integer, which is invertible in the chosen characteristic-zero field.
The finite quotient consequence additionally uses the finite étale torsion
theorem already proved in the Library. These results concern actual
homomorphisms and their canonical integer module, in arbitrary universe `u`.
They do not assert global finite generation or freeness.

Source identifier: `milne-abelian-varieties-1986-author-2022`; PDF SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The complete registered author errata snapshot was read; the cited revision
incorporates its correction to the proof of Theorem 12.5.
