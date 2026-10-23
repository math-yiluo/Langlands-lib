# Harris's complexes `C_m^{•,H}`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.Invariants`
(the `H`-invariants of `ℓ`-divisible systems of complexes of smooth
representations, as systems of complexes of representations of `G ⧸ H`, and
the instance for the truncated smooth Godement resolutions) and on
`Langlands.Cohomology.DivisibleSystem.Total` (finite-row total complexes of the
standard resolutions, and the group case `groupStandardTotalSystem`), and
through them on the Sections module and the earlier modules of the series. It
also uses Mathlib's instance `Subgroup.finite_quotient_of_finiteIndex`. All
names are in the namespace `Langlands.Cohomology.DivisibleSystem`.

On p.305 Harris calls `S(ẽ)/H` "a finite group", sets
`M_m^{q,H} = G_m^q(U(ẽ)_F̄)^H`, and resolves it by iterating the surjection
(2.4). On p.306 he lets (2.5) be "the canonical free resolution of `M_m^{q,H}`
obtained via (2.4)", and lets `C_m^{•,H}` be "the simple complex associated to
the double complex `K_m^{-•,•,H}` for each `m`. Then another snake lemma
argument shows that `C_m^{•,H}` is an ℓ-divisible system of complexes of free
`ℤ/ℓ^mℤ[S(e)/H]`-modules as `m` varies."

This module applies the Total module's total complexes, for the finite group
`Γ = G ⧸ H`, to the `H`-invariants systems of the Invariants module, for a
general system and for the truncated smooth Godement resolutions. It contains
no new construction beyond this composition, the choice `N = D + 2` of the row
bound, and three vanishing lemmas. It proves no freeness, no
quasi-isomorphism and no comparison between different subgroups.

## A general system

`R` is a commutative ring, `G` a topological group, `ℓ, N : ℕ`, and
`K : DivisibleSystem (CochainComplex (SmoothRep R G) ℕ) ℓ`, with smooth
representations in the Library's `SmoothRep.{uR, uG, max w uR uG} R G`.
`H : Subgroup G` is normal and of finite index (`[H.Normal] [H.FiniteIndex]`),
so `G ⧸ H` is finite by Mathlib's instance
`Subgroup.finite_quotient_of_finiteIndex`; this is the finiteness that the
Total module's group case needs. The hypothesis `hK` is that of the
Invariants module's `quotientInvariantsComplexes`: for all `m' ≤ m` and `q`,
the `H`-invariants of the degree-`q` component of the projection
`K m ⟶ K m'` form an epimorphism.

- `quotientInvariantsTotalSystem N K H hK` is
  `(K.quotientInvariantsComplexes H hK).groupStandardTotalSystem N`, an
  `ℓ`-divisible system of `ℤ`-graded cochain complexes in
  `Rep.{max w uR uG} R (G ⧸ H)`. At level `m` its degree-`n` term is the
  coproduct, over `q - r = n` with `q < N`, of `(Ind_1^Γ Res_1^Γ)^(r+1)` of the
  `H`-invariants of the degree-`q` term of `K m`, with the Total module's
  differential and signs.
- `quotientInvariantsTotalSystemAugmentation N K H hK` is the Total module's
  `groupStandardTotalSystemAugmentation` for this system. Its target is
  exactly the `totalSystem N` of the `H`-invariants system mapped along
  `(ChainComplex.single₀ _).mapHomologicalComplex (ComplexShape.up ℕ)`: the
  total complex, with rows `q < N`, of the `H`-invariants placed in resolution
  degree `0`. It is not identified with the `H`-invariants system.
- `isZero_quotientInvariantsTotalSystem_obj_X`: every level vanishes in
  degrees `n ≥ N` (the Total module's `isZero_totalSystem_obj_X`).

## The truncated smooth Godement resolutions

`R`, `G`, `X`, `h`, `T : SmoothSheafDivisibleSystem R G X ℓ`, `D : ℕ`,
`H : Subgroup G` normal and the hypotheses `hterm`, `hres` are those of the
Invariants module's `smoothGodementTruncatedQuotientInvariantSectionsSystem`
(all types in one universe `u`, and `h` a proof of Worker 3's unproved
proposition `SmoothGodementZeroExactStatement R G X`). `hterm` and `hres` say
that the `H`-invariants of the compact sections of the projections of the term
systems `F^q` (`q ≤ D`) and of the residual system `R (D + 1)` are
epimorphisms.

- `isZero_smoothGodementTruncatedQuotientInvariantSectionsSystem_obj_X`: the
  `H`-invariant section complexes vanish in degrees `q ≥ D + 2`. This is the
  Sections module's `isZero_truncatedResolutionSectionsSystem_obj_X` (the
  truncated resolutions vanish above `D + 1`, and the left exact functor of
  invariant compact sections preserves zero objects). It needs only
  `[H.Normal]`.

Now `H` also has finite index.

- `smoothGodementInvariantTotalSystem h T D H hterm hres` is
  `groupStandardTotalSystem (D + 2)` of
  `smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres`:
  the total complexes, rows `q < D + 2`, of the standard resolutions along
  `Ind_1^Γ Res_1^Γ`, `Γ = G ⧸ H`, of the `H`-invariant compact sections of the
  truncated smooth Godement resolutions, an `ℓ`-divisible system of
  `ℤ`-graded cochain complexes in `Rep.{u} R (G ⧸ H)`. By the previous lemma
  the rows `q ≥ D + 2` that the bound omits are zero. The module does not
  prove that the total complex of the unrestricted double complex, which
  would need infinite coproducts, agrees with this one.
- `smoothGodementInvariantTotalSystemAugmentation h T D H hterm hres` is the
  totalized augmentation; its target is the total complex, rows `q < D + 2`,
  of the `H`-invariant section complexes placed in resolution degree `0`.
- `isZero_smoothGodementInvariantTotalSystem_obj_X`: every level vanishes in
  degrees `n ≥ D + 2`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read both pages in the scanned original.

1. The complexes. Harris's `C_m^{•,H}` is the simple complex of the double
   complex `K_m^{-•,•,H}` of the resolutions (2.5) of the complexes
   `M_m^{•,H} = G_m^•(U(ẽ)_F̄)^H`. `smoothGodementInvariantTotalSystem` is
   this construction for the Library's stand-ins: the `H`-invariants of the
   compact sections of the truncated smooth Godement resolutions in place of
   `G_m^•(U(ẽ)_F̄)^H` (as in the Sections and Invariants modules), `G ⧸ H` in
   place of `S(ẽ)/H`, and `Ind_1^Γ Res_1^Γ` with its counit, over the
   coefficient ring `R`, in place of the integral surjection (2.4) (as in the
   StandardResolution module). `quotientInvariantsTotalSystem` is the same
   construction for a general system `K`.
2. The finite group. Harris notes that `S(ẽ)/H` is a finite group (p.305).
   Here `H` is any normal subgroup of finite index of `G`, and finiteness of
   `G ⧸ H` follows from that; no topology on `G ⧸ H` and no pro-`p` property
   of `H` are used.
3. The row bound. The Total module restricts the rows to `q < N`. Harris's
   complexes `M_m^{•,H}` have finite length (p.305), and for the truncated
   smooth Godement systems the module takes `N = D + 2`, justified by the
   vanishing of the rows `q ≥ D + 2`. Indexing (total degree `q - r`, against
   `q - r - 1` with Harris's labels) and signs (`ε₁ = 1`, `ε₂ = (-1)^q`) are
   those of the Total module; Harris states no sign rule.
4. Divisibility. Harris's snake lemma argument is replaced, as in the Total
   module, by the exactness of totalization and of the standard resolution
   functor. The surjectivity of the projections on `H`-invariants, which Harris
   derives from the exactness of `H⁰(H, ·)` for pro-`p` `H`, stays the
   explicit hypothesis `hK` (or `hterm`, `hres`) of the Invariants module.
5. Change of subgroup. Harris states a natural isomorphism
   `C_m^{•,H} = [C_m^{•,H'}]^H` for `H' ⊂ H` normal in `S(ẽ)`. For the
   resolution built from `Ind_1^Γ Res_1^Γ` this is not a literal identity of
   terms. With `Γ' = G ⧸ H'` and `M'` the `H'`-invariants in some degree, the
   first resolution term for `H'` is `R[Γ'] ⊗_R M'`, with `Γ'` acting by left
   multiplication on `R[Γ']`; its `H/H'`-invariants are `R[Γ] ⊗_R M'`, built
   from all of `M'`, whereas the corresponding term for `H` is
   `R[Γ] ⊗_R M'^{H/H'}`. The module does not construct any comparison between
   different subgroups.

The definitions `quotientInvariantsTotalSystem` and
`smoothGodementInvariantTotalSystem` and their augmentations are the formal
counterpart of Harris's `C_m^{•,H}` and of the totalized augmentation of
(2.5), with the surjectivity on invariants as a hypothesis. The finiteness
of `G ⧸ H`, the choice `N = D + 2` and the vanishing lemmas are derived.

## Scope

The module does not prove that any term is free or projective (Harris's
"complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules"; `Ind_1^Γ Res_1^Γ V = R[Γ] ⊗_R V`
is free over `R[Γ]` when `V` is free over `R`, which is not assumed), that
the augmentation is a quasi-isomorphism, or that its target is isomorphic
to the `H`-invariants system; no morphism to that system is constructed
here. It does not construct the isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`,
the direct limit over `H`, the quasi-isomorphism (2.6), the isomorphism (2.7)
or Lemma 2.8.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
