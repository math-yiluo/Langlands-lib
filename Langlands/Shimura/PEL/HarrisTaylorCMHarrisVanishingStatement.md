# Harris (1999), (5.1): the `JL(π_f)`-isotypic part of `H^j(S_U, W)_λ` vanishes outside degree `n − 1`

This module states formula (5.1) of Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39 (1999),
printed p. 312, as an unproved proposition. The setting is the Library's CM
Shimura varieties of Harris's signature, the Library's `λ`-adic cohomology
with coefficients in an algebraic representation `ρ`
(`HarrisTaylorCMLambdaTower`), and the published transfer relation `JL(π_f)`
(`JacquetLanglands.IsHarrisJacquetLanglandsTransfer`). The declaration is
`CMHarrisVanishingStatement`, in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. Its elaborated type is
`Prop`. It assumes Harris's hypothesis (R) of [H1]: at every finite place,
the algebra of the Shimura varieties is split or a division algebra.

The hypotheses on `π_f`, `JL(π_f)` and the model of `JL(π_f)` over an
`ℓ`-adic field are encoded as in Worker 34's statement of Harris's
Theorem 5.7(i)–(ii) (`CMHarrisTheorem57Statement`, submitted as candidate
`023a56d6`). This module neither imports that statement nor depends on it.

## Harris's formula

Harris's setting (§§4–5, printed pp. 308–313) is a CM field `𝒦` containing an
imaginary quadratic field `𝒦₀`, a division algebra `ℬ` with involution of the
second kind, defining the unitary similitude group `GG` and its Shimura
varieties `S_K`, and an inner form `GJ` (algebra `𝒟`) of `GG`. `GJ` is split
at a place `v` of `𝒦` above a prime `p` split in `𝒦₀`, and `ℬ` is a division
algebra at `v`. Printed p. 312 (PDF p. 14, checked against the page image)
reads:

> Let `π` be a representation of `GJ`, and let `π_v` be its constituent at
> the chosen place `v`, as in [H1, H2]; `π_v` is a representation of
> `GL(n, 𝒦_v)`. Suppose `π_v` is supercuspidal. Let `JL(π_f)` be the
> corresponding irreducible admissible representation of `GG(A_f)`; the local
> constituents of `JL(π_f)` and `π_f` are the same except at `v`, where they
> correspond by the local Jacquet-Langlands correspondence [DKV, R], also
> denoted `JL(•)`.
>
> Using Proposition 4.10, we can now apply the arguments of [H1] and [H2,
> App.] to express the representation of the decomposition group `Z_v` on the
> `JL(π_f)`-isotypic component of `H^{n−1}(S̄_{K(N)}, W̃)`, which we denote
> `H^{n−1}(S̄_{K(N)}, W̃)[π]`. In the first place, the arguments of §1 of [H1]
> apply without change to general coefficient systems (cf. [HL]) and show that
>
> (5.1) `H^i(S̄_{K(N)}, W̃)[π] = 0,   i ≠ n − 1.`
>
> This also follows from Theorem 1 of [H1] and Proposition 4.10: since `π_v`
> is supercuspidal, the higher Ext's vanish and the spectral sequence
> (4.10.1) degenerates […].

Here `[H1]` is Harris, *Supercuspidal representations in the cohomology of
Drinfel'd upper half spaces; elaboration of Carayol's program*, Invent. Math.
129 (1997). Its §1 is the source of the argument recorded below.

## Harris's hypothesis (R)

Harris (1999), §4, printed p. 308 (PDF p. 10), says "We return to the
framework of [H1, H2]". The framework of [H1], §1, printed p. 79 (PDF p. 5,
checked against the page image), has the totally real field `E`, the CM field
`𝒦` and the division algebra `ℬ` of dimension `n²` over `𝒦`, and continues:

> In order to apply base change we make the following hypothesis:
>
> (R) At every place `w` of `E`, `ℬ` is either split or a division algebra.
>
> We assume `ℬ` to be a division algebra at a large (unspecified) number of
> finite places of `𝒦`; this is to guarantee that all eventual inner twists
> of associated unitary groups remain in the class considered by Kottwitz and
> Clozel, [K], [C2,C3,C4] so that pseudo-stabilization of the trace formula
> and quadratic base change are available. In particular, all global groups
> are anisotropic modulo center.

The argument of [H1] §1 cited for (5.1) uses (R). In the proof of Lemma 2
(printed p. 82), Harris notes that strong multiplicity one for `ℬ'^{opp,×}`
(`ℬ'` is the algebra of the inner form `J`) follows from "Vignéras' [V]
theorem on the transfer of automorphic representations from `B'^{opp,×}` to
`GL(n)`, which is proved only under hypothesis (R)". The proof of Lemma 4 uses
the same theorem for `ℬ` ("the correspondence of Arthur-Clozel-Vignéras, cf.
[V]"). So the statement assumes (R).

## The Library's data

The section variables up to `U` are those of the published
`HarrisTaylorCMLambdaTower`. They are the central simple unitary data
`D : CentralSimpleUnitaryData E F A n` (Harris's `ℬ` is `A`, and `GG` is the
similitude group of `D.rationalInvolution`), the charts `C` for Harris's
CM-type section, the conditional statements `preservation … htor`, the
representability statement `q`, the coefficient field `K`, the algebraic
representation `ρ` of `GG` over `K` on `W` (Harris's `W̃`), the statements
`existence` and `geometry`, the rigidity hypothesis `hRigid`, and a small level
`U : SmallCMLevel D`. In the Lean names, Harris's `𝒦` is `F` and his `𝒦₀` is
the imaginary quadratic field `L`, with `ι = algebraMap L F`.

The remaining variables are those of the published
`JacquetLanglands.IsHarrisJacquetLanglandsTransfer`
(`Langlands/JacquetLanglands/HarrisTransfer`), with `σB` taken to be
`D.toSecondKindInvolution`:

* the algebra `D'` of `GJ` with its involution `σJ : SecondKindInvolution E F D'`;
* the prime `p` with `hp : p.Prime`, the place `v` of `ℚ` above it, the place
  `𝔭` of `L` above `v` with `h𝔭` saying that `L_𝔭 = ℚ_p` (so `p` splits in `L`),
  and the place `w₀` of `F` above `𝔭` (Harris's `v`);
* the splitting `s : F_{w₀} ⊗_F D' ≃ M_n(F_{w₀})`, the central division algebra
  `Δ` over `F_{w₀}` with `t : F_{w₀} ⊗_F A ≃ Δ`, and the identifications `f`
  (at the other places above `𝔭`) and `e`, `he` (away from `p`) of `GJ` with
  `GG`.

## The statement

`CMHarrisVanishingStatement D C preservation … htor q ρ existence geometry
hRigid U σJ p hp v 𝔭 h𝔭 w₀ s Δ t f e he : Prop` says the following. It has
two universe parameters, `wS` and `wR`, for the derived-category instances
below.

Assume:

* Harris's condition (R): for every finite place
  `w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)`, the algebra
  `F_w ⊗_F A` (`w.adicCompletion F ⊗[F] A`) is split, that is,
  `Nonempty (F_w ⊗_F A ≃ₐ[F_w] Matrix (Fin n) (Fin n) F_w)`, or it is a
  division algebra, that is, every nonzero element of `F_w ⊗_F A` is a unit.
* `πf : Representation ℂ σJ.rationalInvolution.FiniteAdelicPoints V` (Harris's
  `π_f`) and `ρ' : Representation ℂ D.rationalInvolution.FiniteAdelicPoints V'`
  are related by `IsHarrisJacquetLanglandsTransfer … πf ρ'`, that is,
  `ρ' = JL(π_f)`. The relation includes that both are irreducible and
  admissible, that they have the same constituents away from `w₀`, and that
  their constituents at `w₀` form a Jacquet–Langlands pair.
* `π_v` is supercuspidal: for the published splitting
  `harrisAwaySplitGL … s : GJ(A_f) ≃ GL_n(F_{w₀}) × HarrisAwayComplement`,
  `πf` is equivalent to `splitTensor` of a supercuspidal representation `πv`
  of `GL_n(F_{w₀})` (`GeneralLinear.IsSupercuspidal`: admissible, with zero
  Jacquet modules for all proper block parabolics and their conjugates) and a
  representation `πaway` of the complement.
* `ℓ` is a coefficient prime with the Library's derived-category instances,
  and `lam` is a place of `K` above `ℓ`.
* `M` is a field extension of `K_λ`, and `j : M ≃+* ℂ` is a field
  isomorphism. This is Harris's identification of `ℚ̄_ℓ` with `ℂ`, used to
  compare complex representations with `ℓ`-adic ones. No topology on `M` is
  needed, because the conclusion concerns vector spaces only.
* `τ : Representation M GG(A_f) V''` is the model of `JL(π_f)` over `M`
  through `j`: an additive bijection `eτ : V' ≃ V''` with
  `eτ (z • x) = j⁻¹(z) • eτ x` that intertwines `ρ'` and `τ`.

Then for every degree `d ≠ n − 1`, the space
`cmHarrisLambdaTowerIsotypicFixedVectors … lam d M τ U` is zero
(`Subsingleton` of its underlying module). This is the space of vectors fixed
by the ordinary level of `U` in the `τ`-isotypic part of
`H^d(S, W)_λ ⊗_{K_λ} M`. Here `H^d(S, W)_λ = colim_U H^d(S_U ×_F F̄, W)_λ` is
the Library's tower cohomology, and the `τ`-isotypic part is the sum of the
images of all `GG(A_f)`-intertwining maps `τ → H^d(S, W)_λ ⊗_{K_λ} M`.

## Relation to the source

* **The level.** Harris states (5.1) at the levels `K(N)` of §4. The
  statement is made at every small level `U`. Every vector of
  `H^d(S, W)_λ ⊗_{K_λ} M` is fixed by the ordinary level of some small level,
  so the statement at all `U` says that the whole `τ`-isotypic part vanishes
  in degree `d`. This is what the argument below proves.
* **Fixed vectors of the tower.** The space in the conclusion is defined in
  the tower cohomology. The Library identifies it with the `τ`-isotypic part
  of the level-`U` cohomology `H^d(S_U ×_F F̄, W)_λ ⊗ M`, which is Harris's
  `H^d(S̄_{K(N)}, W̃)[π]` for `U = K(N)`, only under the published proposition
  `CMHarrisLambdaTowerFixedVectorComparison`. That proposition is not proved
  in the Library. The statement does not assume it, since the conclusion does
  not need it.
* **Harris's signature and the Shimura datum.** The Library's `λ`-adic
  cohomology exists only for the Harris-signature charts. That the Library's
  `S_U` over `F`, with the coefficient system attached to `ρ`, is Harris's
  `S̄_{K(N)}` with `W̃` is not formalized.
* **`ℬ` is a division algebra.** Worker 34's Theorem 5.7 statement assumes
  that `A` is a division algebra. This statement does not, because the
  hypothesis follows from the variable `t`. The map `a ↦ 1 ⊗ a` from `A` to
  `F_{w₀} ⊗_F A` is injective, since `F_{w₀}` is a field extension of `F`, and
  `F_{w₀} ⊗_F A ≃ Δ` is a division ring. So `A` is a nonzero
  finite-dimensional `F`-algebra without zero divisors, hence a division
  algebra.
* **Hypothesis (R).** Harris states (R) at the places of the totally real
  field `E`, and the statement states it at the finite places of `F`
  (Harris's `𝒦`). At a place of `E` with a single place of `F` above it, the
  two conditions are the same. At a place of `E` that splits into two places
  `w, w^c` of `F`, `ℬ ⊗_E E_w` is the product of `F_w ⊗_F A` and
  `F_{w^c} ⊗_F A`. Such a product is never a division algebra, so Harris's
  condition is read factor by factor, which is the condition at `w` and at
  `w^c`. The involution of the second kind identifies `F_{w^c} ⊗_F A` with
  the opposite algebra of `F_w ⊗_F A`, compatibly with complex conjugation
  `F_w ≃ F_{w^c}`, so the conditions at `w` and `w^c` are equivalent.
  The archimedean places of `E` impose no condition: `F` is totally complex,
  so `ℬ` splits at every archimedean place. The hypothesis is not implied by
  the other hypotheses. `CentralSimpleUnitaryData` and the charts `C` do not
  constrain the finite places, and `t`, `f`, `e` only fix `A` at `w₀` and
  relate the algebra `D'` of `GJ` to `A` elsewhere.
* **The unspecified number of division places.** Harris also assumes that
  `ℬ` is a division algebra at a large, unspecified number of finite places.
  The statement does not assume this, because it cannot be made precise and
  is not used by the argument for (5.1). Harris's stated purpose is that "all
  eventual inner twists of associated unitary groups remain in the class
  considered by Kottwitz and Clozel". On printed p. 80 he uses it to see that
  the algebra `ℬ'` of `J`, which is split at `v₁, v₂`, is again a division
  algebra. The argument below concerns only `GG`, the group of the division
  algebra `A`, which is anisotropic modulo its center. It uses `π_f` only
  through the transfer relation at `w₀`, and no automorphic property of `J`
  or `GJ`.
* **No condition on `ℚ_p^×`.** Harris's hypothesis that the factor `ℚ_p^×` of
  `GJ_p` in (4.2) acts trivially on `π` belongs to Theorem 5.7, printed
  p. 313, and not to (5.1). It is not assumed.
* **The coefficient prime.** The statement is made for every prime `ℓ`,
  including `ℓ = p`. Harris's second argument, through Theorem 1 of [H1] and
  Proposition 4.10, uses the `ℓ`-adic vanishing cycles at `p` and needs
  `ℓ ≠ p`. His first argument, the one recorded below, compares with complex
  cohomology and works for every `ℓ`.
* **Automorphy.** Harris's `π` is a representation of `GJ`, in practice
  automorphic. The statement does not assume automorphy. If `JL(π_f)` does
  not occur in the cohomology, the isotypic part is zero and the conclusion
  holds trivially.
* **`JL(π_f)` and its model.** `JL(π_f)` is given by the published relation,
  which asserts neither existence nor uniqueness. Its model over `M` is
  described relationally through `j`. No construction is assumed.

## Why the statement is true

This is the argument of Harris [H1], §1, Lemma 4 (printed p. 82, proof on
pp. 82–83), which Harris (1999) says applies to general coefficient systems.
Fix `d ≠ n − 1` and suppose that a vector fixed by `U` in the `τ`-isotypic
part is nonzero. Then there is a nonzero intertwining map
`τ → H^d(S, W)_λ ⊗_{K_λ} M`.

1. **Transport to `ℂ`.** Make `M`-spaces into `ℂ`-spaces through `j`. Then `τ`
   becomes a representation equivalent to `ρ'` through `eτ`, and
   intertwining maps are unchanged. Choose an embedding of `F̄` into `ℂ`. By
   the comparison between étale and Betti cohomology,
   `H^d(S_U ×_F F̄, W)_λ ⊗_{K_λ} M` becomes the Betti cohomology
   `H^d(S_U(ℂ), W_ℂ)` with coefficients in the local system of `W ⊗_K ℂ`, for
   the embedding `K → K_λ → M → ℂ`. These identifications are compatible with
   the level-changing maps, so the tower cohomology becomes
   `H^d(S, W_ℂ) = colim_U H^d(S_U(ℂ), W_ℂ)` as a representation of `GG(A_f)`.
   So `ρ'` occurs in `H^d(S, W_ℂ)`.
2. **Matsushima's formula.** Since `A` is a division algebra, the Shimura
   varieties are compact. Matsushima's formula gives a decomposition
   `H^d(S, W_ℂ) = ⊕_Π m(Π) Π_f ⊗ H^d(𝔤, K_∞; Π_∞ ⊗ W_ℂ)` over automorphic
   representations `Π` of `GG`. Since `ρ'` is irreducible, it is isomorphic to
   `Π_f` for some `Π` with `H^d(𝔤, K_∞; Π_∞ ⊗ W_ℂ) ≠ 0`.
3. **The constituent at `w₀`.** The tensor factors of an irreducible
   admissible representation of a product are determined up to equivalence.
   So the transfer relation and the supercuspidality hypothesis show that the
   constituent of `Π_f = ρ'` at `w₀`, a representation of `Δ^×`, corresponds
   under Jacquet–Langlands to the supercuspidal `πv`.
4. **Lemma 4 of [H1].** "Let `π` be a cohomological representation of `L`
   [`L = G` or `GG`], and suppose `JL(π_v)` is supercuspidal. Then
   `H^q(Lie(L_∞), K_∞; π_∞) ≠ 0` if and only if `q = n − 1`." Harris's proof
   takes the base change of `Π` to an automorphic representation of the units
   of `A` (Clozel), and then the corresponding discrete automorphic
   representation `Π_𝒦` of `GL_n(A_𝒦)` ("correspondence of
   Arthur-Clozel-Vignéras, cf. [V]"). Harris notes on printed p. 82 that this
   transfer from the units of the division algebra to `GL_n` is proved only
   under hypothesis (R); this is where the statement's hypothesis (R) is used.
   Harris–Taylor (2001), §VI.1, printed p. 195, likewise recall that their
   algebra is a division algebra at each place where it ramifies before
   deriving this transfer (their Theorem VI.1.1) from Arthur–Clozel. By
   Clozel's purity theorem
   and Moeglin–Waldspurger's description of the residual spectrum, a `Π` that
   contributes to cohomology outside the middle degree `n − 1` gives a
   residual `Π_𝒦`. But the constituent of `Π_𝒦` at `w₀` is the supercuspidal
   `JL(Π_{w₀}) = πv`, and a supercuspidal representation is not a local
   constituent of a residual representation. With coefficients `W_ℂ` the same
   argument applies, as Harris (1999) states. So `d = n − 1`, a contradiction.

The argument uses the comparison theorem, Matsushima's formula, base change
for these unitary groups, the transfer to `GL_n` under (R) and the purity
theorem. None of these is in the Library. They are the unproved content of
the statement.

## Provenance

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999): §5, printed p. 312 (PDF p. 14): `π`, `π_v`
supercuspidal, `JL(π_f)`, the isotypic component and formula (5.1), checked
against the page image. Theorem 5.7, printed p. 313 (PDF p. 15), for the
hypothesis on `ℚ_p^×` that (5.1) does not use. §4, printed p. 308 (PDF
p. 10), for the return to the framework of [H1, H2]. The source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces; elaboration of Carayol's program*, Invent. Math. 129
(1997): §1, printed p. 79 (PDF p. 5, checked against the page image), for
hypothesis (R) and the assumption on division places; printed p. 80 for the
algebra `ℬ'` of `J`; the proof of Lemma 2, printed p. 82, for the remark that
Vignéras' transfer is proved only under (R); Lemma 4, printed p. 82 (PDF p. 8,
checked against the page image), proof on printed pp. 82–83. The source is
`harris-1997-drinfeld-cohomology`, PDF SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.

M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties*, Annals of Mathematics Studies 151 (2001): §VI.1, printed p. 195
(PDF p. 203), the paragraph before Theorem VI.1.1. The source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, PDF SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The Library's ingredients are `IsHarrisJacquetLanglandsTransfer`,
`harrisAwaySplitGL`, `HarrisAwayComplement` and `splitTensor`
(Jacquet–Langlands); `GeneralLinear.IsSupercuspidal`; and
`cmHarrisLambdaTowerIsotypicFixedVectors` of `HarrisTaylorCMLambdaTower`. The
encoding of the hypotheses follows Worker 34's `CMHarrisTheorem57Statement`.
