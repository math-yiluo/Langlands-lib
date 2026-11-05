# Norm surjectivity on units over the separable inertia fixed field

Authors: Worker 1512 and Worker 1237. Worker 1512 wrote the shared draft
of the Lean declaration and this file. Worker 1237 checked it against the
imported interfaces and the original sources and revised this file.

`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity.{u}`
is a proposition definition, not a proof. It states the form of KP
Remark 2.5.11 that KP Lemma 2.5.12 uses: over the maximal unramified
extension `K` of a nonarchimedean local field `F`, the norm of every finite
extension of every finite extension of `K` maps units onto units.

## The proposition

For every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, write `U := inertiaFixedField F` and
`v := sepClosureValuation F`. For every

- `E : IntermediateField U (SeparableClosure F)` with
  `[FiniteDimensional U E]`,
- `L : IntermediateField E (SeparableClosure F)` with
  `[FiniteDimensional E L]`, and
- `u : Eˣ` with `v ((u : E) : SeparableClosure F) = 1`,

the proposition asserts that there is `x : Lˣ` with
`v ((x : L) : SeparableClosure F) = 1` and
`Langlands.LocalClassField.normUnits E L x = u`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary, and `F` may have characteristic zero or positive characteristic.

## Exact fields, maps and scope

- `U = inertiaFixedField F`, imported from
  `Langlands.Galois.Local.SeparableInertiaDefinitions`, is the actual
  intermediate field of `SeparableClosure F` fixed by the inertia subgroup
  `separableInertia F` of `Gal(SeparableClosure F/F)`. That subgroup is
  the kernel of the residue action on the integers of the spectral
  valuation. `U` is the field that
  `Langlands.Geometry.Building.UnramifiedClosure F` abbreviates in
  `Langlands.Geometry.Building.KPZeroSubgroups`, which is KP's `K`, the
  maximal unramified extension of `F` in `F^sep`. No separately chosen or
  postulated unramified field occurs.
- `E` and `L` are presented as intermediate fields of the same separable
  closure. `L` is an intermediate field over `E`, so the tower
  `U → E → L → SeparableClosure F` consists of the actual inclusions. Every
  finite extension involved is therefore separable; there is no separability
  hypothesis. Finiteness is over the infinite field `U` and then over `E`.
  It is not finiteness over `F`.
- `v = sepClosureValuation F` is the spectral valuation
  `spectralValuation F (SeparableClosure F)` with values in `ℝ≥0`, that
  is, the spectral norm of `F^sep/F` over the norm `localNormedField F`.
  That norm is the rank-one norm attached to the valuation of `F`, and the
  instance `sepClosureValuation_extends` records that `v` extends the
  valuation of `F`. Since `F` is complete, `v` is the unique extension of
  the absolute value of `F` to `F^sep`; this standard fact explains the
  convention and is not part of the proposition. Only the condition
  `v = 1` occurs, so the normalization of the absolute value plays no role.
  The restriction of `v` along `E → F^sep` (respectively `L → F^sep`) is
  the absolute value of `E` (respectively `L`). For intermediate fields of
  `F^sep/UnramifiedClosure F` this restriction is exactly
  `Langlands.Geometry.Building.intermediateValuation`, by
  `intermediateValuation_apply`. Thus an element of `Eˣ` with `v`-value
  `1` is a unit of the valuation ring `O_E`, and the same holds for `L`.
  The hypothesis on `u` and the condition on `x` say exactly that
  `u ∈ O_E^×` and `x ∈ O_L^×`.
- `Langlands.LocalClassField.normUnits E L`, imported from
  `Langlands.ClassFieldTheory.Local.Norms`, is exactly
  `Units.map (Algebra.norm E)` for the given finite-dimensional `E`-algebra
  `L`. It is the determinant norm. No replacement norm, chosen preimage
  function or norm subgroup is defined here.

The proposition asserts the inclusion `O_E^× ⊆ N_{L/E}(O_L^×)`. The
reverse inclusion `N_{L/E}(O_L^×) ⊆ O_E^×` holds by the valuation identity
`v(N_{L/E} x) = v(x)^{[L:E]}` explained below. That inclusion is not part
of the proposition, but together the two give the source form
`N_{L/E}(O_L^×) = O_E^×`. `L/E` is not assumed Galois. There are no
assumptions on ramification, residue fields, completeness, Henselian
properties, Galois cohomology or norm images.

The existing `Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormSurjectivity`
(module `Langlands.ClassFieldTheory.Local.InertiaFixedFieldNormStatement`)
is a different proposition. It concerns `PadicField p` and the inertia
fixed field inside `AlgebraicClosure`. It states surjectivity on the full
multiplicative groups for Galois `L/E`. The present statement is
characteristic-uniform, uses `SeparableClosure F` and the separable
inertia fixed field, and concerns units. Neither proposition is used as a
hypothesis here.

## Original sources and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections (version of 1 November 2024) are registered as
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979, is registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
PDF page numbers below count from one.

- KP §2.1 ("Henselian Fields", printed pp. 68–70 / PDF pp. 99–101): `k`
  is a Henselian field (Definition 2.1.1), and on printed p. 70 / PDF
  p. 101 KP assume that its valuation is discrete and its residue field is
  perfect, and let `K` denote the maximal unramified extension of `k`
  contained in `k^s`. Here `k = F` is a nonarchimedean local field. It is
  complete, hence Henselian (Example 2.1.4), discretely valued, and has
  finite, hence perfect, residue field, so it satisfies these assumptions.
- KP Remark 2.5.11, printed p. 89 / PDF p. 120: for a finite separable
  extension `L/K` the norm map `O_L^× → O^×` is surjective, where `O` and
  `O_L` are the rings of integers of `K` and `L`. KP cite
  "[Ser79, Chapter V, §7, Corollary 4]". The authors' corrections
  (Section 2.5, PDF p. 24) replace "§7" by "§6".
- KP Lemma 2.5.12 and its proof, printed pp. 89–90 / PDF pp. 120–121:
  independence of the splitting field `L` reduces to showing that
  `T(L') → T(L)` maps `T(L')^b` onto `T(L)^b` for `L ⊂ L'`. For
  `T = G_m` this is Remark 2.5.11 applied to the extension `L'/L`, whose
  base `L` is finite over `K` rather than equal to `K`. This use is the
  reason the proposition quantifies over a finite extension `E` of `U` and
  a finite extension `L` of `E`.
- Serre, Chapter V, §6, Corollary 4, printed p. 93 / PDF p. 100, in the
  setting of §6 (printed p. 91 / PDF p. 98): `L/K` is Galois and totally
  ramified, and, by the standing hypotheses of Chapter V (printed p. 80 /
  PDF p. 87, referring to Chapter IV), `K` is complete under a discrete
  valuation. If the residue
  field is algebraically closed, then `N(U_L^{ψ(v)}) = U_K^v` for every real
  `v ≥ 0`. At `v = 0` this is surjectivity on units.
- Serre, Chapter V, §4, Proposition 7, printed p. 90 / PDF p. 97: let `K`
  be complete under a discrete valuation with perfect residue field and
  let `K_nr` be its maximal unramified extension. If `F ⊃ E ⊃ K_nr` are
  finite extensions of `K_nr` with `F/E` separable, then `N(F^*) = E^*`.

The proposition is a derived formulation, not a verbatim numbered result.
The fields `E` here are finite over `U`, which is Henselian but not
complete, so Serre's §6 corollary, stated for complete fields, does not
apply to them verbatim. Serre's Proposition 7 applies verbatim with
Serre's `K := F` and `K_nr := U`, and gives `N_{L/E}(L^×) = E^×`. The unit
form follows. If `N_{L/E}(x) = u` with `v(u) = 1`, then
`v(u) = ∏_σ v(σ x)` over the `E`-embeddings `σ : L → F^sep`. Each `σ`
extends to an automorphism of `F^sep` over `F`, and the spectral valuation
is invariant under these automorphisms. Hence
`v(u) = v(x)^{[L:E]}`, so `v(x) = 1`. KP Corollary 2.3.7 (printed p. 81 /
PDF p. 112) also proves `L^× → E^×` surjective for finite Galois `L/E`
with `E` finite separable over `K`. This statement records only the unit
form that KP Remark 2.5.11 and Lemma 2.5.12 need. It does not claim the
multiplicative form.

The statement supplies no proof. A proof is a separate obligation.
