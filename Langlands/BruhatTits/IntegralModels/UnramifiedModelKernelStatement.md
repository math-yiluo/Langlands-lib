# Kernels of special-fibre maps between unramified parahoric models (KP 8.4.15)

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Proposition 8.4.15, printed pp. 306–307 / PDF pp. 337–338, and the
  opening of Section 8.4 with its notation `f̄` for the residue field of
  `K` and the special-fibre map `ρ̄_{Ω,Ω′}` of 8.3.17, printed p. 302 /
  PDF p. 333;
- the relation `Ω ≺ Ω′` ("`Ω` is contained in the closure of `Ω′`"),
  printed p. 26 / PDF p. 57 and printed p. 158 / PDF p. 189;
- Lemma 2.10.9, Corollary 2.10.10 and Corollary 2.10.11 (a smooth model is
  determined by its points over the integers `O` of the maximal unramified
  extension, and so are the morphisms out of it), printed pp. 123–124 /
  PDF pp. 154–155;
- Theorem 8.3.13 (printed p. 299 / PDF p. 330) and Proposition 7.7.5(1)
  (printed p. 269 / PDF p. 300), which give `𝒢^0_Ω(O) = G(K)^0_Ω` and
  identify `G(K)^0_Ω` with the pointwise stabilizer of `Ω` in `G(K)^0`.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, change
this proposition. On PDF p. 37 they assume in Sections 8.3 and 8.4 that the
residue field of `k` is perfect. On PDF p. 38 they insert the following
before Proposition 8.4.15: for two nonempty bounded subsets `Ω ≺ Ω′` of
`A`, the inclusion `G(K)^0_{Ω′} ⊂ G(K)^0_Ω` gives an `O`-group scheme
homomorphism `ρ_{Ω,Ω′} : 𝒢^0_{Ω′} → 𝒢^0_Ω`, and `ρ̄_{Ω,Ω′}` is the
induced map of special fibres. They also delete the first sentence
("Assume that `Ω ≺ Ω′ ⊂ A`.") of the proposition. The Library's KP source
ledger (`notes/bruhat-tits/kp-source-ledger.md`, the corrections row for
"Sections 8.3–8.4 and the setup of Proposition 8.4.15") records the same
correction. The ledger also records that the restricted product index in
Theorem 8.4.19(1) is false, while the general product of 8.4.15 is valid;
the statement below does not use either product.

## Source content

`k` has Henselian discrete valuation and perfect residue field `f`, `K` is
a maximal unramified extension of `k` with integers `O`, and `G` is
connected reductive over `k`, so `G_K` is quasi-split (corrections, PDF
p. 37). The opening of Section 8.4 (printed p. 302 / PDF p. 333) writes
`f̄` for the residue field of `K`, which is also the residue field of `O`
and an algebraic closure of `f`. Sections 8.3–8.4 write `G` for `G_K` and
work in its reduced building `B(G)` (Section 7.6, "The (Reduced)
Building"). `A` is the apartment of a maximal `K`-split torus `S`. For
nonempty bounded `Ω ≺ Ω′ ⊂ A`, the corrected Proposition 8.4.15 is about
the map of special fibres
`ρ̄_{Ω,Ω′} : 𝒢^0_{Ω′} ⊗_O f̄ → 𝒢^0_Ω ⊗_O f̄`. It says that the kernel of
`ρ̄_{Ω,Ω′}` is a smooth, connected, unipotent group. It also says that
multiplication gives an isomorphism of `f̄`-schemes onto that kernel from
the product, over the nondivisible roots `a`, of the kernels of the
induced maps of special fibres of the root-group models
`𝒰_{a,Ω′,0} ⊗_O f̄ → 𝒰_{a,Ω,0} ⊗_O f̄`.

Here `𝒢^0_Ω` is the smooth affine `O`-model of `G_K` with connected fibres
and `𝒢^0_Ω(O) = G(K)^0_Ω` (KP Theorem 8.3.13). By KP Proposition 7.7.5(1),
`G(K)^0_Ω` is the pointwise stabilizer of `Ω` in `G(K)^0`.

## Lean declarations

All types are in the arbitrary universe `u`.

`unramifiedModelKernelAffineHom` is a private instance. It records that the
base change of an affine group scheme along `F → inertiaFixedField F` is
again affine, by the pullback-stability of affine morphisms. The statement
needs it to form `MaximalUnramified.BuildingData`. It is the same private
instance as in the published `UnramifiedParahoricModelStatement`.

`UnramifiedModelKernelStatement.{u}` is an unproved proposition. Its inputs:

- `F`, a nonarchimedean local field. The source's `k`, `K` and `O` are `F`,
  the existing `inertiaFixedField F` (the maximal unramified extension inside
  the chosen separable closure) and `fixedFieldIntegers F`. The residue field
  of `F` (the source's `f`) is finite, hence perfect, so the corrected
  hypothesis of Sections 8.3–8.4 (corrections, PDF p. 37) holds. The
  residue field of `K`, equivalently of `fixedFieldIntegers F`, is then an
  algebraic closure of `f`. It is the source's `f̄` (Section 8.4 opening,
  printed p. 302 / PDF p. 333), the base of the special fibres below.
- `G`, an affine group scheme over `F`. Its base change
  `baseChanged F (inertiaFixedField F) G` is the source's `G_K`.
- `C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)`,
  the published supplied building data of `G_K` for the normalized integer
  valuation `MaximalUnramified.valuation F` of `K`. An element supplies the
  connected reductivity of `G_K`, a maximal split torus `S`, a
  `KPApartmentData` equipollence class with representing centralizer datum,
  and axiom V6 for that class. So the source's standing hypotheses on `G`
  are part of `C`. `C.ReducedBuilding` is the reduced building,
  `C.Apartment` the apartment, and `C.apartmentMap` the inclusion of the
  apartment.
- `E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)`, the
  published datum from which `E.zeroPoints` computes `G(K)^0` (KP
  Definition 2.6.23(1)).
- `g` in the rational points of `G_K`, and `Ωa Ωa′ : Set C.Apartment`. The
  source's `Ω` and `Ω′` are `{g • C.apartmentMap x | x ∈ Ωa}` and
  `{g • C.apartmentMap x | x ∈ Ωa′}`. Both lie in the translated apartment
  `g • A`, which is the apartment of `gSg⁻¹` (KP Proposition 6.2.5,
  printed pp. 215–216 / PDF pp. 246–247). Maximal `K`-split tori are
  `G(K)`-conjugate, so every apartment of the reduced building arises this
  way, and the source's single apartment `A` is any of them.
- Three hypotheses on the subsets. `Ωa` is nonempty. `Ωa′` is bounded:
  every real affine function on `C.Apartment` is bounded above on it (so,
  applying this to `-f`, bounded). `Ωa` lies in the closure of `Ωa′` for
  the initial topology of all real affine functionals. This topology is
  `affineApartmentTopology` of `Langlands.BruhatTits.IntegralModels.ModelFamily`,
  the convention of the target `IntegralModelAxiomsStatement`; that
  definition is stated for `ValuationBuildingData`, so the statement writes
  the same infimum of induced topologies inline for `C.Apartment`. The
  translation space is finite-dimensional, so this is the usual topology of
  the real affine space `A`, the action of `g` is an affine isomorphism of
  `A` onto `g • A`, and the hypothesis says `Ω ≺ Ω′` inside `g • A`. With
  it, `Ω′` is nonempty (the closure of the empty set is empty) and `Ω` is
  bounded (the closure of a bounded set is bounded, as in the published
  `isBoundedSubset_apartmentClosure`). So `Ω` and `Ω′` are exactly the
  corrected source's two nonempty bounded subsets with `Ω ≺ Ω′`.
- `N N′ : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) _`,
  two smooth published integral models of `G_K` (affine, flat, of finite
  type, with a specified generic-fibre isomorphism). Their integral points
  are fixed by two equations:

  ```lean
  N.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa)
  N′.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa′)
  ```

  `C.pointwiseFixer` is the pointwise fixer for the action of `G(K)` on
  the reduced building `C.ReducedBuilding`, the building in which
  Sections 7.7 and 8.3–8.4 work. By Proposition 7.7.5(1) the right-hand
  sides are therefore `G(K)^0_Ω` and `G(K)^0_{Ω′}`. The same subgroups are
  the `neutral` integral points in the published
  `UnramifiedParahoricModelStatement`.
- `ψ : N′.Hom N (𝟙 _)`, any model homomorphism whose generic fibre is the
  identity of `G_K`. The direction `N′ → N` is the source's direction of
  `ρ_{Ω,Ω′}`, from the model of the larger subset `Ω′`.

The conclusion is about `kernel ψ.specialFibreMap`, the published
scheme-theoretic kernel (`Langlands.GroupScheme.kernel`, a pullback along
the unit) of the special-fibre map `IntegralModel.Hom.specialFibreMap` of
`ψ` (the base change of `ψ` to the residue field of
`fixedFieldIntegers F`, the source's `f̄`), as a group scheme over that
residue field. Under the identifications below this is the source's
`ker(ρ̄_{Ω,Ω′})`.
Its structure morphism is smooth, its underlying scheme is connected, and
it is unipotent in the sense of the published `IsUnipotent` (every nonzero
finite-dimensional representation has a nonzero fixed vector). These are
the three conjuncts of the published
`RelativeComponentModelHom.HasSmoothConnectedUnipotentKernel`, written for
a single model homomorphism.

## Choices and scope

- **Any presentation of the models.** The source fixes the models
  `𝒢^0_{Ω′}`, `𝒢^0_Ω` and the homomorphism `ρ_{Ω,Ω′}`. The statement
  instead quantifies over every smooth `N`, `N′` with the right integral
  points and every `ψ`. This is the same assertion. `O` is strictly
  Henselian, so for a base field equal to `K` the points tested in KP
  Lemma 2.10.9 and Corollaries 2.10.10–2.10.11 are the `O`-points
  themselves. By Corollary 2.10.11, smooth affine models are determined up
  to unique isomorphism compatible with the generic fibre by their
  `O`-points. Hence `N ≅ 𝒢^0_Ω` and `N′ ≅ 𝒢^0_{Ω′}`. Under these
  isomorphisms `ψ` is `ρ_{Ω,Ω′}`, because a model homomorphism is
  determined by its generic fibre (Corollary 2.10.10, or the published
  generic rigidity `IntegralModel.Hom.hom_eq`, the models being flat).
  These isomorphisms commute with the special-fibre maps, so they induce
  an isomorphism of the special-fibre kernels, and being smooth, connected
  and unipotent is invariant under such an isomorphism. Conversely the
  source's models are instances: they are smooth with these `O`-points,
  and `ρ_{Ω,Ω′}` is a model homomorphism with identity generic fibre. The
  statement asserts no existence of models or homomorphisms; if none
  exists the conclusion is vacuous. A consumer can therefore apply the
  statement to models built in any way, such as base changes of models
  over `𝒪[F]`.
- **Why over `O` and not over `𝒪[F]`.** The source works over `O`.
  Corollaries 2.10.10–2.10.11 test a smooth model by its points over the
  integers of the maximal unramified extension; its `𝒪[F]`-points do not
  determine it, since the residue field of `F` is finite. For example,
  with `q` the residue cardinality and `π` a uniformizer, the dilatation
  `Spec 𝒪[F][x, (x^q − x)/π]` of the additive group along the constant
  subgroup `𝔽_q` of its special fibre is a smooth affine model of the
  additive group with the same `𝒪[F]`-points `𝒪[F]`, but its special fibre
  is disconnected and it is not isomorphic to `𝔾_a`. A statement over
  `𝒪[F]` whose models are pinned down only by `𝒪[F]`-points would
  therefore range over models other than KP's and would not express the
  source result. A consumer with models over `𝒪[F]` applies this
  statement to their base changes to `O`, whose integral points it knows
  (for example from the published `UnramifiedParahoricModelStatement` and
  the descent statement `UnramifiedSmoothModelDescentStatement`), and then
  descends the conclusion along the residue field extension.
- **Omitted part.** The statement omits the second assertion of 8.4.15:
  the isomorphism of `f̄`-schemes onto the kernel from the product of the
  kernels `ker(𝒰_{a,Ω′,0} ⊗_O f̄ → 𝒰_{a,Ω,0} ⊗_O f̄)`, `a ∈ Φ_nd`, of the
  maps between the special fibres of the root-group models. It records
  only the smooth–connected–unipotent conclusion, which is what KP Axiom
  4.1.22(1) uses.
- **No connected-fibre hypothesis.** The source's models have connected
  fibres. The statement does not assume this, because the integral-point
  equations and smoothness already determine the models up to
  isomorphism, as explained above.
- **Choice of `E`.** KP define `G(K)^0` from one maximally split maximal
  torus `T`. The statement quantifies over every datum `E`, which also
  chooses a splitting field of `T` and a simply connected cover. This is
  no strengthening: `G(K)^0` does not depend on `T` (KP Lemma 2.6.24,
  printed p. 104 / PDF p. 135), `T(K)^0` does not depend on the splitting
  field (Lemma 2.5.12, printed p. 89 / PDF p. 120), and the image of the
  simply connected cover does not depend on the chosen cover. The Library
  does not prove these independence results; the statement needs them only
  for the comparison with the source.
- **Choice of `C`.** The statement quantifies over every supplied `C`.
  This is no strengthening either. The class carried by `C` is an
  equipollence class of valuations of the root datum of `(G_K, S)`
  satisfying V6, which is KP's `ω`-compatibility (Section 6.1, printed
  p. 199 / PDF p. 230). By KP Proposition 6.2.6 (printed p. 216 / PDF
  p. 247) any two `ω`-compatible valuations are equipollent, so the class
  of `C` is KP's canonical apartment `A(S)` (Definition 6.1.27, printed
  p. 210 / PDF p. 241), and `C.ReducedBuilding` is the reduced building of
  `G_K`. The Library proves this rigidity step as
  `Langlands.Geometry.Building.IntegerValuation.IsOmegaCompatible.eq_of_hasOppositeFactorPairs`
  (module `IntegerOmegaApartmentRigidity`), keeping the existence of
  opposite factor pairs (KP Proposition 2.11.17) as an explicit premise.
  The choice of `S` is immaterial since the translates `g • A` cover all
  apartments.

## Intended consumers

The construction of the integral models for KP Axioms 4.1.20 and 4.1.22
(task `cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs this statement. The
general morphism clauses of Axiom 4.1.22 require the special-fibre kernel of
each model homomorphism `𝒢_{Ω′} → 𝒢_Ω` over `𝒪[F]` to be smooth, connected
and unipotent. That task applies the statement after unramified base change
and descends the conclusion to the finite residue field.
