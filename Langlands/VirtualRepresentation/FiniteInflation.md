# Inflation from a finite quotient to continuous exact virtual groups

Helper module for the proof of
`Langlands.LocalFactor.CommonClosureDegreeZeroGenerationStatement`. In
Tate's proof of (2.3.1) (*Number theoretic background*, Corvallis 1979), a
representation of a Weil group with finite image is treated as a
representation of a finite quotient. Brauer's theorem is applied there, and the
result is carried back to the Weil group. This module supplies the carrying
back: an integer-linear inflation map from the split Grothendieck group of a
group `Q` to the continuous exact virtual group of a topological group `G`,
for a homomorphism `π : G →* Q` with open kernel. It also shows that inflation
turns induction from a subgroup `S` of `Q` into induction from the preimage
subgroup of `G`. Nothing here is specific to Weil groups or to finite `Q`.

## Coinduction and inflation (`Langlands.FiniteRep`)

Fix `π : G →* Q`, subgroups `S ≤ Q` and `T ≤ G` with `g ∈ T ↔ π g ∈ S` for all
`g` (hypothesis `hT`), a representation `σ` of `S` on `V`, a representation `τ`
of `T` on `W`, and a linear equivalence `e : V ≃ₗ W` with
`e (σ ⟨π t, _⟩ v) = τ t (e v)` (hypothesis `he`).

- `coindInflation_tau_eq`: if `π t = 1` then `τ t` is the identity.
- `coindInflation_apply_eq`: every function `F` in Mathlib's coinduced space
  `Representation.coindV T.subtype τ` takes the same value at `g` and `g'`
  whenever `π g = π g'`. The reason is that `g' * g⁻¹` lies in `T` and is in
  the kernel of `π`.
- `coindInflationLinearEquiv` and `coindInflationEquiv`: if `π` is surjective,
  then `f ↦ (g ↦ e (f (π g)))` is an intertwining linear equivalence from
  `(Representation.coind S.subtype σ).comp π` to
  `Representation.coind T.subtype τ`. The inverse is
  `F ↦ (q ↦ e⁻¹ (F (s q)))`, where `s = Function.surjInv` is a set-theoretic
  section of `π`. By `coindInflation_apply_eq` the result does not depend on
  the section.
- `compEquiv φ e`: an equivalence of representations stays an equivalence
  after both are composed with a monoid homomorphism `φ`.

## Inflated representations (`Langlands.FiniteRepresentation`)

- `isContinuous_of_le_ker A N hN h`: if a finite-dimensional complex
  representation `A` of `G` is trivial on an open subgroup `N`, then `A` is
  continuous. Its kernel contains `N`, so it is open, and the Library lemma
  `Weil.continuous_of_open_kernel` applies.
- `inflate π V`: for `V : FDRep ℂ Q`, the restriction along `π` of
  `Weil.liftFiniteRepresentation V`, whose carrier is `V` lifted to the
  universe `uV`.
- `isContinuous_inflate`: if `π` has open kernel, the inflation is continuous.
  This is `isContinuous_of_le_ker` with `N = ker π`.
- `inflateEquiv π V e`: given an equivalence `e` of `V.ρ` with some
  representation `ρ` of `Q`, the inflation is equivalent to `ρ.comp π`.

## The inflation map (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

Write `Cont(G)` for the exact virtual group of continuous representations,
`ExactGrothendieckGroup (fun A => A.IsContinuous)`.

- `ofRepresentation_eq_add_of_equiv_prod`: let `A`, `B` and `C` be
  representations satisfying the predicate, and suppose `C` is equivalent to
  the product representation `A × B`. Then `[C] = [A] + [B]`. The proof is the
  defining short-exact relation for `A → C → B`, using the left inclusion and
  the second projection transported through the equivalence.
- `inflateClass π hπ`: the map on representation classes `RepClass ℂ Q` sending
  the class of `V` to `[inflate π V]`. It is well defined because isomorphic
  `V` have equivalent inflations. `inflateClass_classOf` records its value on
  `classOf V`.
- `inflateClass_add`: it is additive. The direct sum `sumRep V W` is the
  product representation, so its inflation is equivalent to the product of
  the inflations.
- `inflateHom π hπ` and `inflate π hπ`: the additive map, and its extension to
  the integer-linear map `VirtualRep ℂ Q →ₗ[ℤ] Cont(G)` given by the universal
  property of the group completion. `inflate_ofClass` gives its value on a
  genuine class.
- `inflate_ofClass_induce`: let `π` be surjective with open kernel. Let
  `S ≤ Q` and `T ≤ G` have finite index, with `g ∈ T ↔ π g ∈ S`. Let
  `V : FDRep ℂ S` and let `B` be a continuous representation of `T` matched
  with `V` by `e` and `he` as above. Then
  `inflate π hπ (ofClass (FiniteRep.induce S (classOf V)))` is the exact
  induction `ExactGrothendieckGroup.induce T` of `[B]`. The equivalence used
  is the chain: the lifted carrier back to the coordinate model of the
  induced representation (`liftFiniteEquiv`); the coordinate model to
  Mathlib's quotient induction (`FiniteRep.induceRepEquiv`); quotient
  induction to equivariant-function coinduction (`FiniteRep.indCoindEquiv`);
  and finally `coindInflationEquiv`.
