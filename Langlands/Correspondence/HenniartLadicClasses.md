# Irreducible ℓ-adic local Galois classes

Let `K` be a nonarchimedean local field, `Ω` a separable closure of `K`, and `ℓ`
a prime. The Galois group `Ω ≃ₐ[K] Ω` carries Mathlib's Krull topology. The
coefficient field `E = PadicAlgCl ℓ` is Mathlib's algebraic closure of `ℚ_[ℓ]`
with its spectral norm. The universe of the representation carriers is
independent of the universes of `K` and `Ω`. The definitions apply in every
characteristic and for every prime `ℓ`.

## Continuity, finite coefficients, and irreducible classes

`IsLadicContinuous ℓ A` says that the action takes the group continuously into
the endomorphisms of the actual carrier of `A`, given their module topology over
`E`. This is the finite-dimensional topology on the endomorphisms. In a basis
it is the product topology on the matrix entries.

`IsLadicDefinedOverFiniteExtension ℓ A` asks for one intermediate field `L`
of `E` of finite dimension over `ℚ_[ℓ]` and one `E`-basis such that
every entry of every action matrix lies in `L`. The definition uses the
coordinates of each image of a basis vector, with the basis indexed by the
finite rank of `A`. The matrix of the inverse group element also has entries in
`L`, so these matrices specify a representation over `L`.

`IrreducibleLadicClass K Ω ℓ n` takes genuine linear intertwining isomorphism
classes of rank `n : ℕ+` whose representatives satisfy both predicates and are
irreducible. It uses `FiniteRepresentation.IsomorphismClassesOfRankWith`.
`ladicClassForget` returns the underlying isomorphism class. Laumon (1987),
(2.1.1)–(2.1.2), pp. 151–152, gives the Galois group and inertia of a henselian
trait and the continuous finite-extension module convention. Henniart (1988),
§4.1, pp. 509–510, uses that convention for the irreducible representations of
`G_K`. [Laumon source map](../../notes/henniart/laumon-local-fourier-source-map.md)

## Unramified characters and twisting

`ladicUnramifiedCharacters K Ω ℓ` is a subgroup of the continuous monoid
homomorphisms from the absolute Galois group to `Eˣ` with its units topology.
Its members are trivial on `LocalGalois.SepClosed.absoluteInertia K Ω`, the
inertia subgroup, and have all their values in a common finite
intermediate extension of `ℚ_[ℓ]`. In rank one, the character acts by scalar
multiplication on `E`, where evaluation at `1` identifies linear endomorphisms
with `E` and the sole matrix entry is the character value. Laumon (1987),
(2.1.5), p. 154, gives the inertia-trivial convention. Henniart (1988), §4.1,
pp. 509–510, describes twists using unramified ℓ-adic characters of `Kˣ`.
The continuity condition here is on the Galois group, where the twists act.

`ladicUnramifiedTwist K Ω ℓ k χ` is the equivalence on rank `k + 1` classes
that multiplies each action by the scalar `χ(g)`. Scalar multiplication on
endomorphisms gives continuity of the twist. The finite model uses the same
basis and the compositum of the two fields of coefficients. The Library's
subrepresentation order isomorphism preserves irreducibility, and retaining
the carrier preserves rank. The inverse equivalence twists by `χ⁻¹`.
`ladicClassForget_unramifiedTwist` identifies the underlying map with
`FiniteRepresentation.twistClassEquiv`.

`ladicTorsionNumber K Ω ℓ ρ` is `Nat.card` of the subtype of unramified
characters whose twist fixes `ρ`. It records the self-twist stabilizer that
appears in Henniart (1988), §4.1, pp. 509–510. The action
`ladicUnramifiedTwistAction` preserves the first component of the sigma type
of all positive-rank irreducible classes and twists the second component.
`LadicUnramifiedOrbitClasses K Ω ℓ` is its orbit quotient and
`ladicUnramifiedOrbitClass K Ω ℓ k ρ` is the orbit of `⟨k, ρ⟩`. In Henniart
(1988), §4.2, p. 510, this orbit construction is used to count classes with
irreducible inertia restriction and prescribed rank and conductor conditions.
[Henniart source index](../../notes/henniart/sources.md)

## Scalar extension and transport to the Weil group

`ladicScalarExtension ℓ ι A` equips `ℂ` with the `E`-algebra structure
`ι.toAlgebra` for the chosen coefficient embedding `ι : E →+* ℂ`. The action
on `ℂ ⊗[E] A` sends `z ⊗ a` to `z ⊗ A.representation g a` for each group
element `g`. Mathlib provides the action on endomorphisms and the finite
base-change instance. `LinearEquiv.baseChange` transports an invertible
intertwiner, and `LinearMap.baseChange_comp` transports its intertwining
equation. `ladicScalarExtensionClass ℓ ι` is the resulting quotient map.

`ladicWeilTransport K Ω ℓ ι` first applies `FiniteRepresentation.restrictClass`
along `Weil.Local.SepClosed.localProjection K Ω`, and then
applies `ladicScalarExtensionClass ℓ ι`. The Weil group is the one for the
specified separable closure, with algebraicity and separable closedness
derived from `IsSepClosure K Ω`. The domain and codomain are the full
algebraic isomorphism class quotients. Henniart (1988), §4.2, p. 510, compares
finite-image Galois representations by choosing an isomorphism between the
algebraic closures of `ℚ` in `ℂ` and `ℚ̄_ℓ`. The transport here uses that
coefficient-change construction on all classes by using the supplied
embedding of the full ℓ-adic coefficient field and the explicit Weil
restriction.

## Laurent series over a finite field

For a finite field `𝓀`, Mathlib supplies the field and the X-adic topology on
`LaurentSeries 𝓀`. The local instance below installs the Library's valuative
relation, with which `Langlands.LocalField.Laurent.localField` supplies the
nonarchimedean local-field instance. `SeparableClosure X` supplies its field,
`Algebra X (SeparableClosure X)`, and `IsSepClosure X (SeparableClosure X)`
instances through Mathlib. The examples use an independent carrier universe `uW`.

```lean
import Langlands.Correspondence.HenniartLadicClasses
import Langlands.LocalField.LaurentSeries

noncomputable section

open Langlands Langlands.Henniart.LocalNumerical
open Langlands.Weil.Local.SepClosed (localWeilGroup)

universe u uW

variable (𝓀 : Type u) [Field 𝓀] [Finite 𝓀] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "X" => LaurentSeries 𝓀
local notation "Ω" => SeparableClosure X
local instance : ValuativeRel X := Langlands.LocalField.Laurent.valuativeRel 𝓀

example (n : ℕ+) : Type (max u (uW + 1)) :=
  IrreducibleLadicClass.{u, u, uW} X Ω ℓ n

example : Type (max u (uW + 1)) :=
  LadicUnramifiedOrbitClasses.{u, u, uW} X Ω ℓ

example (ι : PadicAlgCl ℓ →+* ℂ) :
    FiniteRepresentation.IsomorphismClasses.{0, _, uW} (PadicAlgCl ℓ) (Ω ≃ₐ[X] Ω) →
      FiniteRepresentation.IsomorphismClasses.{0, _, uW} ℂ (localWeilGroup X Ω) :=
  ladicWeilTransport X Ω ℓ ι
```

## Original sources

- Gérard Laumon, *Transformation de Fourier, constantes d'équations
  fonctionnelles et conjecture de Weil* (1987), `laumon-1987-fourier-weil`,
  (2.1.1), p. 151, (2.1.2), p. 152, and (2.1.5), p. 154.
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
  (1988), `henniart-1988-numerical`, §4.1, pp. 509–510, and §4.2, p. 510.
