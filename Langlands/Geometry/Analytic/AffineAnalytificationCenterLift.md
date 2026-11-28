# Points of an analytification over a point with a prescribed center

Let `K` be a complete ultrametric nontrivially normed field, `A`, `D` finitely presented
`K`-algebras with finite polynomial presentations `P`, `Q`, and `f : A →ₐ[K] D` an algebra map
that is étale as a ring map. The theorem
`Langlands.Analytic.AffineAnalytification.exists_baseMap_eq_center` states: for every point
`z` of `Spec(A)ᵃⁿ` (`Space K P`) and every prime `𝔓` of `D` with
`PrimeSpectrum.comap f 𝔓 = center K P z`, there is a point `y` of `Spec(D)ᵃⁿ` with
`baseMap K P Q f y = z` and `center K Q y = 𝔓`. Here `center` is the prime kernel of the
multiplicative seminorm of a point and `baseMap` the induced map of analytifications.

The algebraic step is `CenterLift.exists_ringHom_ker_eq`: for an essentially finite type,
formally unramified `A`-algebra `D`, a ring map `g : A → Ω` into an algebraically closed field
and a prime `𝔓` of `D` lying over `ker g`, there is `g' : D → Ω` with `g' ∘ algebraMap = g`
and `ker g' = 𝔓`.

## Proof

- `exists_ringHom_ker_eq`: with `p = ker g` and `q = 𝔓`, the residue field `κ(q)` is a
  finite extension of `κ(p)` (`Localization.AtPrime.algebraOfLiesOver` and the finiteness of
  residue field extensions of quasi-finite algebras in Mathlib), hence algebraic. The map `g`
  induces `κ(p) → Ω` (`Ideal.ResidueField.lift`), which extends to `κ(q) → Ω` because `Ω` is
  algebraically closed (`IsAlgClosed.lift`). Composing with `D → κ(q)` gives `g'`; its kernel
  is `ker(D → κ(q)) = q` because a field map is injective.
- `exists_baseMap_eq_center`: realize the seminorm of `z` as the norm of a ring map
  `f₀ : A → H` into a complete valued field (`BaseChangeComparison.normedRealization`) and
  compose with the completed algebraic closure `Ω` of `H`, getting `g : A → Ω` with
  `‖g a‖ = |a|_z`; then `ker g` is the center of `z`. The algebra `D` is étale and of finite
  type over `A`, so the first step gives `g' : D → Ω` over `g` with kernel `𝔓`. The seminorm
  `b ↦ ‖g' b‖` extends the norm of `K`, so it is the seminorm of a point `y` of `Spec(D)ᵃⁿ`
  (`SeminormComparison.range_pointSeminorm`). Its restriction along `f` is the seminorm of
  `z`, so `baseMap K P Q f y = z` by injectivity of `pointSeminorm`; its kernel is
  `ker g' = 𝔓`.

## Provenance

Derived. The algebraic step is the standard extension of homomorphisms into algebraically
closed fields along finite residue field extensions. The analytic step uses the description
of the points of `Spec(A)ᵃⁿ` as the multiplicative seminorms on `A` restricting to the norm of
`K` (Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990),
Remark 3.4.2, printed p.64/PDF p.78), which the Library's `pointSeminorm` and
`SeminormComparison.range_pointSeminorm` implement.
