# The half modulus of a standard parabolic on its positive split component

Module `Langlands.Global.AdelicHalfModulusRootProductStatement`, namespace `Langlands.Global`.
It states one proposition, `HalfModulusRootProductStatement`, and proves nothing.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.1.4, printed pp.4–8 (the
  logarithm of characters and the parameter notation `m^λ`); I.1.6, printed pp.10–12
  (restriction of characters and roots from the minimal torus to the split centre `T_M` of a
  standard Levi, the roots of `M` restricting trivially); I.1.13, printed p.18 (the half sums
  `ρ_0`, `ρ_P` of positive roots and the density `m^{-2ρ_P}` in the Iwasawa decomposition of the
  Haar measure); I.2.17, printed p.37 (`ρ_P` as the half sum of the roots on `Lie U`).
- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered
  as `delorme-2023-spectral-theorem-langlands` (published PDF numbering): §2, p.6 (`ρ_P^Q`
  defined by `|det Ad_P^Q(m)| = exp⟨2ρ_P^Q, H_P(m)⟩` for the adjoint action of `M_P` on the Lie
  algebra of `M_Q ∩ N_P`; with `Q = G` this is the action on `Lie N_P`, and `ρ = ρ_{P_0}`).

Provenance: derived. The statement is the standard computation of the modulus of a parabolic on
its split component by the weight decomposition of the Lie algebra: the determinant of the
adjoint action on `Lie P_J`, restricted to the split component, is compared with the product of
the positive roots outside the Levi, counted with the dimensions of their weight spaces. It is
written for the Library's `StandardParabolicFamily.halfModulus` (the parameter power
`a^{ρ_P}` with `ρ_P = halfModulusParameter`, half the adjoint determinant character of `P`) and
for the root product that defines `siegelModulus` (module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`).

## The statement

Let `F` be a number field, `G` an affine group scheme of finite type over `F` and
`𝓕 : StandardParabolicFamily F G` a compatible family of standard parabolics `P_J = M_J U_J`
for a maximal split torus `𝓕.i : T → G`, a generic cocharacter `𝓕.ν` and split components
`𝓕.a J : A_J → M_J` with `𝓕.f J : A_J → T`. Let `J` be a standard index and
`s ∈ A_J(𝔸)^+ = PositiveRealTorus.intrinsicSubgroup F (𝓕.A J)` a positive real point, with image
`a = PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s` in `P_J(𝔸)`.
Then

`‖𝓕.halfModulus J a‖² = ∏ᶠ_{β ∈ Φ⁺} |β(s)|^{m_β}`,

where `Φ⁺ = positiveRelativeRoots 𝓕.i 𝓕.ν`, `|β(s)| = PositiveRealTorus.normCharacter F (𝓕.A J)
(𝓕.f J ≫ β) s` is the idele norm of the restriction of `β` along `A_J → T` evaluated at `s`, and
`m_β = Module.finrank F (weightSpace 𝓕.i β)` is the dimension of the `β`-weight space of `T` on
the Lie algebra of `G`.

## Why it is true

`𝓕.halfModulus J a` is the positive square root of the idele norm of
`det(Ad(a) | Lie P_J)` (`StandardParabolicFamily.halfModulus_eq_sqrt`). The torus `T` acts on
`Lie P_J = Lie M_J ⊕ Lie U_J` with weights `0`, the roots in the span of `J` and the positive
roots outside that span, the latter exactly on `Lie U_J`, with the multiplicities `m_β` of
`Lie G`. The split component `A_J` is central in `M_J`, so every root in the span of `J` is
trivial on it. Hence `det(Ad(a) | Lie P_J) = ∏_{β ∈ Φ⁺} β(s)^{m_β}`, and taking idele norms gives
the statement.

## Use

The statement converts between the half modulus and root products on positive split-component
points. For a normalized exponent `ν` of a constant term along `P_J` and a dominant point
`a = exp X` of `𝔄_J`, Delorme's subunitarity condition (§2, p.6) gives `Re ν(X) ≤ 0`, so the
unnormalized exponential `e^{(ν + ρ_{P_J})(X)}` is bounded in absolute value by
`δ_{P_J}(a)^{1/2} = ‖𝓕.halfModulus J a‖`. Taking the square root of the identity gives
`δ_{P_J}(a)^{1/2} = ‖𝓕.halfModulus J a‖ = ∏_{β ∈ Φ⁺} |β(s)|^{m_β/2}`. For the minimal
parabolic, restriction to the positive torus of a Siegel setup identifies the full-exponent
product `∏_{β ∈ Φ⁺} |β(s)|^{m_β}` with `siegelModulus`; the half-exponent product there is
`siegelModulus^{1/2} = δ_{P₀}^{1/2}`. In the tempered estimate of Delorme's Proposition 4.1 (with (4.5)), the
common factor `δ_{P₀}^{1/2}` is an upper bound obtained by comparing the individual terms,
indexed by the standard parabolics `P`, of Mœglin–Waldspurger's Lemma I.4.1 (printed p.49); each
of those terms carries its own weight `m_{P₀}(g)^{Re π + ρ_P}`.

## Scope

Only positive real points of the split component are considered. Nothing is proved here.
