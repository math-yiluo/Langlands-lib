# Gelfand–Kazhdan realization of the smooth contragredient

`Langlands.GelfandKazhdanContragredientStatement.{uF,uV}` is a `Prop`-valued
definition; this module proves nothing. The proposition is proved by the
published theorem `Langlands.gelfandKazhdanContragredient` in
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof` (see
Status below). For every prime `p`, finite p-adic extension
`F : PadicField.{uF} p`, natural number `n`, and complex representation
`rho` on `V : Type uV` of the actual group `GL_(n+1)(F)`, it asserts:
if `rho` is admissible and irreducible, there is a complex linear equivalence
`E : V ≃ₗ[ℂ] SmoothDual rho` such that, for every `g` and `v`,

`E (rho ((g inverse) transpose) v) = smoothContragredient rho g (E v)`.

The field topology is installed from `F.canonicalNormedField`, and the group
uses Mathlib's actual matrix-units topology. The field and vector-space
universes are independent. There is no topology or finite-dimensionality
assumption on `V`. Rank one is included, and rank zero is excluded by the
`n + 1` indexing. No Whittaker functional, additive character, genericity
hypothesis, chosen equivalence, or character-equality assumption is present.
The equivalence is existential; the statement assigns it no normalization.

The imported `IsAdmissible` includes smoothness and finite-dimensional fixed
vectors for every open subgroup, using the Library's all-open-subgroups
convention. In particular it supplies the compact-open fixed-vector condition
of the source. `SmoothDual rho` is the smooth-vector submodule of the full
algebraic complex dual, with action
`(smoothContragredient rho g ell)(v) = ell (rho (g inverse) v)`.
It is neither the full algebraic dual nor a renamed inverse-transpose pullback.
`GeneralLinear.inverseTranspose` is the existing involutive group automorphism
whose underlying matrix is exactly `(g inverse).val.transpose`.

## Source and convention comparison

The principal source is Bernstein and Zelevinsky, *Representations of the group
GL(n, F), where F is a non-Archimedean local field*, Russian Mathematical
Surveys 31:3 (1976), 1–68, registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

Sections 2.13–2.15, printed/PDF pages 19–20, define the contragredient as
the smooth part of the algebraic dual with inverse action and give its
admissibility, biduality and irreducibility properties. Sections 2.17–2.20,
page 21, define the distribution character using finite-rank integrated
operators and distinguish irreducible admissible representations by that
character. Section 2.27, page 23, fixes the pullback convention
`rho^sigma(g) = rho(sigma(g))`.

Sections 7.1–7.3, pages 57–58, state the Gelfand–Kazhdan equivalence for
`rho^s`, where `s(g) = s_r theta(g) s_r inverse`, `r = n + 1`,
`theta(g) = (g inverse) transpose`, and `s_r` is the source's signed
anti-diagonal matrix. The conclusion in this Lean proposition removes that
inner conjugation. Explicitly, the invertible operator `I = rho(s_r)` obeys

`I (rho(theta(g)) v) = rho(s(g)) (I v)`.

Indeed both sides are `rho(s_r theta(g)) v`. Thus, if `E_s` intertwines
`rho^s` with the smooth contragredient as in Theorem 7.3, then
`E = E_s composed with I` has exactly the displayed equivariance in the Lean
statement. Conversely, composing `E` with `I inverse` gives `E_s`.
This is an elementary convention conversion, not an extra hypothesis or an
identification of the signed matrix with the unsigned long Weyl matrix.
The present module records only the resulting proposition. The deep theorem
is proved in a separate module (see Status below). That proof establishes the
displayed inverse-transpose form directly, so this explanatory conversion is
not formalized in the Library.

The consumer convention is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Section 2.1, page 386, equation (4), uses the unsigned-long-Weyl transformed
Whittaker function `W_tilde(g) = W(w_r g^iota)`, and the following
irreducible paragraph identifies `pi^iota` with the contragredient.
That paragraph is the generic consumer of the stronger Bernstein–Zelevinsky
theorem. The unsigned Weyl factor in a transformed Whittaker function is not
part of the automorphism `theta` used in this statement. The cited source
pages were read, including visual checks of BZ page 57 and JPSS page 386.

## Status and dependencies

This module defines one `Prop`-valued target and proves no representation
equivalence. The original proof uses equality of distribution characters,
conjugation invariance, invariance under transposition, and character
separation. None is assumed as an axiom or supplied by defining this target.

The published theorem
`Langlands.gelfandKazhdanContragredient : GelfandKazhdanContragredientStatement.{uF,uV}`,
in `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`, proves
exactly this proposition, with the same independent universes and no added
hypothesis. It follows the character route: the conditional assembly
`Langlands.gelfandKazhdanContragredient_of_character_inputs` (module
`GelfandKazhdanAssembly`) is applied to the published theorems
`Langlands.characterSeparation` and
`Langlands.generalLinearConjugationDistributionTranspose`. That proof module
describes the argument. The equivalence it supplies is existential and carries
no normalization.

The module reuses `Langlands.Group.GL.Maps` and
`Langlands.Representation.Smooth.Contragredient.Definitions`; their imports
supply the actual p-adic fields, inverse transpose, admissibility and smooth
dual. Mathlib supplies complex scalars, representations and irreducibility.
No existing statement or imported definition is changed. In particular,
`GenericContragredientStatement` retains its genericity hypothesis and its
additional inverse-character Whittaker-functional conclusion. Its published
proof `Langlands.genericContragredient` (module
`Langlands.Representation.Whittaker.GenericDualProof`) uses the proved
realization theorem and transports the Whittaker functional separately. The
present statement makes no assertion about Whittaker functionals.
