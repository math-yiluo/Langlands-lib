# Transport of the geometric coefficient realization along CM level maps

`HarrisCMGeometricCoefficientLevelComparisonStatement` compares the actual
Harris coefficient cohomology at each represented small CM level with the
projector-selected cohomology of the universal abelian powers. The CM
datum has division algebra `A`. The finite-dimensional algebraic
coefficient representation over the number field `K` is absolutely
irreducible, in the sense that its action on `W` extended to the
algebraic closure of `K` is irreducible on the similitude group over
that closure. The ordinary scalar exponent is `−w`, so transport to the
right frame group gives scalar exponent `w`.

The cohomology uses the algebraic closure `Λ` of the finite completion
at the specified coefficient place over the rational place `p`.
Representability at all small levels supplies the schemes and
universal classes. The PEL and base-change inputs include the Picard
and tensor pullback comparisons, compatibility of the finite Weil
pairings and finite étaleness of torsion. The actual coefficient
functor also uses relative dual existence and geometry and geometric
coarse-level rigidity at each small level. The derived-category
localization choices are for the two coefficient rings and their
small-étale module sheaves.

One pair of nonnegative integers `m` and `t` satisfying `2t−m=w` and
one projector expression over `Λ` apply to every level and connected
component. Each evaluated projector is idempotent in every total
degree. For each degree `i`, the statement gives linear equivalences
between coefficient cohomology in degree `i` and the product of the
componentwise projected constant-coefficient groups in degree `i+m`,
with cyclotomic twist `+t`. These equivalences intertwine the Galois
actions and the actual pullbacks for all level transporters, including
both legs of the Hecke span.

For a transporter from level `U` to `V`, let `α` be the rational polarized
isomorphism from the chosen abelian representative over a component of `U`
to the pullback of the representative on its image component of `V`. Its
multiplier `a` satisfies `α*λ_V = a λ_U`. The component pullback is the
pullback on the actual abelian powers with the denominator correction in
degree one in each factor, multiplied by `a⁻ᵗ`. To see the latter factor,
write the target frame as `α η_U g` after transporting it to the image
geometric point. If `c_U` is the scalar of the Weil pairing at `η_U`, the
target scalar is `a c_U ν(g)` for the pairing similitude `ν(g)`. Pulling
back the tensor of degree-one classes gives the dual action of `g`, and
its product with `ν(g)^t` is the transported action on the Tate-twisted
coefficient representation. Removing `a^t` gives the pullback on that
coefficient sheaf. The displayed comparison uses the actual scaled
coefficient transport and its rational normalization in the level
cohomology functor.

Under the fixed-vector comparison for the actual tower in degree `i`,
the same family also compares transfer. For a normal inclusion `V ≤ U`,
pullback is injective and the trace followed by that pullback is the sum
of the actual `U/V` deck pullbacks. The statement gives this equation
both in coefficient cohomology and componentwise after applying the
geometric equivalences. Thus the component equation characterizes the
transferred class in the projected image.

For a double coset with original transporter `g`, take the Hecke
intersection `M` and any small `N ≤ M` normal in `U`. The compact open
normal refinement of `M` inside `U` gives one such `N`. The geometric
formula is the translating pullback to `N` followed by the trace to `U`
and divided by `[M:N]`. In the deck sum indexed by `U/N`, each term of the
sum over `U/M` occurs `[M:N]` times. The resulting operator equals the
Library's unnormalized double-coset operator on actual tower fixed
vectors, transported to level cohomology. For that operator, the ordinary
adelic element is `(unop g)⁻¹`. The characteristic-zero coefficient field
allows division by the finite index.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp. 90–91 (PDF pp. 98–99), gives the frame orbit,
polarized isogeny equivalence and right translation. III.2, printed
pp. 94–96 (PDF pp. 102–104), gives coefficient descent and the translating
map. Its relative Künneth projector, Leray degree shift and Tate twist are
on printed pp. 97–99 (PDF pp. 105–107). Literature ID
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

The trace formula for finite étale maps is Milne, *Étale Cohomology*
(1980), V.1, Lemma 1.12, printed pp. 168–169 (PDF pp. 182–183).
Literature ID `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.
Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
§6, printed pp. 392–393 (PDF pp. 20–21), describes the two legs and their
coefficient identifications. Literature ID
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
