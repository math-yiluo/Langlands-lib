# A uniform exponent for quasi-finite commutative group schemes

`Langlands.GroupScheme.quasiFiniteCommutativeUniformExponent.{u}` proves
`Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentStatement.{u}`
in every scheme universe. If \(S\) is quasi-compact and \(K\) is a
commutative \(S\)-group scheme of finite presentation with locally
quasi-finite structure morphism, there is one positive integer \(n\)
such that \(x^n=1\) for every \(S\)-scheme \(T\) and every \(x\in K(T)\).

The result is SGA 3, Exposé IX, Lemma 6.1, whose proof continues through
Lemma 6.2, printed pp.52–54 (retained PDF pp.22–24), registered as
`sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
Worker 887 supplies the locality, approximation, directed-family organization,
dimension induction and final assembly. Worker 801 supplies the Artinian
exponent, adic support separation, local geometric exhaustion and
stalk-to-global fullness.

Over a local Artinian base, quasi-compactness and local quasi-finiteness make
the group scheme finite. The theorem for finite group schemes over a field
supplies one positive exponent on its residue fibre. In residue
characteristic \(p>0\), the maximal ideal is nilpotent and contains \(p\).
Taking a \(p\)-th power moves a point in the kernel of reduction modulo
one power of the extended ideal into the kernel for the next power. A
bound on the nilpotence of the maximal ideal therefore gives one exponent
\(p^N\) for the kernel of reduction in every coefficient algebra.
Multiplying the residue exponent by \(p^N\) gives the desired exponent. In residue
characteristic zero, reducedness of the finite residue Hopf algebra, base
change of Kähler differentials and Nakayama's lemma give formal
unramifiedness. Uniqueness of lifts across the nilpotent ideal then gives
the identity with the residue exponent itself. Evaluating at the universal
affine point gives the identity on every test scheme.

For a finite-type quasi-finite scheme over a noetherian local base, a directed
subscheme family that is full on the punctured base and on every canonical
closed-point thickening has a full stage. Here a stage is full if its
immersion is an isomorphism. A common stage of punctured and special-fibre
fullness is a surjective closed immersion. Its defining ideal is supported
over the closed point. On a finite affine cover, Artin–Rees gives a
sufficiently high power of the extended maximal ideal whose intersection
with this defining ideal is zero. A later stage full modulo that power has
zero defining ideal. For the global step,
`ImmersionExhaustion.Family.full_of_stalk_full` spreads an isomorphism
stage from each stalk to a principal open in an affine neighborhood of the
base point. The pullbacks of those opens cover the quasi-compact ambient
scheme, and directedness gives a common stage for a finite subcover.
`ImmersionExhaustion.exhaustion_of_stalkLocality` uses this step in strong
induction on local ring dimensions, applying the smaller-dimensional case
on each punctured spectrum. The argument chooses a dimension bound
separately on the spectrum of each base stalk.

Apply this exhaustion theorem to the actual scheme-theoretic equalizers of
multiplication by `i!` and the constant unit map of the commutative group.
They form an increasing sequence of immersions, including when the group
is not separated. The Artinian theorem makes this sequence full after every
local Artinian base change. A full equalizer therefore gives a positive
factorial exponent on all points.

Finally, general finite-presentation scheme descent, descent of the full group
law and commutativity, and descent of zero-dimensional fibres reduce an
arbitrary affine coefficient ring to a noetherian one. A finite affine cover
of the original quasi-compact base gives finitely many positive exponents;
their product kills all points globally. Equality of multiplication by the
product with the constant unit homomorphism glues by the locality of
group-scheme homomorphisms.

The exhaustion argument uses local finite type, in accordance with the
source's convention in footnote 41. The original target supplies it
through local finite presentation.
