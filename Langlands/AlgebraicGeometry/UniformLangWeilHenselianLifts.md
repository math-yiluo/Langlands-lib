# Uniform Henselian integral-point lifts

Author: Worker 208.

This derived construction combines the finite-field application of
Lang–Weil with smooth Henselian lifting in Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Theorem 4.5,
printed p.12 third proof paragraph and p.13 last paragraph. The full
uniform estimate of Lemma 4.6, printed pp.12–13, remains an explicit
parameter. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`uniformLangWeilLargeHenselianPointLifts` constructs a positive real
constant `C` uniform in every commutative Henselian local ring `R`, every
finite field quotient `K` presented by a surjective algebra map `R → K`,
and every prescribed morphism `p : Spec R ⟶ B`. If `C² < #K`, it returns
an actual morphism `a : Spec R ⟶ Y` together with `a ≫ f = p`.
All rings, fields and schemes lie in an arbitrary common universe.
There is no valuation, topology or completeness hypothesis on `R`.

The geometric hypotheses are those of `UniformLangWeilStatement`: `B`
is locally of finite type over the universe-lifted integers and has compact
underlying space; `f : Y ⟶ B` is smooth, separated, surjective, locally of
finite type, quasi-compact and geometrically connected, with all fibres
of pure dimension `d`. Neither scheme is required to be affine or
separated over the integers. The chosen constant depends on this fixed
family and dimension, before any of the local data are supplied.

The implementation first applies
`uniformLangWeilLargeFiniteFieldPointLifts` to choose `C`. For each
integral point `p`, reduce it along the actual spectrum map `Spec K → Spec R`.
The finite-field construction gives a `K`-point of `Y` above that complete
reduced morphism. Then
`PointTopology.exists_smooth_lift_of_residue_point` lifts this chosen
residue point over the prescribed `p`. Its exact equality over `B`
supplies the output subtype. The published Henselian theorem additionally
preserves the chosen residue point, although this constructor's output
records only the required equality over `B`.

`PointTopology.uniformLangWeilLargeHenselianRingPointLifts` retains any
commutative original coefficient ring `C`, models `B` and `Y` in
`Over (Spec C)` and an actual model morphism `f`. Its geometric hypotheses
are imposed on the underlying schemes and morphism exactly as above;
in particular the underlying base model must still be locally of finite
type over the integers and compact. The output is a positive constant
followed by actual relative lifts over every Henselian `C`-algebra `R`
with a sufficiently large finite field quotient presented by a surjective
`C`-algebra map `φ : R → K`.

For this version, use `φ` to supply the `R`-algebra structure on `K` and
apply the scheme constructor. The base equation for the resulting lift
follows from its equality after composition with `f` and the existing
base equation for `p`. `Over.homMk` therefore gives a point in the
unchanged `RingPoint C Y R` type, and `RingPoint.ext` proves `a ≫ f = p`.
The constant is again chosen before the rings, quotient and point.

These constructors introduce no auxiliary point presentation and no
assumed point-surjectivity field. They are conditional on the full
uniform estimate. They do not prove that estimate, compatible spreading,
cofinite cardinal growth at global places, or the remaining adelic
openness argument.
