# Proof of two-axis rigidity over an algebraically closed field

Authors: Worker 423 implemented the proof. Worker 334 supplied the proof route:
replace the Mathlib commutator by the arbitrary map and use its graph.

## Result and scope

`Langlands.AbelianScheme.algebraicallyClosedTwoAxisRigidity.{u}` has exact type
`Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidity.{u}` for every universe
`u`. It imports the published statement unchanged from
`Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidityStatement`.

For an algebraically closed field `K`, write `S = Spec K`. Given schemes
`A,H` over `S`, the assumptions are properness of `A → S`, integrality of
`A ×_S A`, and separatedness and local finite type of `H → S`. For sections
`a : S → A` and `b : S → H`, any morphism `g : A ×_S A → H` taking value
`b` on both axes through `a` equals the constant morphism with value `b`.
These are precisely the quantified data and implication hypotheses of the
published proposition.

The proof uses no group object, multiplicativity assumption, or properness of
`H`. It does not depend on the project's pointed-morphism rigidity results over
fields or arbitrary bases.

## Implemented proof

Set `p = pr₁ : A ×_S A → A` and
`γ = (pr₁,g) : A ×_S A → A ×_S H`; let `q` denote the first projection
`A ×_S H → A`. The section `a` gives a point of `A`, so `A → S` and
its base change `p` are surjective. Properness of `A → S` makes `p` and
the structure map of the square proper. The latter also gives the square its
Jacobson-space structure. Since `q` is separated and `γ ≫ q = p`, `γ` is
proper, even though the target `H` need not be proper.

Let `s` be the unique point of `S`. The section `a` is a closed immersion.
The map `(a,b) : S → A ×_S H` is also a closed immersion because its
composition with the separated morphism `q` is `a`. These facts make the
sets in the following closed-point argument locally closed.

First, the image under `γ` of the fibre `p⁻¹(a(s))` is contained in the
singleton `{(a,b)(s)}`. If a counterexample existed, the Jacobson property
would supply a closed counterexample point. Algebraic closedness identifies
it with a `K`-rational point `c` of the square. The equality of its first
coordinate with `a(s)` implies equality of the corresponding rational-point
morphisms, by `ext_of_apply_closedPoint_eq`. Thus `c` factors through the
first axis `a ▷ A`. The first axis equation then gives the asserted value,
contradicting the choice of `c`.

Apply
`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`
to `γ` and `q`. Its hypotheses follow from properness of `γ`,
separatedness and local finite type of `q`, and the finite image just proved.
It produces an open neighborhood `U` of `a(s)` on which the scheme-theoretic
image of `γ` is finite over `U`. Properness makes the set-theoretic image
closed, so for each `x ∈ U`, the intersection
`q⁻¹(x) ∩ range γ` is finite.

It remains to compare `g` with the constant morphism on closed points of
`p⁻¹(U)`. This set is nonempty by surjectivity of `p`, and is dense because
the square is irreducible. For a closed point `y` in it, `x = p(y)` is
closed by properness of `p`, and hence gives a rational section of `A`.
The fibre `p⁻¹(x)` is the image of the irreducible square under the map
`(z,w) ↦ (x,w)`, and is therefore preirreducible. Its image under `γ` is
finite by the preceding paragraph. The lemma
`subsingleton_image_closure_of_finite_of_isPreirreducible` forces
`γ(y) = γ(x,a)`. Taking second projections gives `g(y) = g(x,a)`, and
the second axis equation identifies the latter value with the value of the
constant morphism `b`.

Finally, `ext_of_apply_eq` upgrades equality on those dense closed points to
equality of scheme morphisms. Its hypotheses use reducedness of the integral
square, finite type of its structure map, and separatedness and local finite
type of `H → S`. Extensionality in `Over S` gives the requested conclusion.

## Provenance and attribution

This is a direct geometric proof of the published derived statement. Its
implementation adapts Andrew Yang and Christian Merten's proof of
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
in Mathlib `Mathlib/AlgebraicGeometry/Group/Abelian.lean`, lines 37–127,
at commit `5ed2965256430c3649e86755f9576b54eca72435`. The source is registered
as `mathlib-abelian-5ed296525643`, with SHA256
`4849f7c4571be20d1674c8e1f20d7ed3efbcd8a5cc25ba7390c8dfd374be7fea`.
The original copyright and Apache 2.0 attribution are retained in the Lean
header. The implemented proof imports only the needed algebraically closed
field and Zariski Main infrastructure, alongside the published statement.

The change from the upstream argument is mathematical as well as notational:
the graph target is `A ×_S H`, the two given axis equations replace the
commutator identities, and the second axis is compared within the source
before applying `γ`. The original-source justification of the statement is
recorded in its existing companion Markdown; this proof follows the separate
finite-image route described above.
