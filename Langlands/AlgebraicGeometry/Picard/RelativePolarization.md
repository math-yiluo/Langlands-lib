# Relative polarizations on geometric fibres

`IsPolarization` is a predicate on an actual abelian-scheme homomorphism
`lam : A → A^dual`, where the target is the previously constructed
`dualAbelianSchemeFromEvaluation`. It requires:

- `lam` is an isogeny, meaning its underlying scheme morphism is finite,
  flat and surjective.
- For every algebraically closed field `K` and every geometric point
  `s : Spec K → S`, the actual base change of `lam`, followed by the
  canonical Poincare-compatible dual comparison, satisfies
  `HasFieldAmpleMumfordPresentation`.

The second condition means that, after some field extension of `K`, that
map is the normalized Mumford classifier of an ample line bundle on the
actual changed abelian scheme. It uses the existing field definition,
including genuine inverse bundles and their evaluation isomorphisms in
the ample presentation. Ampleness is imposed on the original line bundle.
The comparison is uniquely determined by the actual Poincare pullback;
no arbitrary identification of the fibre dual is supplied. Geometric
points and the subsequent field extensions use the same universe as the
schemes. The base scheme is otherwise arbitrary.

`IsPrincipalPolarization` additionally requires `IsIso lam` in the actual
abelian-scheme category.

## Connection with the field-polarization predicate

`IsPolarization.geometricFibre` proves that the geometric-fibre condition
gives `IsFieldPolarization` for the actual transported abelian-scheme
homomorphism `dualAbelianBaseChangeMap`. The theorem takes the explicit
`DualAbelianBaseChangeStatement` compatibility input, the fibre dual's
actual universal-family and geometric properties, and an inverse of its
Poincare line bundle with evaluation. It holds for every such set of
inputs. These are exactly the inputs needed to construct that fibre dual
as an abelian scheme and to lift the canonical scheme comparison.

The proof first obtains the isogeny on the fibre from stability under
actual base change and composition with the comparison isomorphism. It
uses the existing group-scheme result that isomorphisms are isogenies.
The ample-presentation conjunct follows by rewriting the underlying map
with `dualAbelianBaseChangeMap_hom` and applying the geometric-fibre clause
of `IsPolarization`. Thus the isogeny is required globally once; it is
proved on each constructed fibre, not omitted from the field condition.

## Sources and scope

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5
(1992), Section 5, printed p.390 (PDF18), describes a polarization as an
isogeny to the dual which is a polarization at every geometric point.
His PEL moduli problem additionally restricts to locally noetherian bases,
projective abelian schemes and prime-to-`p` isogenies. This file isolates
the general polarization predicate required by the host task; it does not
assert those extra moduli restrictions or a representability theorem.

The field criterion is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
preliminary draft, Chapter XI, Corollary (11.5)(b1) and Definition (11.6),
printed p.160 (PDF164). It requires an ample Mumford presentation after
some field extension, together with the isogeny condition; the same
definition calls a polarization principal when it is an isomorphism.
`FieldPolarization` implements this criterion and is reused here.

The tensor, square, universal-family base-change and group construction
inputs are explicit throughout. The geometric-fibre theorem also makes
group compatibility explicit. This file proves neither unconditional
existence of duals or inverse Poincare bundles nor the separately named
compatibility theorem. It asserts no base-change stability of the whole
relative predicate, independence of inverse choices, equivalence with
other polarization criteria, or existence of polarizations.
