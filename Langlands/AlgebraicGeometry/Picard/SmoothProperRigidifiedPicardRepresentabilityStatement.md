# Full rigidified Picard representability for smooth proper pointed schemes

`Langlands.AlgebraicGeometry.Picard.SmoothProperRigidifiedPicardRepresentabilityStatement.{u}`
is a proposition definition. For every field `K : Type u`, every actual
`X : Over (Spec (CommRingCat.of K))` with smooth, proper and geometrically
connected structure morphism, and every actual section
`ε : Spec (CommRingCat.of K) ⟶ X.left` with `ε ≫ X.hom = 𝟙 _`, it asserts
the existence of an actual parameter scheme `P` over `K` and a bundle
`L : RigidifiedLineBundle.relative X.hom ε section_eq P` satisfying:

- `IsSeparated P.hom`;
- `LocallyOfFiniteType P.hom`;
- `RigidifiedLineBundle.IsUniversal X.hom ε section_eq L`.

The bundle is an actual locally free rank-one module sheaf on `P ×_K X`,
with an isomorphism from the structure sheaf of `P` to its pullback
along the section induced by `ε`. The imported `IsUniversal` requires
the canonical pullback classifying map to be bijective for every
`T : Over (Spec (CommRingCat.of K))`. By the imported `isUniversal_iff`,
for every actual rigidified line bundle `M` on `T ×_K X` there is a
unique `K`-morphism `h : T ⟶ P` such that the actual relative pullback
of `L` along `h` is isomorphic to `M` as a rigidified line bundle.
The uniqueness is of `h`; the predicate does not assert uniqueness of
the chosen compatible bundle isomorphism. Forgetting its rigidification
gives an actual isomorphism of the underlying module sheaves.

All test schemes are included, in particular nonreduced and
non-quasi-compact schemes. The field may be imperfect, is not required
to be algebraically closed, and has arbitrary characteristic. The
statement is polymorphic in every universe `u`: fields have type
`Type u`, and base, source, parameter and test schemes use
`Scheme.{u}`. The imported rigidified class quotients take values in
`Type (u + 1)`; no smallness restriction is imposed on their elements.

This is the full Picard classifier. No group structure on `X` or `P`,
projectivity, ample bundle, Picard-zero condition, representing scheme,
or universal bundle is assumed. The conclusion is local finite type;
it does not require the full parameter scheme to be quasi-compact or
of finite type.

## Sources and derived specialization

The principal source is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI (6.2), printed pp.88–89 (PDF pp.92–93), describes the
rigidified functor, its actual universal Poincaré bundle, and its
comparison with the fppf Picard sheaf under condition (*).
Paragraph (6.3)(iii), printed p.89 (PDF p.93), states scheme
representability, separatedness and local finite type for the Picard
sheaf of a proper scheme over a field. The draft attributes this
representability result to Murre, using Oort's reduction to the reduced
case; this file does not claim to formalize those proofs.

The present statement is a derived specialization, not a verbatim
statement of (6.3)(iii). Properness supplies quasi-compactness and
quasi-separatedness. Smoothness supplies flatness and local finite
presentation; together with properness it gives finite presentation.
Smoothness over a field also gives geometric reducedness, as in
Stacks Project, Lemma 33.25.4, [Tag 056T](https://stacks.math.columbia.edu/tag/056T).
Thus, with geometric connectedness, Stacks Project, Lemma 36.32.6,
[Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L), yields the
canonical isomorphism `O_T ≅ (p_T)_* O_(T ×_K X)` after every base
change `T → Spec K`. This is the universal structure-sheaf condition
in (6.2), including for arbitrary nonreduced and non-quasi-compact `T`.
The actual section supplies the remaining part of condition (*).

The supplementary retained sources are:

- `stacks-global-functions-field-and-fibre-criterion-2026-10-23`,
  directory SHA-256
  `c170b7f07df230ebbd77e6b3dc8774e0061520328c065c87cfd45554d2ddb850`,
  file `056T.html`, Lemma 33.25.4, statement and proof;
- `stacks-relative-global-functions-0e0l-2026-10-22`,
  directory SHA-256
  `4f31e85523053c46b315dc46c77b611347154add7f98d9d89a57a748f3e85b87`,
  file `0E0L.html`, Lemma 36.32.6, statement and proof.

The retained principal PDF and both supplementary statements and proofs
were checked. No source-specific errata file was found in the project
or Library notes at authoring; the retained Stacks pages have no
correction comments. The Library uses `T ×_K X`, canonically symmetric
to the source's `X ×_K T`, and the same direction for rigidification,
from the structure sheaf to the section pullback.

## Proof boundary

This file supplies a statement, not a proof or an axiom. The universal
structure-sheaf theorem, the canonical rigidified/fppf comparison, and
Picard-sheaf representability remain proof obligations, not additional
hypotheses. A proof must recover an actual universal rigidified bundle
from those results and show that its classifying map is exactly the
existing canonical pullback map on every test scheme. An abstract
equivalence on field-valued points would not establish this proposition.
The full existence result is separate from the abelian-variety
specialization and from statements about the Picard identity component.
