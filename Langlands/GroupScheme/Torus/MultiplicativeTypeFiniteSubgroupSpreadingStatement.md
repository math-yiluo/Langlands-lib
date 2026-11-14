# Statement: closed subgroups of groups of multiplicative type with a finite fibre

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `IsFinite`.

`GroupScheme S` is `Grp (Over S)`. For a homomorphism `k : K ⟶ H` in it,
`k.hom.hom.left : K.X.left ⟶ H.X.left` is the underlying morphism of schemes. The scoped
notation of `CategoryTheory.MonObj` is open, so for every test object `T` the set of
morphisms `T ⟶ K.X` (the group `K(T)` of `T`-points of `K`) carries the group structure
induced by the group law of `K`, `1` is its unit and `x ^ n` is the `n`-th power in it.

## Objects and predicates used

- **Closed subgroups.** A closed subgroup scheme `K` of `H` (a *sous-préschéma en groupes
  fermé*) is represented by a homomorphism `k : K ⟶ H` with
  `IsClosedImmersion k.hom.hom.left`, that is, an isomorphism of `K` onto a closed
  subscheme of `H` that is stable under the group law.
- **Finite presentation.** `LocallyOfFinitePresentation K.X.hom`, `QuasiCompact K.X.hom`
  and `QuasiSeparated K.X.hom` together say that `K` is of finite presentation over `S`.
- **Fibres.** `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism
  from the spectrum of the residue field `κ(s)` at a point `s ∈ S`, and
  `K_s := (GroupScheme.baseChange (S.fromSpecResidueField s)).obj K` is the fibre of `K`
  at `s`, a group scheme over `κ(s)`.
- **Restriction to an open.** For an open `U : S.Opens`, `U.ι : U ⟶ S` is the open
  immersion of `U` and `K_U := (GroupScheme.baseChange U.ι).obj K` is the restriction
  `K|_U`, a group scheme over the scheme `U.toScheme`.
- `IsFinite K_s.X.hom` says that `K_s` is finite over `κ(s)`; `IsFinite K_U.X.hom` says that
  `K_U` is finite over `U`.
- **Containment in `ₙH`.** For `n > 0`, SGA 3 writes `ₙH` for the kernel of `n · id_H`; its
  `T`-points are the `y ∈ H(T)` with `y ^ n = 1`. The condition
  `∀ (T : Over U.toScheme) (x : T ⟶ K_U.X), x ^ n = 1` says that every point of `K_U` is
  `n`-torsion. Since `k` is an injective homomorphism on points, this is the same as
  saying that the image of every point of `K_U` in `H_U` lies in `ₙ(H_U) = (ₙH)|_U`, that is,
  that `K|_U` is contained in `ₙH|_U` as a subscheme of `H|_U`.
- **Unit group.** `IsIso K_s.X.hom` says that the structure morphism `K_s → Spec κ(s)` is
  an isomorphism, that is, `K_s` is the unit group over `κ(s)`. Likewise
  `IsIso K_U.X.hom` says that `K|_U` is the unit group over `U`.
- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms locally of finite presentation) over each
  member of which `H` becomes isomorphic to `D(Λ)` for a finitely generated abelian group
  `Λ`.

## Statement and quantifiers

For every scheme `S : Scheme.{u}`, all `S`-groups `H, K` and every homomorphism
`k : K ⟶ H` such that `H` is of multiplicative type, `k` is a closed immersion and `K` is
of finite presentation over `S`, and for every `s ∈ S`:

1. **(6.4)** if `K_s` is finite over `κ(s)`, there are an open `U ∋ s` and an integer
   `n > 0` such that every point of `K|_U` is `n`-torsion and `K|_U` is finite over `U`;
2. **(6.5)** if `K_s` is the unit group, there is an open `U ∋ s` such that `K|_U` is the
   unit group.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Théorème 6.4, p.54 (margin 66): "Soient S un préschéma, H un S-groupe de type
  multiplicatif et de type fini, K un sous-préschéma en groupes fermé, de présentation finie
  sur S. Soit s ∈ S tel que K_s soit fini. Alors il existe un voisinage ouvert U de s tel que
  K|U soit contenu dans ₙH|U pour un certain n, et a fortiori (ₙH étant fini sur S) tel que
  K|U soit fini sur U."
- Corollaire 6.5, p.54 (margin 66): "Avec les notations précédentes, supposons que K_s soit
  le groupe unité. Alors il existe un voisinage ouvert U de s tel que K|U soit le groupe
  unité."
- Théorème 4.7, p.47, defines `ₙG` as "le noyau de n · id_G".

SGA 3 derives 6.4 from Lemme 6.1 (a commutative quasi-finite group of finite presentation
over a quasi-compact base is killed by some `n > 0`) and Lemme 6.3 (local quasi-finiteness
spreads from the unit point of a fibre), and 6.5 from 6.4 by Nakayama's lemma. This is
explanation only.

Brian Conrad, *Reductive group schemes* (registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), Definition B.1.1,
p.280, is the source of the predicate `IsMultiplicativeType`.

## Derivation from the source

- **Base and groups.** "S un préschéma" is an arbitrary scheme `S : Scheme.{u}` (Mathlib's
  schemes are not assumed separated, matching *préschéma*). "H un S-groupe de type
  multiplicatif et de type fini" is `IsMultiplicativeType H` (see Scope).
- **"K un sous-préschéma en groupes fermé, de présentation finie sur S".** A closed
  immersion `k : K ⟶ H` of group schemes, with `K → S` locally of finite presentation,
  quasi-compact and quasi-separated (finite presentation in the sense of EGA IV₁, 1.6.1,
  which SGA 3 follows).
- **Fibres and restrictions.** `K_s` is the base change of `K` along `Spec κ(s) → S`, and
  `K|U` the base change along the open immersion `U.ι`. "Un voisinage ouvert U de s" is an
  open `U : S.Opens` with `s ∈ U`. "K_s fini" means finite over `κ(s)`.
- **"K|U contenu dans ₙH|U pour un certain n".** Some `n > 0` such that every point of
  `K|U` is `n`-torsion, as explained above. The source's "a fortiori … K|U soit fini sur U"
  is included as the conjunct `IsFinite K_U.X.hom`.
- **"Le groupe unité".** The unit group over a base is the group whose structure morphism is
  an isomorphism; this is the meaning of `IsIso K_s.X.hom` and `IsIso K_U.X.hom`.

## Scope and omissions

- **Class of groups of multiplicative type.** SGA 3, IX, 1.1 defines groups of
  multiplicative type as fpqc-locally diagonalizable, with possibly infinitely generated
  character groups. The predicate used here is Conrad's Definition B.1.1 (fppf-locally
  `D(Λ)` with `Λ` finitely generated). Conrad notes after Definition B.1.1 (p.280) that
  these are precisely the groups of multiplicative type of SGA 3 whose structure morphism is
  of finite type, deducing this from his Corollary B.4.2(1), p.299 (fpqc-local diagonalizability
  implies fppf-local diagonalizability for fppf groups). The source's hypothesis "de type multiplicatif et de type fini" is
  therefore exactly `IsMultiplicativeType H`, and the two parts are the full statements of
  6.4 and 6.5.
- All schemes are in universe `u`.
- Not stated here: Lemmes 6.1, 6.2 and 6.3.
