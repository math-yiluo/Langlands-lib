# The Bernstein component of a non-self-associate supercuspidal of a maximal Levi

Author: Worker 6. Module `Langlands.Representation.Exponents.MaximalLeviBlockStatements`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. It contains one **statement**,
the closed `Prop`-valued definition `MaximalLeviBlockStatements` (universe parameters
`u, v`), a conjunction of three parts. It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
**9 July 2026**:

- VII.1.3, Corollary, printed p.226 / PDF p.232, with the setting and Theorem of VII.1.3,
  printed pp.224–226 / PDF pp.230–232;
- VI.7.1, the inertial support `Si` and the sets `Irr(G)_Ω`, printed p.181 / PDF p.187;
- VI.7.2, the full subcategories `M(G)_Ω`, printed pp.181–182 / PDF pp.187–188.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 6 read
PDF pages 187–188 and 230–232.

The Corollary reads: "Soit `P = MN`, avec `M` sous-groupe de Levi maximal de `G`. Posons
`W(M, *) = {1, w}` et soit `D` une classe d'inertie de représentations supercuspidales de
`M` telle que `w · D ≠ D` (c'est le cas par exemple si `w · M ≠ M`). Soit `Ω` la composante
connexe de `Ω(G)` associée à `(M, D)`. Alors

- (i) `i_P^G` envoie les représentations de `D` (c'est-à-dire les représentations
  irréductibles de `M(M)_D`) dans les représentations irréductibles de `M(G)_Ω`.
- (ii) Soit `r_D` la composition du foncteur `r_P^G` et de la projection sur `M(M)_D`.
  Alors `r_D` est un foncteur fidèle de `M(G)_Ω` vers `M(M)_D`.
- (iii) Pour toute représentation `(π, V)` dans `M(G)_Ω`, le morphisme naturel
  `π → i_P^G r_D(π)` est un isomorphisme. Le foncteur `r_D : M(G)_Ω → M(M)_D` est une
  équivalence de catégories dont l'inverse est `i_P^G`."

By VI.7.2, `M(G)_Ω` is the full subcategory of the representations all of whose irreducible
subquotients lie in `Irr(G)_Ω`, the fibre of the inertial support over the class of `Ω`.

## Lean model

The setting is that of the published VII.1.3 Theorem statement
[MaximalLeviSupercuspidalReducibilityStatement](MaximalLeviSupercuspidalReducibilityStatement.md):
a nonarchimedean local field `k : Type u`, a connected reductive `G` over `Spec k` with the
canonical topology on `G(F)`, and every actual rational parabolic `p : P ⟶ G` with rational
Levi `l : M ⟶ P`, matching radical `r : U ⟶ P` and `hmul`, which is proper (`¬ IsIso p`)
and maximal (no actual parabolic lies strictly between `P` and `G`). The topology and the
derived instances on `M(F)` are those of the Theorem. Induction is the published
`leviInductionFunctor p l r hp hr hl hmul`, Renard's `i_P^G` from smooth representations of
`M(F)`; the normalized Jacquet functor with values in representations of `M(F)` is the
published `leviJacquetFunctor p l r hp hr hl hmul`. Unramified characters are the published
`Plancherel.unramifiedCharacters` of the rational norm characters of `M`, as in the Theorem.

All smooth representations have carriers in `Type (max u v)`, so the categories of `M(F)`
and of `G(F)` are taken in one universe that contains the field's; induction does not
enlarge it.

The statement fixes `ρ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)`, irreducible and
supercuspidal in the sense of the Theorem (every normalized Jacquet module of `ρ` for an
actual proper parabolic of `M` is zero). Its inertial class is `D`.

- **The hypothesis `w · D ≠ D`.** There are no `g : G(F)`, automorphism `φ : M ≅ M`,
  unramified `ψ` and linear equivalence `T : ρ ≃ₗ[ℂ] ρ` such that conjugation by `g`
  preserves the image of `M` and induces `φ` (`φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom`),
  `g ∉ pointImage (l ≫ p)`, and `T (ρ m x) = ψ(φ(m)) • ρ(φ(m)) (T x)`. As explained in the
  Theorem's Markdown, the last identity says `ρ^g ≃ ρψ`, and an element `g ∉ M(F)`
  normalizing `M` exists exactly when `w · M = M`, in which case `g` represents `w`. So the
  hypothesis says: either `w · M ≠ M`, or `ρ^w` is not an unramified twist of `ρ`. Since
  `ψ ∘ φ` is again unramified, this is `w · D ≠ D`.
- **`IsTwist σ`** (a `let` in the statement) means that some unramified `ψ` and linear
  equivalence `T : ρ ≃ₗ[ℂ] σ` satisfy `ψ(m) • T (ρ m x) = σ m (T x)`, that is
  `σ ≃ ρ ⊗ ψ`. The members of `D` are the representations with `IsTwist`.
- **`InBlockM X`** means that every irreducible `σ` with `SmoothRep.IsSubquotient σ X` has
  `IsTwist σ`. This is `M(M)_D`: an irreducible supercuspidal representation of `M` is its
  own supercuspidal support, so the irreducible representations of `M` with inertial support
  `(M, D)` are exactly the members of `D`.
- **`InBlockG Y`** means that every irreducible subquotient `τ` of `Y` is a subquotient of
  `i_P^G σ` for some `σ` with `IsTwist σ`. This is the analogue of `M(G)_Ω` with `Irr(G)_Ω`
  replaced by the irreducible subquotients of the representations `i_P^G σ`, `σ ∈ D`. See
  correspondence note 2.

The three parts:

| Part | Source | Statement |
| --- | --- | --- |
| (i) | Corollary (i) | For every `σ` with `IsTwist σ`, `(leviInductionFunctor … ).obj σ` is irreducible |
| (ii) | Corollary (ii), in the form its proof reduces to | For every `Y` with `InBlockG Y` and `Nontrivial Y`, the Jacquet module `(leviJacquetFunctor … ).obj Y` has an irreducible subquotient `σ` with `IsTwist σ` |
| (iii) | Corollary (iii) | Induction maps every `InBlockM` object to an `InBlockG` object; the functor `InBlockM.ι ⋙ leviInductionFunctor …` is full and faithful; every `InBlockG` object is isomorphic to the induction of an `InBlockM` object |

## Correspondence notes

1. **Maximal parabolics and `W(M, *)`.** As in the Theorem, the statement allows every
   actual maximal proper parabolic with any rational Levi instead of a maximal standard
   Levi; this is equivalent by `G(F)`-conjugation.
2. **The block `M(G)_Ω`.** The source's `Irr(G)_Ω` consists of the irreducible `π` whose
   supercuspidal support (VI.7.1, defined through the irreducible supercuspidal
   subquotients of the Jacquet modules of `π`, well defined up to association by the VI.7.1
   Lemma) is associated to `(M, ρψ)` for an unramified `ψ`. By Frobenius reciprocity such a
   `π` embeds in the induction of a datum of its support, and by the VI.5.4 Theorem the
   inductions of associated data have the same composition factors. Conversely, an
   irreducible subquotient of `i_P^G(ρψ)` shares an irreducible subquotient with the
   induction of its own support, so by the VI.5.4 Theorem that support is associated to
   `(M, ρψ)`. Hence `Irr(G)_Ω` is the set of irreducible subquotients of the representations
   `i_P^G σ`, `σ ∈ D`, and `InBlockG` is `M(G)_Ω`. This identification uses the published,
   unproved `LeviCuspidalSupportAssociationStatement` (VI.7.1, Lemma) and
   `LeviSupercuspidalInductionAssociationStatement` (VI.5.4, Theorem), recorded in the
   [supercuspidal finite-length progress note](../../../notes/renard/supercuspidal-finite-length-progress.md);
   this module does not prove it. The same encoding by induction occurrence is used for
   actual standard families in Worker 1153's
   [BernsteinBlock](../CuspidalSupport/BernsteinBlock.md).
3. **Part (i).** The source's "dans les représentations irréductibles de `M(G)_Ω`" has two
   halves. Membership in `M(G)_Ω` holds by the definition of `InBlockG`, since an
   irreducible `i_P^G σ` is its own irreducible subquotient. The statement asserts the
   irreducibility.
4. **Part (ii) is derived.** The source's `r_D` composes `r_P^G` with the projection of
   `M(M)` onto its factor `M(M)_D` from the Bernstein decomposition of `M`. No such
   projection exists in the Library, so the statement does not name `r_D`. The source proves
   (ii) by Lemma A.VIII.1: an exact functor between these abelian categories is faithful
   once it sends every nonzero object to a nonzero object. For nonzero `Y` in `M(G)_Ω`, the
   `D`-component of `r_P^G(Y)` is nonzero exactly when `r_P^G(Y)` has an irreducible
   subquotient in `D`: subquotients of the other components are not in `D`, and a nonzero
   smooth representation has an irreducible subquotient. Part (ii) states this nonvanishing
   criterion. Its equivalence with the faithfulness of `r_D` uses the Bernstein
   decomposition of `M(M)` and Lemma A.VIII.1, which are not formalized here.
5. **Part (iii).** The source asserts that `r_D : M(G)_Ω → M(M)_D` is an equivalence with
   inverse `i_P^G`, and that the unit `π → i_P^G r_D(π)` is an isomorphism. The statement
   asserts the equivalence through `i_P^G`: it sends `M(M)_D` into `M(G)_Ω` (stated
   explicitly, since the source takes it for granted), it is full and faithful there, and it
   is essentially surjective onto `M(G)_Ω`. Full, faithful and essentially surjective is an
   equivalence of the full subcategories. The unit isomorphism is not stated because `r_D`
   is not named.
6. **Universes.** Carriers in `Type (max u v)` cover every universe containing the field's.
   One universe on both sides keeps induction and essential surjectivity inside the same
   categories.

## Relation to published work

At Library commit `7e84f6ad`:

- the VII.1.3 Theorem is the published `MaximalLeviSupercuspidalReducibilityStatement`
  (Worker 6), with proof task `004e00e1-5995-4dc1-884e-a5f512150d0c`; it is not proved.
  Part (i) follows from it as in the source: if `i_P^G σ` were reducible for some `σ ∈ D`,
  the Theorem would give `w · M = M` and `σ^w ≃ σψ`, hence `w · D = D`;
- Worker 1153's `BernsteinBlock` defines full Bernstein blocks for actual standard families
  by the same induction-occurrence relation, over all cuspidal data at once. No comparison
  between that block and `InBlockG` is stated or proved.

No theorem of the Library proves `MaximalLeviBlockStatements` or any of its parts. Its proof
is a separate obligation; the source route for (ii) and (iii) uses (i), the geometric lemma
VI.5.3, Lemma A.VIII.1, the adjunction of `r_P^G` and `i_P^G`, and the injectivity of the
unit of the adjunction from Lemma VI.7.2 (iii).

## Provenance

Derived from Renard VII.1.3, Corollary, for the represented-parabolic interface. The
encodings of `w · D ≠ D`, of `M(M)_D` and `M(G)_Ω`, of part (ii) and of the equivalence in
part (iii) are formalization choices explained above.
