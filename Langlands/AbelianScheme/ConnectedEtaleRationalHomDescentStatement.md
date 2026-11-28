# Étale descent of rational homomorphisms of abelian schemes over a connected base

The module `Langlands.AbelianScheme.ConnectedEtaleRationalHomDescentStatement`
defines one auxiliary isomorphism and one proposition. The module states the
proposition and does not prove it.

## The comparison isomorphism `baseChangeSquareIso`

For scheme morphisms `g : W ⟶ S`, `g' : W' ⟶ S`, `a : Z ⟶ W` and
`a' : Z ⟶ W'` with `h : a ≫ g = a' ≫ g'`, and an abelian scheme `A` over `S`,

```lean
baseChangeSquareIso g g' a a' h A :
  (baseChange a).obj ((baseChange g).obj A) ≅ (baseChange a').obj ((baseChange g').obj A)
```

is the composite of the inverse of the Library's comparison
`baseChangeCompIso g a A` between direct and successive pullback, the
isomorphism `eqToIso` given by the equality of the composites, and
`baseChangeCompIso g' a' A`. It is the canonical identification of the two
iterated pullbacks of `A` to `Z`.

## The proposition

`ConnectedEtaleRationalHomDescentStatement.{u}` says the following. Let
`S : Scheme.{u}` be connected and locally noetherian, and assume that every
positive natural number is a unit in `Γ(S, ⊤)` (for every
`k : GroupScheme.Tate.Index (fun _ => True)`). Let `K : Type u`, let
`W : K → Scheme.{u}` be connected locally noetherian schemes and let
`g k : W k ⟶ S` be étale morphisms whose images cover `S`: every point of `S`
is `g k y` for some `k` and some point `y` of `W k`. Let `A` and `B` be
abelian schemes over `S`, and for every `k` let

```lean
e k : Hom0 ((baseChange (g k)).obj A) ((baseChange (g k)).obj B)
```

be a rational homomorphism between the pullbacks. `Hom0` is the Library's
rationalized Hom group `ℚ ⊗[ℤ] (A ⟶ B)` (`Langlands.AbelianScheme.Rational`).

The compatibility hypothesis is tested on connected locally noetherian
schemes: for all `k l : K`, every connected locally noetherian scheme
`Z : Scheme.{u}` and all morphisms `a : Z ⟶ W k`, `b : Z ⟶ W l` with
`h : a ≫ g k = b ≫ g l`,

```lean
comp0 _ _ _ (rationalBaseChangeHom a (e k))
    (homToHom0 (baseChangeSquareIso (g k) (g l) a b h B).hom) =
  comp0 _ _ _ (homToHom0 (baseChangeSquareIso (g k) (g l) a b h A).hom)
    (rationalBaseChangeHom b (e l))
```

That is, the pullback of `e k` along `a` and the pullback of `e l` along `b`
agree once the two iterated pullbacks of `A` and of `B` are identified by
`baseChangeSquareIso`. Here `rationalBaseChangeHom` is the Library's pullback
of rational homomorphisms (`Langlands.AbelianScheme.RationalBaseChange`),
`homToHom0` the inclusion of actual homomorphisms and `comp0` composition of
rational homomorphisms, written in diagrammatic order.

The conclusion is that there exists `f : Hom0 A B` with
`rationalBaseChangeHom (g k) f = e k` for every `k`.

## Mathematical content and source

The connectedness argument rests on the rigidity of morphisms over a
connected base. Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
third enlarged edition (1994), Chapter 6, §1, Proposition 6.1 (rigidity
lemma), printed pp.115–116 (PDF pp.128–129), registered source
`mumford-fogarty-kirwan-1994-git-3rd`, work with locally noetherian schemes
throughout Chapter 6 (opening of the chapter, printed p.115). Their proper
case reads: let `S` be connected, `p : X → S` flat and proper with
`H⁰(X_s, O_{X_s}) = κ(s)` for every point `s`, and `q : Y → S` separated; if
an `S`-morphism `f : X → Y` maps one fibre `X_s` set-theoretically to a single
point, then `f` factors as `η ∘ p` for a section `η` of `q`. The proof obtains
the section by faithfully flat descent along a base extension over which `X`
acquires a section. This proper case, applied to abelian schemes, and its
use of faithfully flat descent are the background of the derived argument
below.

For actual homomorphisms the proposition is descent of morphisms of schemes
along an étale covering: representable functors are sheaves for the fpqc
topology, and étale coverings are fpqc coverings. Mathlib proves that the
fpqc topology on schemes is subcanonical (`Mathlib.AlgebraicGeometry.Sites.Fpqc`).

Rational homomorphisms have denominators, and the connectedness hypotheses
are what make one denominator suffice. On a connected piece write a rational
homomorphism as `h / m` with `h` actual and `m` positive. Under the unit
hypothesis multiplication by `m` is a finite étale surjective isogeny, and
`h / m` is actual exactly when `h` kills the `m`-torsion subgroup scheme, for
then `h` factors through multiplication by `m` by fpqc descent. The
restriction of `h` to the finite étale `m`-torsion of the source and the zero
map both take values in the finite étale `m`-torsion of the target; their
equalizer is open and closed, so over a connected base they agree everywhere
as soon as they agree on the fibre over one geometric point. Hence
integrality of a rational homomorphism over a connected base is detected at
one geometric point. If `N • e k` is an actual homomorphism, then so is
`N • e l` whenever the images of `W k` and `W l` meet: a connected component
`Z` of `W k ×_S W l` maps to both, the two pullbacks agree on `Z`, and
integrality passes through `Z`. Since the images are open and cover the
connected base `S`, one `N` works for all `k`, and the actual homomorphisms
`N • e k` descend. The proposition is internal to the Library and records a
prerequisite for étale descent of rational isogeny classes of abelian
schemes over connected bases.
