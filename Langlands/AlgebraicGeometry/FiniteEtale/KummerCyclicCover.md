# Torsor covers of finite abelian quotients of the fundamental group

The module `Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicCover`
realizes a finite commutative quotient `C` of the finite étale fundamental
group by a cover with an action of `C`. For an affine base, it describes the
`C`-invariants of the ring of such a cover and provides points of the cover
over every maximal ideal on which `C` acts freely. Declarations are in the
namespace `Langlands.AlgebraicGeometry.FiniteEtale`; schemes, the field `Ω` and
the group `C` are in one universe `u`.

## Torsor covers

`exists_torsor_cover` assumes that `S` is a connected, locally Noetherian
scheme, `s : Spec Ω ⟶ S` is a geometric point (`Ω` algebraically closed) with
finite geometric fibres `hs`, `C` is a finite commutative group, and
`χ : FundamentalGroup s hs →* C` has open kernel. It gives a diagram
`D : SingleObj C ⥤ Cover S` and a bijection
`φ : Fiber s (D.obj (SingleObj.star C)) ≃ C` such that

- `φ (g • y) = χ g * φ y` for `g` in the fundamental group, and
- `φ (y ≫ (D.map c).hom) = c * φ y` for `c ∈ C` (the arrow `c` of
  `SingleObj C`).

So the geometric fibre of the cover is a `C`-torsor, and the fundamental
group acts on it through `χ` and translation.

Proof as implemented. By the Library's `geometricGaloisFiberFunctor`,
`Cover S` is a Galois category with fibre functor `fiberFunctor s hs`. Give
`C` the discrete topology and the action of the fundamental group through
`χ`. This action is continuous because the stabilizer of every point is
`ker χ`, which is open (Mathlib's `continuousSMul_iff_stabilizer_isOpen`).
Multiplications by elements of `C` commute with this action (`C` is
commutative), so they form a homomorphism `m` from `C` to the endomorphisms
of the continuous action `X = C`. Mathlib's
`PreGaloisCategory.functorToContAction` is an equivalence `E` from `Cover S`
to continuous finite actions. Put `D = SingleObj.functor m ⋙ E.inverse`. The
bijection `φ` is the component at `X` of the counit isomorphism of `E`; its
compatibility with the fundamental group is the equivariance of that
component, and its compatibility with `C` is the naturality of the counit.

## Invariants and free points over an affine base

Now `S` is moreover affine, `C` is a finite group, and
`D : SingleObj C ⥤ Cover S`. The Library module `AffineQuotientCoconeProof`
provides the ring `coverRing D` of the cover, the action `coverAction D c` of
`c ∈ C` on it, the subalgebra `quotientRing D` of invariants, and the quotient
cover `quotientCover D` with its structure morphism `quotientStructure D`.

- `bijective_algebraMap_quotientRing`: if the geometric fibre at `s` is
  nonempty and `C` acts transitively on it, then
  `algebraMap Γ(S, ⊤) (quotientRing D)` is bijective. By the Library's
  `quotientCocone_surjective` and `quotientCocone_orbit`, the geometric fibre
  of the quotient cover is the set of orbits, here a single point. The
  geometric fibre of the identity cover `cover (𝟙 S)` is also a single point.
  So the map `quotientCover D ⟶ cover (𝟙 S)` given by `quotientStructure D` is
  bijective on geometric fibres. Fibre functors reflect isomorphisms
  (`isIso_of_reflects_iso`), so `quotientStructure D` is an isomorphism. The
  ring map is then bijective by `isIso_SpecMap_iff`.
- `exists_algebraMap_eq_of_forall_coverAction_eq`: under the same
  hypotheses, every element of `coverRing D` fixed by all `coverAction D c`
  is the image of an element of `Γ(S, ⊤)`.
- `exists_free_residue_point`: if the geometric fibre at `s` is nonempty and
  `C` acts freely on it, then for every maximal ideal `𝔪` of `Γ(S, ⊤)` there
  are a field `K : Type u` and a ring map `φ : coverRing D →+* K` that
  vanishes on the image of `𝔪` and satisfies `φ ∘ coverAction D c ≠ φ` for
  every `c ≠ 1`. This statement does not need `C` to be finite. Here `K` is
  an algebraic closure of `Γ(S, ⊤)/𝔪` and `s'` is
  the corresponding geometric point of `S` (the Library's `affinePointEquiv`).
  The Library's `geometricPathExists` gives an isomorphism of fibre functors
  from `s` to `s'`, so `C` also acts freely on the geometric fibre at `s'`.
  Take for `φ` the ring map `fiberRingHom D s' y'` of a point `y'` of that
  fibre. If `φ ∘ coverAction D c = φ`, then `fiberRingHom_map` and
  `fiberRingHom_injective` show that `c` fixes `y'`, so `c = 1`. The map `φ`
  kills `𝔪` by `appTop_comp_fiberRingHom`.

## Provenance

The torsor cover is the cover attached to a finite continuous `π₁`-set
through Grothendieck's equivalence between finite étale covers of `S` and
finite sets with a continuous action of `π₁(S, a)` (SGA 1, Exposé V §7,
printed p.115, PDF p.131; registered source `sga1-arxiv-math-0206203v2`).
The same section notes that this equivalence translates passing to the
quotient of a cover into passing to the quotient of the `π₁`-set; the Library
module `AffineQuotientCoconeProof` follows the affine case of SGA 1,
Exposé V §1. The formulation through the Library's fibre functors and the
quotient cocone, and the arguments above, are internal to the Library.
