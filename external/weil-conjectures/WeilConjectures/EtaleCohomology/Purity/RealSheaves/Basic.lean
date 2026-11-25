/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RepresentationTheory.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.ZetaFunction
public import WeilConjectures.ZetaSeries

/-!
# Weil groups of curves over a finite field and their representations

This file sets up the group-theoretic side of the purity theorem for real lisse sheaves on
curves: the Weil group of a curve over a finite field, lisse Weil sheaves in their
description as representations of that group, and the elementary operations on them.

A Weil group `AlgebraicGeometry.WeilGroup` of `C₀` is a topological group `W(C₀)` with the
exact degree sequence `1 → π₁(C) → W(C₀) → ℤ → 0`, a degree-one lift `frobeniusLift`, and, for
every closed point `x` of `C₀`, a local Frobenius element of degree `e_x = [k(x) : 𝔽_q]`,
*presented* as the Weil group of the étale fundamental group: it comes with a geometric base
point `s` of `C₀`, a fundamental group `π₁(C₀, s)` of the fibre functor at `s` on finite étale
`C₀`-schemes, and an isomorphism of `W(C₀)` with the Weil group
`AlgebraicGeometry.Scheme.FiniteEtale.weilGroup` of `π₁(C₀, s)` (the elements acting on the
geometric fibres of the constant covers as an integral power of the geometric Frobenius),
matching the degrees, inducing the profinite topology on `π₁(C)`, and carrying each local
Frobenius to a Frobenius element of `π₁(C₀, s)` at that point
(`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement`). These fields determine `W(C₀)`,
its topology and the conjugacy classes of its local Frobenius elements up to isomorphism.

Coefficients are `ℚ̄_ℓ = PadicAlgCl l`, and the archimedean comparison is a ring embedding
`ι : ℚ̄_ℓ →+* ℂ`.

## Implementation notes

The curve itself enters through the instance arguments `[Finite K]` and `[IsCurve p]` of
`AlgebraicGeometry.WeilGroup`, so that every statement about a `W : WeilGroup p` carries them.
Geometric connectedness of `C₀`, a standing hypothesis of `situation-weil`, is the field
`AlgebraicGeometry.WeilGroup.geometricallyConnected`, since the presentation through
`AlgebraicGeometry.Scheme.FiniteEtale.weilGroup` requires it; smoothness is an extra hypothesis
where it is needed. Only closed
points of `C₀` — those of `AlgebraicGeometry.Scheme.finitePoints` — index a local Frobenius,
since `AlgebraicGeometry.Scheme.Hom.degreeOver` has the junk value `0` elsewhere.

`W(C₀)` is kept as an abstract topological group `carrier` together with its presentation,
rather than defined as the subgroup `weilGroup` of `π₁(C₀, s) × ℤ`, because the topology of the
Weil group is not the subspace topology: the geometric part `π₁(C)` is open. Some fields are
consequences of others for the genuine Weil group (for instance `deg_frobenius` follows from
`isFrobeniusElement_frobenius`), and some are theorems about it which need hypotheses on `C₀`:
the surjectivity of the degree needs `C₀` geometrically connected. The structure is constructed
for a geometrically connected curve in `AlgebraicGeometry.WeilGroup.ofFundamentalGroup`.

The Chebotarev density theorem, that the local Frobenius elements generate a dense normal
subgroup, is not a field: it is a consequence of the other fields and of the Euler product of
`L`-functions, `AlgebraicGeometry.WeilGroup.dense_frobenius`.

The identification of `ker deg` with the étale fundamental group of the *geometric* curve
`C₀ ×_K K̄`, which the rank-one purity theorems use, is the separate predicate
`AlgebraicGeometry.WeilGroup.IsEtaleQuotient`; every Weil group of a geometrically connected
curve satisfies it by the homotopy exact sequence (`AlgebraicGeometry.WeilGroup.isEtaleQuotient`).

## Main definitions

- `AlgebraicGeometry.WeilGroup` : the Weil group of a curve over a finite field.
- `AlgebraicGeometry.WeilGroup.Restriction` : the restriction of Weil groups along a nonempty
  open immersion of curves.
- `AlgebraicGeometry.WeilGroup.IsLisse` : a Weil representation is lisse.
- `AlgebraicGeometry.WeilGroup.constLine` : the constant Weil line `B_b`.
- `AlgebraicGeometry.WeilGroup.tateLine` : the Tate line `ℚ̄_ℓ(n) = B_{q ^ (-n)}`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `definition-weil-representation--1`: Weil sheaves and their representations.

The Weil group of a curve `p : C₀ ⟶ Spec 𝔽_q`. It is the preimage of the integer powers of
the geometric Frobenius under `π₁(C₀, s) → Gal(k / 𝔽_q)`, and comes with the exact degree
sequence `1 → π₁(C) → W(C₀) → ℤ → 0` whose kernel is the profinite geometric fundamental
group `π₁(C)`.

It consists of a topological group `W` with a surjective degree homomorphism to `ℤ` whose kernel
is open and profinite, a chosen degree-one lift `frobeniusLift`, and for every closed point `x`
of `C₀` a local Frobenius element `frobenius x`, well defined up to conjugacy, of degree
`e_x = [k(x) : 𝔽_q]`; together with a presentation of all this through the étale fundamental
group `π₁(C₀, s)` of `C₀` at a geometric base point `s`:

* `weilGroupEquiv` identifies `W` with the Weil group of `π₁(C₀, s)`, the subgroup of pairs
  `(g, n)` of `π₁(C₀, s) × ℤ` such that `g` acts on the geometric fibres of the constant covers
  `C₀ ×_{𝔽_q} Spec A` as the `n`-th power of the geometric Frobenius
  (`AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`), and `deg` with the second projection;
* the topology of `W` induces the profinite topology of `π₁(C₀, s)` on `π₁(C)`;
* `frobenius x` is a Frobenius element at `x` of `π₁(C₀, s)`: it acts on the geometric fibres
  at `s` as the geometric Frobenius of `κ(x)` acts on those at a geometric point over `x`,
  transported along a path (`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement`).

That the local Frobenius elements generate a dense normal subgroup (Chebotarev density) is a
theorem about these data, `AlgebraicGeometry.WeilGroup.dense_frobenius`. -/
structure WeilGroup [Finite K] (p : C ⟶ Spec (.of K)) [IsCurve p] where
  /-- The underlying group `W(C₀)` of the Weil group. -/
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  /-- The degree homomorphism `deg : W(C₀) → ℤ`. -/
  deg : carrier →* Multiplicative ℤ
  /-- The degree homomorphism is surjective. -/
  deg_surjective : Function.Surjective deg
  /-- The geometric fundamental group `π₁(C) = ker deg` is open; equivalently, `deg` is
  continuous for the discrete topology of `ℤ`. -/
  isOpen_ker : IsOpen (deg.ker : Set carrier)
  /-- The geometric fundamental group `π₁(C) = ker deg` is compact. -/
  compactSpace_ker : CompactSpace (deg.ker : Subgroup carrier)
  /-- The geometric fundamental group `π₁(C) = ker deg` is profinite. -/
  totallyDisconnectedSpace_ker : TotallyDisconnectedSpace (deg.ker : Subgroup carrier)
  /-- A chosen lift of the geometric Frobenius, of degree one. -/
  frobeniusLift : carrier
  /-- The chosen lift has degree one. -/
  deg_frobeniusLift : deg frobeniusLift = Multiplicative.ofAdd 1
  /-- A choice of local Frobenius element at a closed point of `C₀`; it is well defined up to
  conjugacy, so the characteristic polynomials of `definition-weights` do not depend on it. -/
  frobenius : C.finitePoints → carrier
  /-- The local Frobenius at `x` has degree `e_x = [k(x) : 𝔽_q]`. -/
  deg_frobenius (x : C.finitePoints) :
    deg (frobenius x) = Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)
  /-- The curve `C₀` is connected, so that its finite étale covers form a Galois category. -/
  [connectedSpace : ConnectedSpace C]
  /-- The geometric base point `s` of `C₀`. -/
  basePoint : Spec (.of (AlgebraicClosure K)) ⟶ C
  /-- The étale fundamental group `π₁(C₀, s)`, a fundamental group of the fibre functor at `s`
  on finite étale `C₀`-schemes. -/
  fundamentalGroup : Type u
  [fundamentalGroupGroup : Group fundamentalGroup]
  [fundamentalGroupTopologicalSpace : TopologicalSpace fundamentalGroup]
  [fundamentalGroupIsTopologicalGroup : IsTopologicalGroup fundamentalGroup]
  [fundamentalGroupCompactSpace : CompactSpace fundamentalGroup]
  [mulAction (P : C.FiniteEtale) :
    MulAction fundamentalGroup ((Scheme.FiniteEtale.fiber basePoint).obj P)]
  [isFundamentalGroup :
    PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber basePoint) fundamentalGroup]
  /-- The curve `C₀` is geometrically connected over `𝔽_q`, the standing hypothesis of the Weil
  group `situation-weil`: without it the degree map of
  `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup` is not surjective. -/
  [geometricallyConnected : GeometricallyConnected p]
  /-- The identification of `W(C₀)` with the Weil group of `π₁(C₀, s)`: the pairs `(g, n)` such
  that `g` acts on the geometric fibres of the constant covers as the `n`-th power of the
  geometric Frobenius. -/
  weilGroupEquiv : carrier ≃* Scheme.FiniteEtale.weilGroup p basePoint fundamentalGroup
  /-- Under `weilGroupEquiv`, the degree is the exponent of the geometric Frobenius. -/
  deg_eq (g : carrier) :
    deg g = Scheme.FiniteEtale.weilGroupDeg p basePoint fundamentalGroup (weilGroupEquiv g)
  /-- The topology of `W(C₀)` induces on `π₁(C) = ker deg` the profinite topology of
  `π₁(C₀, s)`. -/
  isEmbedding_ker :
    Topology.IsEmbedding fun g : deg.ker ↦ (weilGroupEquiv g).1.1
  /-- The local Frobenius at `x` is a Frobenius element of `π₁(C₀, s)` at `x`. -/
  isFrobeniusElement_frobenius (x : C.finitePoints) :
    haveI : Finite (C.residueField x.1) := x.2
    Scheme.FiniteEtale.IsFrobeniusElement basePoint fundamentalGroup x.1
      (weilGroupEquiv (frobenius x)).1.1

attribute [instance] WeilGroup.group WeilGroup.topologicalSpace WeilGroup.isTopologicalGroup
  WeilGroup.compactSpace_ker WeilGroup.totallyDisconnectedSpace_ker
  WeilGroup.fundamentalGroupGroup WeilGroup.fundamentalGroupTopologicalSpace
  WeilGroup.fundamentalGroupIsTopologicalGroup WeilGroup.fundamentalGroupCompactSpace
  WeilGroup.mulAction WeilGroup.isFundamentalGroup

namespace WeilGroup

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)

/-- The geometric fundamental group `π₁(C)`, the kernel of the degree homomorphism. -/
protected abbrev geometric : Subgroup W.carrier := W.deg.ker

/-- The inclusion `W(C₀) → π₁(C₀, s)` of the Weil group into the étale fundamental group. -/
noncomputable def toFundamentalGroup : W.carrier →* W.fundamentalGroup :=
  haveI := W.geometricallyConnected
  (MonoidHom.fst _ _).comp
    ((Scheme.FiniteEtale.weilGroup p W.basePoint W.fundamentalGroup).subtype.comp
      W.weilGroupEquiv.toMonoidHom)

theorem toFundamentalGroup_apply (g : W.carrier) :
    W.toFundamentalGroup g = (W.weilGroupEquiv g).1.1 :=
  rfl

/-- Blueprint `lemma-boundary-stalk--2`: Boundary stalks and restriction to an open.

The restriction of Weil groups along a nonempty open immersion `j : U₀ ↪ C₀` of curves over
`𝔽_q`: the homomorphism `W(U₀) → W(C₀)` induced by the restriction functor
`j^* : FÉt(C₀) ⥤ FÉt(U₀)` of finite étale covers and a path `τ` between the base points, that is
an isomorphism `τ : F_{s_U} ∘ j^* ≅ F_{s_C}` of fibre functors on `FÉt(C₀)`: an element `g` of
`W(U₀)` acts on the geometric fibre at `s_U` of the restriction `j^* P` of a finite étale
`C₀`-scheme `P`, and its restriction acts on the fibre of `P` at `s_C` through `τ`
(`restrict_smul`). Since `W(C₀)` embeds into `π₁(C₀, s_C)`, this determines the restriction
map.

The remaining fields are theorems about the map so defined: it is continuous and preserves
degrees, it is surjective because `π₁(U) → π₁(C)` is for a nonempty open of a connected
normal curve (`lemma-boundary-stalk--2`), and it carries the local Frobenius at a closed point of
`U₀` into the Frobenius conjugacy class at its image. -/
structure Restriction {U : Scheme.{u}} {pU : U ⟶ Spec (.of K)} [IsCurve pU] (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (WU : WeilGroup pU) (WC : WeilGroup p) where
  /-- `j` is a morphism of curves over `𝔽_q`. -/
  comp_eq : j ≫ p = pU
  /-- The restriction map `W(U₀) → W(C₀)` of Weil groups. -/
  restrict : WU.carrier →* WC.carrier
  /-- The path from the base point of `U₀` to that of `C₀`: an isomorphism between the fibre
  functor at `s_U` precomposed with the restriction of finite étale covers to `U₀`, and the fibre
  functor at `s_C`. -/
  fiberIso : Scheme.FiniteEtale.pullback j ⋙ Scheme.FiniteEtale.fiber WU.basePoint ≅
    Scheme.FiniteEtale.fiber WC.basePoint
  /-- The restriction map is induced by the restriction of finite étale covers along `j`,
  transported along `fiberIso`. -/
  restrict_smul (g : WU.carrier) (P : C.FiniteEtale)
    (y : (Scheme.FiniteEtale.fiber WU.basePoint).obj ((Scheme.FiniteEtale.pullback j).obj P)) :
    WC.toFundamentalGroup (restrict g) • fiberIso.hom.app P y =
      fiberIso.hom.app P (WU.toFundamentalGroup g • y)
  /-- The restriction map is continuous. -/
  continuous_restrict : Continuous restrict
  /-- The restriction map preserves degrees. -/
  deg_restrict : WC.deg.comp restrict = WU.deg
  /-- The restriction map is surjective, because `π₁(U) → π₁(C)` is. -/
  surjective_restrict : Function.Surjective restrict
  /-- The restriction map carries the local Frobenius at a closed point `x` of `U₀` into the
  Frobenius conjugacy class at the image point of `C₀`. -/
  restrict_frobenius (x : U.finitePoints) (y : C.finitePoints) (hxy : j.base x.1 = y.1) :
    IsConj (WC.frobenius y) (restrict (WU.frobenius x))

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `definition-weil-representation--1`: Weil sheaves and their representations.

A `ℚ̄_ℓ`-representation of the Weil group is *lisse* if the geometric subgroup `π₁(C)` acts
continuously, i.e. the matrix coefficients of the restricted representation are continuous in
every basis. By `proposition-lattices-representations-normal-scheme` this is equivalent, for a
finite-dimensional `V`, to the existence of a model over a finite extension `E/ℚ_ℓ` carrying a
`π₁(C)`-stable `𝒪_E`-lattice.

Finite-dimensionality of `V` is not part of this predicate: it is an independent condition,
imposed where it is needed (see `AlgebraicGeometry.WeilGroup.isLisseRep`). -/
structure IsLisse {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) : Prop where
  /-- In every basis, the matrix coefficients of the geometric part of `ρ` are continuous. -/
  continuous_toMatrix {n : ℕ} (b : Module.Basis (Fin n) (PadicAlgCl l) V) (i j : Fin n) :
    Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) i j

variable {W l} in
/-- For a lisse representation on a finite-dimensional `V`, every coefficient
`g ↦ φ (ρ g v)` of the geometric part of `ρ`, for a linear form `φ` and a vector `v`, is
continuous: in a basis it is a fixed linear combination of matrix coefficients. -/
theorem IsLisse.continuous_apply {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] {ρ : Representation (PadicAlgCl l) W.carrier V}
    (hρ : W.IsLisse l ρ) (φ : V →ₗ[PadicAlgCl l] PadicAlgCl l) (v : V) :
    Continuous fun g : W.geometric ↦ φ (ρ g v) := by
  let b := Module.finBasis (PadicAlgCl l) V
  have key (g : W.geometric) : φ (ρ g v) =
      ∑ i, φ (b i) * ∑ j, LinearMap.toMatrix b b (ρ g) i j * b.repr v j := by
    conv_lhs => rw [← b.sum_repr (ρ g v)]
    simp only [map_sum, map_smul, smul_eq_mul, ← LinearMap.toMatrix_mulVec_repr b b,
      Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  simp_rw [key]
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul <|
    continuous_finsetSum _ fun j _ ↦ (hρ.continuous_toMatrix b i j).mul continuous_const

variable {W l} in
/-- A representation is lisse as soon as every coefficient `g ↦ φ (ρ g v)` of its geometric
part, for a linear form `φ` and a vector `v`, is continuous: the matrix coefficients in a
basis `b` are the coefficients for the coordinate forms of `b` and the vectors of `b`. -/
theorem IsLisse.of_continuous_apply {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V}
    (h : ∀ (φ : V →ₗ[PadicAlgCl l] PadicAlgCl l) (v : V),
      Continuous fun g : W.geometric ↦ φ (ρ g v)) :
    W.IsLisse l ρ where
  continuous_toMatrix b i j := by
    simpa [LinearMap.toMatrix_apply] using h (b.coord i) (b j)

/-- Blueprint `definition-weil-representation--1`: Weil sheaves and their representations.

Continuity of the matrix coefficients in *one* basis of a finite-dimensional `V` implies
continuity in every basis: a change of basis is a fixed invertible matrix, so it acts on the
matrix coefficients by a fixed polynomial expression. -/
theorem isLisse_iff_exists_basis {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) :
    W.IsLisse l ρ ↔ ∃ (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) V), ∀ i j,
      Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) i j := by
  refine ⟨fun h ↦ ⟨_, Module.finBasis (PadicAlgCl l) V, h.continuous_toMatrix _⟩, ?_⟩
  rintro ⟨n, b, hb⟩
  refine IsLisse.of_continuous_apply fun φ v ↦ ?_
  have key (g : W.geometric) : φ (ρ g v) =
      ∑ i, φ (b i) * ∑ j, LinearMap.toMatrix b b (ρ g) i j * b.repr v j := by
    conv_lhs => rw [← b.sum_repr (ρ g v)]
    simp only [map_sum, map_smul, smul_eq_mul, ← LinearMap.toMatrix_mulVec_repr b b,
      Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  simp_rw [key]
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul <|
    continuous_finsetSum _ fun j _ ↦ (hb i j).mul continuous_const

/-- Blueprint `definition-weil-representation`: Operations, constituents and coinvariants.
Blueprint `proposition-twisting-weight-zero-adding-dual--2`: Constant Weil twist.

The constant Weil line `B_b`: the one-dimensional representation of `W(C₀)` on which `g`
acts by `b ^ deg g`; it is trivial on `π₁(C) = ker deg`. Tensoring with it,
`ρ.tprod (W.constLine l b)`, is the constant Weil twist of `ρ`. -/
noncomputable def constLine (b : (PadicAlgCl l)ˣ) :
    Representation (PadicAlgCl l) W.carrier (PadicAlgCl l) where
  toFun g := (b ^ Multiplicative.toAdd (W.deg g) : (PadicAlgCl l)ˣ) • (1 : Module.End _ _)
  map_one' := by simp
  map_mul' g h := by
    have h' : Multiplicative.toAdd (W.deg (g * h))
        = Multiplicative.toAdd (W.deg g) + Multiplicative.toAdd (W.deg h) := by
      rw [map_mul]; rfl
    rw [h', zpow_add]
    ext
    simp [smul_smul, mul_comm]

/-- Blueprint `definition-weil-representation`: Operations, constituents and coinvariants.

The Tate line `ℚ̄_ℓ(n) = B_{q ^ (-n)}`, on which the geometric Frobenius acts by `q ^ (-n)`. -/
noncomputable def tateLine (n : ℤ) :
    Representation (PadicAlgCl l) W.carrier (PadicAlgCl l) :=
  W.constLine l (Units.mk0 ((Nat.card K : PadicAlgCl l) ^ (-n))
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')))

end WeilGroup

end AlgebraicGeometry
