/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MvPolynomial.Funext
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.PointCount

/-!
# Zariski density of rational points on a smooth scheme

Let `k` be a separably closed field and let `X` be a smooth `k`-scheme, given by a
structure morphism `f : X ⟶ Spec k`. Then the `k`-rational points of `X` are Zariski dense
in `X`.

The proof follows Stacks, Tag 056U. Over any field `k`, a smooth `X` is, around every point,
étale over an affine space `𝔸ⁿ_k`. Étale morphisms are open, and a nonempty open of `𝔸ⁿ_k`
contains a point with coordinates in a separable closure of `k`, since a nonzero polynomial does
not vanish identically on an infinite field. Residue field extensions along étale morphisms
are separable, so every nonempty open of `X` contains a closed point whose residue field is
finite and separable over `k`. If `k` is separably closed, such a residue field is `k` itself,
and the point is `k`-rational. In particular `X(k)` is nonempty as soon as `X` is.

The `k`-rational points are `AlgebraicGeometry.Scheme.Hom.fieldPoints f k`, the sections
of `f`, and we record their density as density of the set of underlying points of `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`: the `K`-rational point `x_K` of
  `X_K = X ×_k Spec K` induced by a `k`-rational point `x` of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.dense_setOf_isClosed_finite_isSeparable`: on a smooth scheme over
  a field `k`, the closed points with finite separable residue field are dense.
- `AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints`: the `k`-rational points of a
  smooth scheme over a separably closed field `k` are Zariski dense.
- `AlgebraicGeometry.Scheme.Hom.denseRange_baseChangeFieldPoint`: the points `x_K` for
  `x ∈ X(k)` are Zariski dense in `X_K`.
- `AlgebraicGeometry.Scheme.Hom.exists_fieldPoints_notMem_support_zeroLocus`: a nonzero
  morphism of invertible modules on a reduced smooth scheme over a separably closed field does
  not vanish at some rational point.
- `AlgebraicGeometry.Scheme.Hom.infinite_fieldPoints`: a smooth proper geometrically integral
  curve over a separably closed field has infinitely many rational points.

## References

- Stacks Project, Tag `056U`, <https://stacks.math.columbia.edu/tag/056U>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

section Separable

/-- The residue fields of `X` along `f : X ⟶ Spec k` are separable over `k`. Phrased with the
algebra structure given by `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`. -/
private abbrev IsSeparableAt (f : X.Hom (Spec (.of k))) (x : X) : Prop :=
  let := (f.residueFieldAlgebraMap x).toAlgebra
  Algebra.IsSeparable k (X.residueField x)

private lemma isSeparableAt_comp {Y : Scheme.{u}} (g : X ⟶ Y) (f : Y.Hom (Spec (.of k))) (x : X)
    (h₁ : IsSeparableAt f (g.base x))
    (h₂ : letI := (g.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (g.base x)) (X.residueField x)) :
    IsSeparableAt (g ≫ f) x := by
  let := (f.residueFieldAlgebraMap (g.base x)).toAlgebra
  let := (g.residueFieldMap x).hom.toAlgebra
  let := ((g ≫ f).residueFieldAlgebraMap x).toAlgebra
  have : IsScalarTower k (Y.residueField (g.base x)) (X.residueField x) :=
    .of_algebraMap_eq' (Hom.residueFieldAlgebraMap_comp g f x)
  exact Algebra.IsSeparable.trans k (Y.residueField (g.base x)) (X.residueField x)

private lemma isSeparableAt_of_comp {Y : Scheme.{u}} (g : X ⟶ Y) (f : Y.Hom (Spec (.of k)))
    (x : X) (h : IsSeparableAt (g ≫ f) x) : IsSeparableAt f (g.base x) := by
  let := (f.residueFieldAlgebraMap (g.base x)).toAlgebra
  let := ((g ≫ f).residueFieldAlgebraMap x).toAlgebra
  let φ : Y.residueField (g.base x) →ₐ[k] X.residueField x :=
    { toRingHom := (g.residueFieldMap x).hom
      commutes' := fun a ↦ (RingHom.congr_fun (Hom.residueFieldAlgebraMap_comp g f x) a).symm }
  exact Algebra.IsSeparable.of_algHom k _ φ

end Separable

/-- On a separated `k`-scheme, a point whose residue field is separable algebraic over `k` is
closed: `Spec κ(y) ⟶ Spec k` is integral, hence universally closed, so `Spec κ(y) ⟶ Y` is
universally closed and its image `{y}` is closed. -/
private lemma isClosed_singleton_of_isSeparableAt {Y : Scheme.{u}} (g : Y.Hom (Spec (.of k)))
    [IsSeparated g] (y : Y) (h : IsSeparableAt g y) : IsClosed {y} := by
  let := (g.residueFieldAlgebraMap y).toAlgebra
  have : IsIntegralHom (Y.fromSpecResidueField y ≫ g) := by
    rw [← g.specMap_residueFieldAlgebraMap, IsIntegralHom.SpecMap_iff]
    exact (Algebra.IsIntegral.isIntegral (R := k) (A := Y.residueField y) ·)
  have := UniversallyClosed.of_comp_of_isSeparated (Y.fromSpecResidueField y) g
  rw [← Y.range_fromSpecResidueField]
  exact (Y.fromSpecResidueField y).isClosedMap.isClosed_range

/-- The `k`-points of `𝔸ⁿ_k` with coordinates in a separable closure of `k` are dense: every
nonempty open of `Spec k[X₁, …, Xₙ]` contains a point with residue field separable over `k`. -/
private lemma exists_isSeparableAt_mvPolynomial (n : ℕ)
    (O : Set (Spec (.of (MvPolynomial (Fin n) k)))) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ w ∈ O, IsSeparableAt (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n)))) w := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨_, ⟨g, rfl⟩, hyg, hgO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy hO
  let K := SeparableClosure k
  have hg : MvPolynomial.map (algebraMap k K) g ≠ 0 := by
    refine (map_ne_zero_iff _ (MvPolynomial.map_injective _ (algebraMap k K).injective)).mpr ?_
    rintro rfl
    exact hyg (zero_mem _)
  obtain ⟨a, ha⟩ : ∃ a : Fin n → K, MvPolynomial.aeval (R := k) a g ≠ 0 := by
    by_contra! h
    refine hg (MvPolynomial.funext fun a ↦ ?_)
    simpa [MvPolynomial.eval_map, MvPolynomial.aeval_def] using h a
  let s : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)
  have hs : s ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext ((MvPolynomial.aeval (R := k) a).comp_algebraMap))
  refine ⟨s.base default, hgO ?_, ?_⟩
  · simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro hmem
    have h : g ∈ Ideal.comap (MvPolynomial.aeval (R := k) a).toRingHom ⊥ := by
      convert hmem using 2
      exact congrArg (Ideal.comap _) (Ideal.eq_bot_of_prime (K := K) _).symm
    exact ha (by simpa using h)
  · obtain ⟨φ, hφ⟩ := ((Spec.map (CommRingCat.ofHom MvPolynomial.C)).exists_fieldPoints_base_eq_iff
      K (s.base default)).mp ⟨⟨s, hs⟩, rfl⟩
    let := ((Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n)))).residueFieldAlgebraMap
      (s.base default)).toAlgebra
    exact Algebra.IsSeparable.of_algHom k _
      { toRingHom := φ.hom, commutes' := fun c ↦ RingHom.congr_fun hφ c }

/-- A smooth scheme over a field is, around every point, étale over an affine space. -/
private lemma exists_etale_mvPolynomial (f : X.Hom (Spec (.of k))) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (n : ℕ)
      (π : V.toScheme ⟶ Spec (.of (MvPolynomial (Fin n) k))),
      Etale π ∧ π ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = V.ι ≫ f := by
  obtain ⟨U, -, V, hV, hxV, e, hss⟩ := Smooth.exists_isStandardSmooth f x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim (f.base x) y ▸ e hxV
  have hss' : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V e).hom.IsStandardSmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso _ _).mpr hss
  obtain ⟨n, g, hgC, hg⟩ := hss'.exists_etale_mvPolynomial
  have : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.mpr hg
  refine ⟨V, hV, hxV, n, hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g), inferInstance, ?_⟩
  have hgC' : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom g =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V e :=
    CommRingCat.hom_ext hgC
  rw [Category.assoc, ← Spec.map_comp, hgC', Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec f _ hV,
    ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]

/-- **Density of separable points.** Let `X` be a smooth scheme over a field `k`. Then the
closed points `x` of `X` whose residue field `κ(x)` is finite and separable over `k` are dense.

(blueprint: `lemma-twisting-h-0-1-h`) -/
@[stacks 056U]
theorem Hom.dense_setOf_isClosed_finite_isSeparable (f : X.Hom (Spec (.of k))) [Smooth f] :
    Dense {x : X | IsClosed {x} ∧ letI := (f.residueFieldAlgebraMap x).toAlgebra
      Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x)} := by
  refine dense_iff_inter_open.mpr fun W hW ⟨x₀, hx₀⟩ ↦ ?_
  obtain ⟨V, hV, hx₀V, n, π, hπ, hπf⟩ := exists_etale_mvPolynomial f x₀
  let W' : Set V.toScheme := V.ι.base ⁻¹' W
  have hW' : IsOpen W' := hW.preimage V.ι.base.hom.continuous
  obtain ⟨w, ⟨y, hyW, rfl⟩, hw⟩ := exists_isSeparableAt_mvPolynomial n (π.base '' W')
    (π.isOpenMap _ hW') ⟨_, ⟨⟨x₀, hx₀V⟩, hx₀, rfl⟩⟩
  have hy : IsSeparableAt (π ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)) y :=
    isSeparableAt_comp π _ y hw inferInstance
  rw [hπf] at hy
  have : IsAffine V.toScheme := hV
  have hyc : IsClosed {y} := isClosed_singleton_of_isSeparableAt _ y hy
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hxc : IsClosed {V.ι.base y} := by
    have := V.ι.isOpenEmbedding.preimage_closedPoints
    exact (this.symm ▸ hyc : y ∈ V.ι.base ⁻¹' closedPoints X)
  exact ⟨V.ι.base y, hyW, hxc, f.finite_residueField_of_isClosed _ hxc,
    isSeparableAt_of_comp V.ι f y hy⟩

/-- **Zariski density of rational points.** Let `X` be a smooth scheme over a separably closed
field `k`, given by its structure morphism `f : X ⟶ Spec k`. Then the image in `X` of the set
`X(k)` of `k`-rational points is Zariski dense.

(blueprint: `lemma-twisting-h-0-1-h`, `lemma-representability-picard-functor`) -/
theorem Hom.denseRange_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k))) [Smooth f] :
    DenseRange fun p : f.fieldPoints k ↦ (p.1.base default : X) := by
  refine f.dense_setOf_isClosed_finite_isSeparable.mono fun x hx ↦ ?_
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Algebra.IsSeparable k (X.residueField x) := hx.2.2
  let e := RingEquiv.ofBijective _ (IsSepClosed.algebraMap_bijective k (X.residueField x))
  refine (f.exists_fieldPoints_base_eq_iff k x).mpr ⟨CommRingCat.ofHom e.symm.toRingHom, ?_⟩
  ext c
  exact e.symm_apply_apply c

/-- **Rational points of a smooth scheme exist.** A nonempty smooth scheme over a separably
closed field `k` has a `k`-rational point.

(blueprint: `lemma-representability-picard-functor`) -/
theorem Hom.nonempty_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k))) [Smooth f]
    [Nonempty X] : Nonempty (f.fieldPoints k) :=
  f.denseRange_fieldPoints.nonempty

open Limits in
/-- The `K`-rational point `x_K = Spec K ×_k x` of the base change `X_K = X ×_k Spec K`
induced by a `k`-rational point `x` of `X`, for a field extension `K` of `k`. A `k`-rational
point is an element of `AlgebraicGeometry.Scheme.Hom.fieldPoints`, a section `Spec k ⟶ X` of the
structure morphism, and `x_K` is the induced section `σ_T` for `T = Spec K`.

(blueprint: `def-pc-rational-point`) -/
noncomputable def Hom.baseChangeFieldPoint (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] (p : f.fieldPoints k) :
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fieldPoints K :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p.1) (𝟙 _) (by
    rw [Category.assoc, p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Category.comp_id, Category.id_comp]), by
    rw [pullback.lift_snd, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩

/-- A `k`-rational point `x : Spec k ⟶ X` of a `k`-scheme is a closed immersion, being a section
of the structure morphism. This specialises Mathlib's low-priority instance `IsClosedImmersion f`
for `f : Y ⟶ X` with `[Subsingleton Y] [X.Over Y] [f.IsOver Y]`, which does not apply here because
`fieldPoints` carry no `IsOver` instances. -/
instance Hom.isClosedImmersion_fieldPoints (f : X.Hom (Spec (.of k))) (p : f.fieldPoints k) :
    IsClosedImmersion p.1 :=
  isClosedImmersion_of_comp_eq_id f p.1 (by
    rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])

open Limits in
/-- The only point of `X_K` over a `k`-rational point `x` of `X` is `x_K`: the fibre of
`X_K ⟶ X` over `x` is `Spec k ×_k Spec K = Spec K`, a single point. -/
lemma Hom.baseChangeFieldPoint_eq_of_fst_eq (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] (p : f.fieldPoints k)
    {y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})}
    (hy : (pullback.fst _ _ : _ ⟶ X).base y = p.1.base default) :
    (f.baseChangeFieldPoint K p).1.base default = y := by
  have : IsIso (p.1 ≫ f) := by
    rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have : Subsingleton (pullback p.1 (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap k K)))) : Scheme.{u}) :=
    ((pullbackRightPullbackFstIso _ _ p.1).hom ≫ pullback.snd _ _).homeomorph.subsingleton
  have hmem (v : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
      (hv : (pullback.fst _ _ : _ ⟶ X).base v ∈ Set.range p.1.base) :
      v ∈ Set.range (pullback.snd p.1 (pullback.fst _ _)).base := by
    rw [Scheme.Pullback.range_snd]
    exact hv
  obtain ⟨z₁, hz₁⟩ := hmem y ⟨default, hy.symm⟩
  obtain ⟨z₂, hz₂⟩ := hmem ((f.baseChangeFieldPoint K p).1.base default)
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap k K))).base default, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, baseChangeFieldPoint,
        pullback.lift_fst]⟩
  rw [← hz₁, ← hz₂, Subsingleton.elim z₁ z₂]

open Limits in
/-- **Density of the base-changed rational points.** Let `X` be a smooth scheme over a
separably closed field `k` and let `K` be a field extension of `k`. Then the `K`-rational
points `x_K` of `X_K = X ×_k Spec K` coming from the `k`-rational points `x` of `X` are
Zariski dense in `X_K`.

(blueprint: `lemma-twisting-h-0-1-h`, part (1)) -/
theorem Hom.denseRange_baseChangeFieldPoint [IsSepClosed k] (f : X.Hom (Spec (.of k)))
    [Smooth f] (K : Type u) [Field K] [Algebra k K] :
    DenseRange fun p : f.fieldPoints k ↦ (f.baseChangeFieldPoint K p).1.base default := by
  refine dense_iff_inter_open.mpr fun U hU hne ↦ ?_
  obtain ⟨p, u, huU, hu⟩ := f.denseRange_fieldPoints.exists_mem_open
    ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isOpenMap _ hU)
    (hne.image _)
  refine ⟨_, ?_, p, rfl⟩
  dsimp only
  rwa [f.baseChangeFieldPoint_eq_of_fst_eq K p hu]

open Limits in
/-- **Non-vanishing at a base-changed rational point.** Let `X` be a smooth scheme over a
separably closed field `k`, let `K` be a field extension of `k` and let `φ` be a morphism of
`𝒪_{X_K}`-modules, e.g. a global section `s : 𝒪_{X_K} ⟶ ℒ` of an invertible module. If `φ` does
not vanish identically, i.e. its zero scheme `Z(φ)` is not all of `X_K`, then there is a
`k`-rational point `x` of `X` such that `φ` does not vanish at `x_K`.

(blueprint: `lemma-twisting-h-0-1-h`, part (2)) -/
theorem Hom.exists_baseChangeFieldPoint_notMem_support_zeroLocus [IsSepClosed k]
    (f : X.Hom (Spec (.of k))) [Smooth f] (K : Type u) [Field K] [Algebra k K]
    {M N : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules} (φ : M ⟶ N)
    (h : ∃ y, y ∉ φ.zeroLocus.support) :
    ∃ p : f.fieldPoints k, (f.baseChangeFieldPoint K p).1.base default ∉ φ.zeroLocus.support :=
  (f.denseRange_baseChangeFieldPoint K).exists_mem_open
    φ.zeroLocus.support.isClosed.isOpen_compl h

/-- **Non-vanishing at a rational point.** Let `X` be a reduced smooth scheme over a separably
closed field `k`, e.g. a smooth projective curve, and let `φ : ℳ ⟶ 𝒩` be a nonzero morphism of
invertible `𝒪_X`-modules, e.g. a nonzero global section `s : 𝒪_X ⟶ ℒ`. Then `φ` does not vanish
at some `k`-rational point of `X`.

(blueprint: `lemma-twisting-h-0-1-h`, part (3)) -/
theorem Hom.exists_fieldPoints_notMem_support_zeroLocus [IsSepClosed k]
    (f : X.Hom (Spec (.of k))) [Smooth f] [IsReduced X] {M N : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} M] [SheafOfModules.IsInvertible.{u, u, u} N]
    (φ : M ⟶ N) (hφ : φ ≠ 0) :
    ∃ p : f.fieldPoints k, p.1.base default ∉ φ.zeroLocus.support := by
  have h : φ.zeroLocus.support ≠ ⊤ := by
    rwa [Ne, IdealSheafData.support_eq_top_iff, Modules.Hom.zeroLocus_eq_bot_iff]
  obtain ⟨y, hy⟩ : ∃ y, y ∉ φ.zeroLocus.support := by
    by_contra! H
    exact h (eq_top_iff.mpr fun y _ ↦ H y)
  exact f.denseRange_fieldPoints.exists_mem_open
    φ.zeroLocus.support.isClosed.isOpen_compl ⟨y, hy⟩

/-- **Infinitude of the rational points of a curve.** A smooth proper geometrically integral
curve over a separably closed field has infinitely many rational points. Every rational point
is a closed point, so if there were only finitely many of them, their union would be closed and,
by `AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints`, equal to `X`; then `X` would be a
finite discrete space, of dimension zero, whereas the curve `X` has dimension one.

(blueprint: `lemma-twisting-h-0-1-h`, part (3)) -/
theorem Hom.infinite_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k)))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] :
    Infinite (f.fieldPoints k) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have hdim := (smoothOfRelativeDimension_iff_topologicalKrullDim_eq f 1).mp inferInstance
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hcl (p : f.fieldPoints k) : IsClosed {p.1.base default} := by
    have hp : p.1 ≫ f = 𝟙 _ := by
      rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    have := isClosedImmersion_of_comp_eq_id f p.1 hp
    have hr : Set.range p.1.base = {p.1.base default} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ congrArg _ (Subsingleton.elim _ _), fun h ↦ ⟨_, h.symm⟩⟩
    rw [← hr]
    exact p.1.isClosedEmbedding.isClosed_range
  have hrange : Set.range (fun p : f.fieldPoints k ↦ p.1.base default) = Set.univ := by
    rw [← (f.denseRange_fieldPoints).closure_range, Set.range_eq_iUnion,
      (isClosed_iUnion_of_finite hcl).closure_eq]
  have : T1Space X := ⟨fun x ↦ by
    obtain ⟨p, rfl⟩ := hrange.symm ▸ Set.mem_univ x
    exact hcl p⟩
  have : Finite X := Set.finite_univ_iff.mp (hrange ▸ Set.finite_range _)
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at this
  exact absurd this (by decide)

end AlgebraicGeometry.Scheme
