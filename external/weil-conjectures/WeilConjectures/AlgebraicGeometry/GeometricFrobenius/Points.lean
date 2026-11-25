/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.PointCount

/-!
# Geometric points over closed points and rational points

Let `X₀` be a scheme over a finite field `k` with `q` elements, `X = X₀ ×_k k̄` its geometric
fiber and `g_X = 𝟙 × σ` its geometric Galois Frobenius. This file constructs the geometric
points `s : Spec k̄ ⟶ X` over the closed points and over the `𝔽_{qⁿ}`-rational points of `X₀`,
and shows that they are fixed by a power of `g_X` up to reparametrisation by `σ`:
`s ≫ g_Xᵐ = σᵐ ≫ s`, with `m` the degree of the point, respectively `m = n`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`: the geometric point over a
  point with finite residue field `κ(x)`, for an embedding `κ(x) ↪ k̄` chosen by
  `IsAlgClosed.lift`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow`:
  the geometric point over a closed point `x` satisfies `s ≫ g_X^{deg x} = σ^{deg x} ≫ s`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow`:
  a geometric point over an `𝔽_{qⁿ}`-rational point satisfies `s ≫ g_Xⁿ = σⁿ ≫ s`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The projection `X̄ ⟶ X` of the geometric fiber is universally closed, being the base change
of the integral morphism `Spec k̄ ⟶ Spec k`. In particular it maps closed points to closed
points. -/
instance universallyClosed_geometricFiberProj : UniversallyClosed f.geometricFiberProj := by
  have : IsIntegralHom (Scheme.specAlgebraicClosure k).hom := by
    change IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral (R := k) (A := AlgebraicClosure k)
  unfold geometricFiberProj
  infer_instance

/-- The geometric point of the geometric fiber over a point `x` of `X` with finite residue
field `κ(x)` (a closed point, for `X` of finite type over a finite field): the geometric point
`AlgebraicGeometry.Scheme.Hom.geometricFiberPoint` over `Spec κ(x) ⟶ X`, for the `k`-algebra
structure of `κ(x)` given by the structure morphism and an embedding `κ(x) ↪ k̄` chosen by
`IsAlgClosed.lift`. -/
noncomputable def geometricFiberPointOfFinitePoint (x : X.finitePoints) :
    Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  -- `Algebra.IsAlgebraic`, needed by `IsAlgClosed.lift`, is found through `Module.Finite`,
  -- which is not found from `Finite` by instance search
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  f.geometricFiberPoint (K := X.residueField x.1) IsAlgClosed.lift (X.fromSpecResidueField x.1)
    (f.specMap_residueFieldAlgebraMap x.1).symm

/-- The geometric point `s` over a closed point `x` is fixed by `g_X^{deg x}` up to
reparametrisation, `deg x = [κ(x) : k]`:

```
              s
  Spec k̄ ---------> X
    |               |
 σ^{deg x}      g_X^{deg x}
    v               v
  Spec k̄ ---------> X
              s
```
-/
theorem geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow [Finite k]
    (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫
        (f.geometricGaloisFrobenius ^ f.degreeOver x.1).asIso.hom =
      (specGeometricFrobenius k ^ f.degreeOver x.1).asIso.hom ≫
        f.geometricFiberPointOfFinitePoint x := by
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  exact f.geometricFiberPoint_comp_geometricGaloisFrobenius_pow (K := X.residueField x.1)
    IsAlgClosed.lift (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm _
    (Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x.1))

/-- A geometric point `s` over an `𝔽_{qⁿ}`-rational point `y` of `X`, for any embedding
`ι : 𝔽_{qⁿ} ↪ k̄`, is fixed by `g_Xⁿ` up to reparametrisation:

```
             s
  Spec k̄ -------> X
    |             |
   σⁿ           g_Xⁿ
    v             v
  Spec k̄ -------> X
             s
```
-/
theorem geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow [Finite k] (n : ℕ)
    (ι : FiniteField.galoisExtension k n →ₐ[k] AlgebraicClosure k)
    (y : f.fieldPoints (FiniteField.galoisExtension k n)) :
    f.geometricFiberPoint ι y.1 y.2 ≫ (f.geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k ^ n).asIso.hom ≫ f.geometricFiberPoint ι y.1 y.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  exact f.geometricFiberPoint_comp_geometricGaloisFrobenius_pow _ _ _ _
    (FiniteField.nat_card_galoisExtension k n hn)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The structure morphism to `Spec k̄` of a geometric point `t` lying over
`Spec ι₀ : Spec k̄ ⟶ Spec κ(x)` is `Spec α` for a ring endomorphism `α` of `k̄` with
`α ∘ (k ⟶ k̄) = ι₀ ∘ (k ⟶ κ(x))`. -/
lemma residueFieldAlgebraMap_comp_eq_of_comp_geometricFiberProj {x : X}
    (t : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber)
    (ι₀ : X.residueField x ⟶ .of (AlgebraicClosure k))
    (h₀ : t ≫ f.geometricFiberProj = Spec.map ι₀ ≫ X.fromSpecResidueField x) :
    ι₀.hom.comp (f.residueFieldAlgebraMap x) =
      (Spec.preimage (t ≫ f.geometricFiberToAlgebraicClosure)).hom.comp
        (algebraMap k (AlgebraicClosure k)) := by
  have h := t ≫= f.geometricFiber_condition
  rw [← Category.assoc, h₀, Category.assoc, ← f.specMap_residueFieldAlgebraMap, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_preimage (t ≫ f.geometricFiberToAlgebraicClosure)] at h
  simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)

/-- Two geometric points `s, s'` of the geometric fiber over the same point `x` of `X` with
finite residue field are related by a positive power of the geometric Galois Frobenius `g_X`, up
to reparametrisation by an automorphism `g` of `Spec k̄` commuting with `σ`:

```
             s
  Spec k̄ -------> X
    ^             |
    g           g_Xʲ
    |             v
  Spec k̄ -------> X
             s'
```

that is `g ≫ s = s' ≫ g_Xʲ`. The residue field embeddings `κ(x) ↪ k̄` of `s` and `s'` differ by
an element of `Gal(κ(x) / k)`, a power of the Frobenius. -/
theorem exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow [Finite k]
    (s s' : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber)
    (hss' : (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) =
      (s' ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _))
    (hx : (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) ∈ X.finitePoints) :
    ∃ (g : Spec (.of (AlgebraicClosure k)) ≅ Spec (.of (AlgebraicClosure k))) (j : ℕ), 1 ≤ j ∧
      g.hom ≫ s = s' ≫ (f.geometricGaloisFrobenius ^ j).asIso.hom ∧
      ∀ m : ℕ, g.hom ≫ (specGeometricFrobenius k ^ m).asIso.hom =
        (specGeometricFrobenius k ^ m).asIso.hom ≫ g.hom := by
  let := Fintype.ofFinite k
  set x := (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _)
  have : Finite (X.residueField x) := X.mem_finitePoints.1 hx
  obtain ⟨ι, hι⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField _ x rfl
  obtain ⟨ι', hι'⟩ :=
    Scheme.exists_eq_spec_map_comp_fromSpecResidueField (s' ≫ f.geometricFiberProj) x hss'.symm
  have hc := f.residueFieldAlgebraMap_comp_eq_of_comp_geometricFiberProj s ι hι
  have hc' := f.residueFieldAlgebraMap_comp_eq_of_comp_geometricFiberProj s' ι' hι'
  set α := Spec.preimage (s ≫ f.geometricFiberToAlgebraicClosure)
  set α' := Spec.preimage (s' ≫ f.geometricFiberToAlgebraicClosure)
  let αe := RingEquiv.ofBijective α.hom (FiniteField.bijective_ringHom_of_isAlgClosed _ k _)
  let ι₁ : X.residueField x →+* AlgebraicClosure k := α'.hom.comp (αe.symm.toRingHom.comp ι.hom)
  have h₁ : ι₁.comp (f.residueFieldAlgebraMap x) = ι'.hom.comp (f.residueFieldAlgebraMap x) := by
    refine RingHom.ext fun c ↦ ?_
    have e₁ := RingHom.congr_fun hc c
    have e₂ := RingHom.congr_fun hc' c
    simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂ ⊢
    rw [e₂]
    change α'.hom (αe.symm (ι.hom _)) = _
    rw [e₁]
    exact congrArg α'.hom (αe.symm_apply_apply _)
  obtain ⟨i, hi⟩ := FiniteField.exists_apply_eq_pow_card_pow_of_comp_eq _ h₁
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  have hE : Nat.card (X.residueField x) =
      Fintype.card k ^ Module.finrank k (X.residueField x) := by
    rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]
  obtain ⟨j, hj, hφ⟩ := FiniteField.exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq k
    (AlgebraicClosure k) Module.finrank_pos hE ι₁ i
  let φj :=
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ j).toRingEquiv
  let αe' := RingEquiv.ofBijective α'.hom (FiniteField.bijective_ringHom_of_isAlgClosed _ k _)
  let γ : AlgebraicClosure k ≃+* AlgebraicClosure k := αe.symm.trans (φj.trans αe')
  have hg : (Scheme.Spec.mapIso γ.toCommRingCatIso.op).hom =
      Spec.map (CommRingCat.ofHom γ.toRingHom) := rfl
  refine ⟨Scheme.Spec.mapIso γ.toCommRingCatIso.op, j, hj, ?_, fun m ↦ ?_⟩
  · ext
    · rw [Category.assoc, Category.assoc, geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj,
        hι, hι', hg, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      change αe' (φj (αe.symm (ι a))) = ι' a
      rw [hi, ← hφ]
      exact FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply k (AlgebraicClosure k)
        α'.hom j (αe.symm (ι a))
    · rw [Category.assoc, Category.assoc,
        geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
        ← Category.assoc s',
        ← Spec.map_preimage (s ≫ f.geometricFiberToAlgebraicClosure),
        ← Spec.map_preimage (s' ≫ f.geometricFiberToAlgebraicClosure),
        specGeometricFrobenius_pow_hom, hg, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext y
      change αe' (φj (αe.symm (α.hom y))) = α'.hom (φj y)
      rw [show αe.symm (α.hom y) = y from αe.symm_apply_apply y]
      rfl
  · rw [specGeometricFrobenius_pow_hom, hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact (FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply k _ γ.toRingHom m y)

/-- The geometric point over a point `g : Spec K ⟶ X` with values in a field lies over the image
point of `g`. -/
theorem geometricFiberPoint_comp_geometricFiberProj_base {K : Type u} [Field K] [Algebra k K]
    (ι : K →ₐ[k] AlgebraicClosure k) (g : Spec (.of K) ⟶ X)
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    (f.geometricFiberPoint ι g hg ≫ f.geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k)) =
      g.base (IsLocalRing.closedPoint K) := by
  rw [geometricFiberPoint_comp_geometricFiberProj]
  exact congrArg g.base (Subsingleton.elim _ _)

/-- The geometric point over a point `x` with finite residue field lies over `x`. -/
theorem geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base (x : X.finitePoints) :
    (f.geometricFiberPointOfFinitePoint x ≫ f.geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k)) = x.1 :=
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  (geometricFiberPoint_comp_geometricFiberProj_base (K := X.residueField x.1) f IsAlgClosed.lift _
    (f.specMap_residueFieldAlgebraMap x.1).symm).trans (X.fromSpecResidueField_apply x.1 _)

/-- A point of `X` with values in a finite field with `#k ^ n` elements, `n ≥ 1`, lies over a
point whose degree divides `n`: its residue field embeds into the finite field. -/
theorem degreeOver_dvd_of_fieldPoints [Finite k] (n : ℕ)
    (y : f.fieldPoints (FiniteField.galoisExtension k n)) :
    f.degreeOver (y.1.base (IsLocalRing.closedPoint _)) ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  set x := y.1.base (IsLocalRing.closedPoint _)
  let := (f.residueFieldAlgebraMap x).toAlgebra
  obtain ⟨ι, hι⟩ := Scheme.exists_eq_spec_map_comp_fromSpecResidueField y.1 x rfl
  have h : ι.hom.comp (f.residueFieldAlgebraMap x) =
      algebraMap k (FiniteField.galoisExtension k n) := by
    have h₀ := y.2
    rw [hι, Category.assoc, ← f.specMap_residueFieldAlgebraMap, ← Spec.map_comp] at h₀
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h₀)
  have : Nonempty (X.residueField x →ₐ[k] FiniteField.galoisExtension k n) :=
    ⟨{ toRingHom := ι.hom, commutes' := fun c ↦ RingHom.congr_fun h c }⟩
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd, FiniteField.finrank_galoisExtension k n hn]
    at this
  exact this

end AlgebraicGeometry.Scheme.Hom
