/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.FieldTheory.Finite.GaloisField
public import WeilConjectures.PointCount

/-!
# Counting Frobenius-fixed points over closed points

Let `X` be a scheme over a finite field `k` with `q` elements, `Ω` an algebraically closed field
extension of `k` and `ψ : x ↦ x ^ (q ^ m)` the `m`-th power of the arithmetic Frobenius of `Ω`,
`m ≥ 1`. The `Ω`-points `g : Spec Ω ⟶ X` over `k` with `Spec ψ ≫ g = g` are the points of `X`
rational over `𝔽_{q^m} ⊆ Ω`. A point `g` lying over `y ∈ X` is the same as a `k`-embedding
`κ(y) ↪ Ω`, and `g` is fixed exactly when the embedding takes values in `𝔽_{q^m}`. Hence the
fixed points over `y` are the `k`-embeddings `κ(y) ↪ 𝔽_{q^m}`: there are `deg y` of them if
`deg y ∣ m`, and none otherwise.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.fixedFieldPoints`: the `Ω`-points of `X` over `k` fixed by a ring
  endomorphism `ψ` of `Ω`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.natCard_fixedFieldPoints_fiber`: the number of fixed points over
  a point `y` is `deg y` if `deg y ∣ m`, and `0` otherwise.
- `AlgebraicGeometry.Scheme.Hom.mem_finitePoints_of_mem_fixedFieldPoints`: a fixed point lies
  over a closed point whose degree divides `m`.
- `AlgebraicGeometry.Scheme.Hom.finite_fixedFieldPoints`: for `X` of finite type over `k` there
  are finitely many fixed points.
- `AlgebraicGeometry.Scheme.Hom.sum_fixedFieldPoints`: a sum over the fixed points of a function
  of the underlying point is `∑_{deg y ∣ m} deg y • h y`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- A morphism `Spec Ω ⟶ X` factoring through `Spec κ(y)` determines the embedding
`κ(y) ↪ Ω`. -/
theorem specMap_comp_fromSpecResidueField_injective (y : X) :
    Function.Injective fun φ : X.residueField y ⟶ .of Ω ↦
      Spec.map φ ≫ X.fromSpecResidueField y :=
  fun φ φ' h ↦ eq_of_heq (Sigma.mk.inj_iff.1
    ((SpecToEquivOfField Ω X).symm.injective (a₁ := ⟨y, φ⟩) (a₂ := ⟨y, φ'⟩) h)).2

/-- A morphism `g : Spec Ω ⟶ X` with image `y` factors through `Spec κ(y)`. -/
theorem exists_eq_specMap_comp_fromSpecResidueField (g : Spec (.of Ω) ⟶ X) {y : X}
    (hy : y ∈ Set.range g.base) :
    ∃ φ : X.residueField y ⟶ .of Ω, g = Spec.map φ ≫ X.fromSpecResidueField y := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective g
  obtain ⟨t, ht⟩ := hy
  obtain rfl : z = y := by
    rw [← ht]
    simp [SpecToEquivOfField]
  exact ⟨φ, rfl⟩

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Algebra k Ω]

/-- The morphism `Spec Ω ⟶ X` induced by an embedding `φ : κ(y) ↪ Ω` lies over `k` if and only
if `φ` is compatible with the embeddings of `k`. -/
theorem Hom.specMap_comp_fromSpecResidueField_comp_eq_iff (y : X)
    (φ : X.residueField y ⟶ .of Ω) :
    (Spec.map φ ≫ X.fromSpecResidueField y) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ↔
      φ.hom.comp (f.residueFieldAlgebraMap y) = algebraMap k Ω := by
  rw [Category.assoc, ← f.specMap_residueFieldAlgebraMap y, ← Spec.map_comp, Spec.map_inj]
  exact ⟨fun h ↦ congrArg CommRingCat.Hom.hom h, fun h ↦ CommRingCat.hom_ext h⟩

/-- The morphism `Spec Ω ⟶ X` induced by an embedding `φ : κ(y) ↪ Ω` is fixed by a ring
endomorphism `ψ` of `Ω` if and only if `ψ ∘ φ = φ`. -/
theorem specMap_comp_specMap_comp_fromSpecResidueField_eq_iff (y : X)
    (φ : X.residueField y ⟶ .of Ω) (ψ : Ω →+* Ω) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map φ ≫ X.fromSpecResidueField y =
        Spec.map φ ≫ X.fromSpecResidueField y ↔ φ ≫ CommRingCat.ofHom ψ = φ := by
  rw [← Category.assoc, ← Spec.map_comp]
  exact (specMap_comp_fromSpecResidueField_injective y).eq_iff

/-- The `Ω`-points `g : Spec Ω ⟶ X` over `k` fixed by a ring endomorphism `ψ` of `Ω`, that is,
with `Spec ψ ≫ g = g`. For `ψ` the `m`-th power of the arithmetic Frobenius `x ↦ x ^ q` of `Ω`,
these are the points of `X` rational over `𝔽_{q^m}`. -/
def Hom.fixedFieldPoints (ψ : Ω →+* Ω) : Set (Spec (.of Ω) ⟶ X) :=
  {g | g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    Spec.map (CommRingCat.ofHom ψ) ≫ g = g}

/-- Membership in `AlgebraicGeometry.Scheme.Hom.fixedFieldPoints`. -/
theorem Hom.mem_fixedFieldPoints_iff (ψ : Ω →+* Ω) (g : Spec (.of Ω) ⟶ X) :
    g ∈ f.fixedFieldPoints ψ ↔ g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ g = g :=
  Iff.rfl

/-- The morphism `Spec Ω ⟶ X` induced by an embedding `φ : κ(y) ↪ Ω` is a fixed point of `ψ` if
and only if `φ` is a `k`-embedding with `ψ ∘ φ = φ`. -/
theorem Hom.specMap_comp_fromSpecResidueField_mem_fixedFieldPoints_iff (ψ : Ω →+* Ω) (y : X)
    (φ : X.residueField y ⟶ .of Ω) :
    Spec.map φ ≫ X.fromSpecResidueField y ∈ f.fixedFieldPoints ψ ↔
      φ.hom.comp (f.residueFieldAlgebraMap y) = algebraMap k Ω ∧
        φ ≫ CommRingCat.ofHom ψ = φ := by
  rw [mem_fixedFieldPoints_iff, specMap_comp_fromSpecResidueField_comp_eq_iff,
    specMap_comp_specMap_comp_fromSpecResidueField_eq_iff]

/-- The `ψ`-fixed `Ω`-point of `X` over `y` induced by a `k`-embedding `κ(y) ↪ E` into a finite
field `E ⊆ Ω` whose elements are fixed by `ψ : x ↦ x ^ #E`. -/
noncomputable def Hom.fixedFieldPointOfAlgHom (E : Type u) [Field E] [Fintype E] [Algebra k E]
    (ι : E →ₐ[k] Ω) (ψ : Ω →+* Ω) (hψ : ∀ a, ψ a = a ^ Fintype.card E) (y : X) :
    let := (f.residueFieldAlgebraMap y).toAlgebra
    (X.residueField y →ₐ[k] E) → {g : f.fixedFieldPoints ψ // g.1.base default = y} :=
  let := (f.residueFieldAlgebraMap y).toAlgebra
  fun φ' ↦ ⟨⟨Spec.map (CommRingCat.ofHom (ι.comp φ').toRingHom) ≫ X.fromSpecResidueField y,
    (f.specMap_comp_fromSpecResidueField_mem_fixedFieldPoints_iff ψ y _).2
      ⟨RingHom.ext fun a ↦ (ι.comp φ').commutes a,
        CommRingCat.hom_ext (RingHom.ext fun a ↦ (hψ _).trans
          ((FiniteField.pow_card_eq_self_iff_mem_range ι.toRingHom).2 ⟨φ' a, rfl⟩))⟩⟩,
    X.fromSpecResidueField_apply y _⟩

/-- The fixed points of `ψ : x ↦ x ^ #E` over a point `y` are the `k`-embeddings of `κ(y)` into
a finite field `E ⊆ Ω`: the image of `E` consists exactly of the elements of `Ω` fixed by `ψ`. -/
theorem Hom.bijective_fixedFieldPointOfAlgHom (E : Type u) [Field E] [Fintype E] [Algebra k E]
    (ι : E →ₐ[k] Ω) (ψ : Ω →+* Ω) (hψ : ∀ a, ψ a = a ^ Fintype.card E) (y : X) :
    Function.Bijective (f.fixedFieldPointOfAlgHom E ι ψ hψ y) := by
  let := (f.residueFieldAlgebraMap y).toAlgebra
  refine ⟨fun φ₁ φ₂ h ↦ ?_, fun g ↦ ?_⟩
  · have h' := specMap_comp_fromSpecResidueField_injective y
      (congrArg Subtype.val (congrArg Subtype.val h))
    exact AlgHom.ext fun a ↦ ι.injective (congrArg (fun χ ↦ χ.hom a) h')
  · obtain ⟨φ, hφ⟩ := exists_eq_specMap_comp_fromSpecResidueField g.1.1 ⟨default, g.2⟩
    have hmem := g.1.2
    rw [hφ, specMap_comp_fromSpecResidueField_mem_fixedFieldPoints_iff] at hmem
    let φa : X.residueField y →ₐ[k] Ω :=
      { φ.hom with commutes' := fun a ↦ RingHom.congr_fun hmem.1 a }
    have hrange (a : X.residueField y) : φa a ∈ ι.range := by
      obtain ⟨b, hb⟩ := (FiniteField.pow_card_eq_self_iff_mem_range ι.toRingHom).1
        ((hψ _).symm.trans (congrArg (fun χ ↦ χ.hom a) hmem.2))
      exact ⟨b, hb⟩
    refine ⟨(AlgEquiv.ofInjective ι ι.injective).symm.toAlgHom.comp
      (φa.codRestrict ι.range hrange), Subtype.ext (Subtype.ext ?_)⟩
    refine Eq.trans (congrArg (fun χ ↦ Spec.map χ ≫ X.fromSpecResidueField y)
      (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_))) hφ.symm
    exact congrArg Subtype.val ((AlgEquiv.ofInjective ι ι.injective).apply_symm_apply
      ⟨φa a, hrange a⟩)

variable [Finite k] [IsAlgClosed Ω]

/-- The degree `m` extension of `k` embeds into `Ω`, and its `k`-embeddings into `Ω` are the
`ψ`-fixed points for `ψ : x ↦ x ^ (q ^ m)`. -/
private lemma exists_algHomEquivFixedFieldPointsFiber {m : ℕ} (hm : m ≠ 0) (ψ : Ω →+* Ω)
    (hψ : ∀ a, ψ a = a ^ (Nat.card k ^ m)) (y : X) :
    letI := (f.residueFieldAlgebraMap y).toAlgebra
    Nonempty ((X.residueField y →ₐ[k] FiniteField.galoisExtension k m) ≃
      {g : f.fixedFieldPoints ψ // g.1.base default = y}) := by
  let := (f.residueFieldAlgebraMap y).toAlgebra
  have : Finite (FiniteField.galoisExtension k m) := Module.finite_of_finite k
  let := Fintype.ofFinite (FiniteField.galoisExtension k m)
  have hE : Fintype.card (FiniteField.galoisExtension k m) = Nat.card k ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k m hm]
  have hψ' (a : Ω) : ψ a = a ^ Fintype.card (FiniteField.galoisExtension k m) := by
    rw [hψ, hE]
  exact ⟨Equiv.ofBijective _ (f.bijective_fixedFieldPointOfAlgHom _
    (IsAlgClosed.lift : FiniteField.galoisExtension k m →ₐ[k] Ω) ψ hψ' y)⟩

/-- **Fixed points over a point.** For `ψ : x ↦ x ^ (q ^ m)`, `m ≥ 1`, the number of `ψ`-fixed
`Ω`-points of `X` lying over a point `y` is `deg y` if `deg y ∣ m`, and `0` otherwise. -/
theorem Hom.natCard_fixedFieldPoints_fiber {m : ℕ} (hm : m ≠ 0) (ψ : Ω →+* Ω)
    (hψ : ∀ a, ψ a = a ^ (Nat.card k ^ m)) (y : X) :
    Nat.card {g : f.fixedFieldPoints ψ // g.1.base default = y} =
      if f.degreeOver y ∣ m then f.degreeOver y else 0 := by
  let := (f.residueFieldAlgebraMap y).toAlgebra
  obtain ⟨e⟩ := exists_algHomEquivFixedFieldPointsFiber f hm ψ hψ y
  have : Finite (FiniteField.galoisExtension k m) := Module.finite_of_finite k
  rw [← Nat.card_congr e]
  by_cases hdvd : f.degreeOver y ∣ m
  · rw [ite_eq_left hdvd]
    have hdvd' : Module.finrank k (X.residueField y) ∣
        Module.finrank k (FiniteField.galoisExtension k m) := by
      rw [FiniteField.finrank_galoisExtension k m hm]
      exact hdvd
    rw [FiniteField.natCard_algHom_of_finrank_dvd hdvd']
    rfl
  · rw [ite_eq_right hdvd]
    have : IsEmpty (X.residueField y →ₐ[k] FiniteField.galoisExtension k m) := by
      rw [← not_nonempty_iff, FiniteField.nonempty_algHom_iff_finrank_dvd,
        FiniteField.finrank_galoisExtension k m hm]
      exact hdvd
    exact Nat.card_of_isEmpty

/-- A `ψ`-fixed `Ω`-point of `X`, for `ψ : x ↦ x ^ (q ^ m)` and `m ≥ 1`, lies over a point with
finite residue field whose degree divides `m`. -/
theorem Hom.mem_finitePoints_of_mem_fixedFieldPoints {m : ℕ} (hm : m ≠ 0) (ψ : Ω →+* Ω)
    (hψ : ∀ a, ψ a = a ^ (Nat.card k ^ m)) {g : Spec (.of Ω) ⟶ X}
    (hg : g ∈ f.fixedFieldPoints ψ) :
    g.base default ∈ X.finitePoints ∧ f.degreeOver (g.base default) ∣ m := by
  let := (f.residueFieldAlgebraMap (g.base default)).toAlgebra
  obtain ⟨e⟩ := exists_algHomEquivFixedFieldPointsFiber f hm ψ hψ (g.base default)
  have : Finite (FiniteField.galoisExtension k m) := Module.finite_of_finite k
  let φ := e.symm ⟨⟨g, hg⟩, rfl⟩
  refine ⟨X.mem_finitePoints.2 (Finite.of_injective φ φ.injective), ?_⟩
  have h := FiniteField.nonempty_algHom_iff_finrank_dvd.1 ⟨φ⟩
  rwa [FiniteField.finrank_galoisExtension k m hm] at h

/-- A scheme of finite type over `k` has finitely many `Ω`-points fixed by
`ψ : x ↦ x ^ (q ^ m)`, `m ≥ 1`. -/
theorem Hom.finite_fixedFieldPoints [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}
    (hm : m ≠ 0) (ψ : Ω →+* Ω) (hψ : ∀ a, ψ a = a ^ (Nat.card k ^ m)) :
    (f.fixedFieldPoints ψ).Finite := by
  have hfib (y : X.finitePoints) : Finite {g : f.fixedFieldPoints ψ // g.1.base default = y.1} := by
    let := (f.residueFieldAlgebraMap y.1).toAlgebra
    obtain ⟨e⟩ := exists_algHomEquivFixedFieldPointsFiber f hm ψ hψ y.1
    have : Finite (X.residueField y.1) := X.mem_finitePoints.1 y.2
    exact Finite.of_equiv _ e
  refine ((f.finite_setOf_degreeOver_le m).biUnion fun y _ ↦
    Set.finite_range fun g : {g : f.fixedFieldPoints ψ // g.1.base default = y.1} ↦
      g.1.1).subset fun g hg ↦ ?_
  obtain ⟨hfin, hdvd⟩ := f.mem_finitePoints_of_mem_fixedFieldPoints hm ψ hψ hg
  exact Set.mem_iUnion₂.2 ⟨⟨g.base default, hfin⟩, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd,
    ⟨⟨g, hg⟩, rfl⟩, rfl⟩

/-- **Regrouping a sum over fixed points.** For `ψ : x ↦ x ^ (q ^ m)`, `m ≥ 1`, and a function
`h` on the points of `X`, the sum of `h` over the underlying points of the `ψ`-fixed `Ω`-points
of `X` is `∑_{deg y ∣ m} deg y • h y`, over the closed points `y` of `X`; the sum may be taken
over any finite set `T` of closed points containing those of degree dividing `m`. -/
theorem Hom.sum_fixedFieldPoints {m : ℕ} (hm : m ≠ 0) (ψ : Ω →+* Ω)
    (hψ : ∀ a, ψ a = a ^ (Nat.card k ^ m)) [Fintype (f.fixedFieldPoints ψ)] {M : Type*}
    [AddCommMonoid M] (h : X → M) {T : Finset X.finitePoints}
    (hT : ∀ y : X.finitePoints, f.degreeOver y.1 ∣ m → y ∈ T) :
    ∑ g : f.fixedFieldPoints ψ, h (g.1.base default) =
      ∑ y ∈ T with f.degreeOver y.1 ∣ m, f.degreeOver y.1 • h y.1 := by
  classical
  let π : f.fixedFieldPoints ψ → X.finitePoints := fun g ↦
    ⟨g.1.base default, (f.mem_finitePoints_of_mem_fixedFieldPoints hm ψ hψ g.2).1⟩
  have hπ (g : f.fixedFieldPoints ψ) (_ : g ∈ Finset.univ) :
      π g ∈ T.filter fun y ↦ f.degreeOver y.1 ∣ m :=
    have hdvd := (f.mem_finitePoints_of_mem_fixedFieldPoints hm ψ hψ g.2).2
    Finset.mem_filter.2 ⟨hT _ hdvd, hdvd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hπ]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [Finset.sum_congr rfl fun g hg ↦ congrArg h (congrArg Subtype.val
    (Finset.mem_filter.1 hg).2), Finset.sum_const, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ Subtype.ext_iff),
    f.natCard_fixedFieldPoints_fiber hm ψ hψ, ite_eq_left (Finset.mem_filter.1 hy).2]

end AlgebraicGeometry.Scheme
