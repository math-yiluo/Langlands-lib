/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Frobenius
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.FieldTheory.Finite.Polynomial

/-!
# The affine and projective lines

Over a scheme `S`, the projective line `ℙ¹_S = ProjectiveLine S` is covered by two copies of the
affine line `𝔸¹_S = 𝔸(PUnit; S)`: the affine chart `t ↦ [t : 1]` of
`AlgebraicGeometry.ProjectiveLine.affineChart` and the chart at infinity `z ↦ [1 : z]`. This
file shows that `ℙ¹_S` is glued from them along `t = z⁻¹`, that the complement of the affine
chart is the point `∞ = [1 : 0]`, and how the `q`-power Frobenius of `ℙ¹_F` acts on the charts
over a finite field `F` with `q` elements.

## Main definitions

- `AlgebraicGeometry.ProjectiveLine.infinityChart`: the chart at infinity `𝔸¹_S ↪ ℙ¹_S`,
  `z ↦ [1 : z]`, onto `D₊(T₀)`.
- `AlgebraicGeometry.ProjectiveLine.infinity`: the point at infinity `∞ : S ⟶ ℙ¹_S`, the section
  `z = 0` of the chart at infinity.

## Main results

- `AlgebraicGeometry.ProjectiveLine.isPullback_affineChart_infinityChart`: the two charts
  intersect in the locus `t ≠ 0` of the affine chart, which the chart at infinity sees through
  `z = t⁻¹`.
- `AlgebraicGeometry.ProjectiveLine.opensRange_affineChart_sup_opensRange_infinityChart`: the two
  charts cover `ℙ¹_S`.
- `AlgebraicGeometry.ProjectiveLine.range_infinity`: the complement of the affine chart is the
  image of `∞`; over a field it is a single point
  (`AlgebraicGeometry.ProjectiveLine.compl_opensRange_affineChart_eq_singleton`).
- `AlgebraicGeometry.ProjectiveLine.affineChart_comp_eq_of_isFrobenius`,
  `AlgebraicGeometry.ProjectiveLine.infinityChart_comp_eq_of_isFrobenius`: the `q`-power
  Frobenius acts by `t ↦ t ^ q` and `z ↦ z ^ q` on the charts `Spec F[t]` and `Spec F[z]`.

## Implementation details

Here `ℙ¹_F` is defined as `ℙ(ULift (Fin 2); Spec F)` rather than by gluing `Spec F[t]` and
`Spec F[z]` along `F[t, t⁻¹] = F[z, z⁻¹]`; the gluing description is the theorem
`isPullback_affineChart_infinityChart` together with the covering statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

variable {X S : Scheme.{u}}

/-- The homogeneous coordinates `[a : b]` on `ℙ¹`: the family of global sections indexed by
`ULift (Fin 2)` with value `a` at `0` and `b` at `1`. -/
def pairSections (a b : Γ(X, ⊤)) : ULift.{u} (Fin 2) → Γ(X, ⊤) := fun i ↦ ![a, b] i.down

@[simp]
lemma pairSections_zero (a b : Γ(X, ⊤)) : pairSections a b ⟨0⟩ = a := rfl

@[simp]
lemma pairSections_one (a b : Γ(X, ⊤)) : pairSections a b ⟨1⟩ = b := rfl

/-- The sections `[a : 1]` generate the unit ideal. -/
lemma span_range_pairSections_one (a : Γ(X, ⊤)) :
    Ideal.span (Set.range (pairSections a 1)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨1⟩, rfl⟩) isUnit_one

/-- The sections `[1 : b]` generate the unit ideal. -/
lemma span_range_one_pairSections (b : Γ(X, ⊤)) :
    Ideal.span (Set.range (pairSections 1 b)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) isUnit_one

/-- The standard open `D₊(T₀)` of `ℙ¹_S` has a single affine coordinate `T₁ / T₀`. -/
private lemma subsingleton_ne_zero : Subsingleton {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
  ⟨fun ⟨⟨a⟩, ha⟩ ⟨⟨b⟩, hb⟩ ↦ by
    have ha : a = 1 := by grind
    have hb : b = 1 := by grind
    subst ha hb
    rfl⟩

instance : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  have := subsingleton_ne_zero.{u}
  refine ⟨AffineSpace.reindex (fun _ ↦ ⟨⟨1⟩, by simp⟩) S, ?_, ?_⟩ <;>
    refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun i ↦ ?_ <;>
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
      AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  exact congrArg _ (Subsingleton.elim _ _)

variable (S) in
/-- **The chart at infinity of the projective line**: the open immersion `𝔸¹_S ↪ ℙ¹_S`,
`z ↦ [1: z]`, onto the standard open `D₊(T₀)`. Its coordinate is `z = T₁ / T₀`, the inverse
of the coordinate `t = T₀ / T₁` of `affineChart`. -/
def infinityChart : 𝔸(PUnit.{u + 1}; S) ⟶ ProjectiveLine S :=
  AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ PUnit.unit) S ≫
    (standardOpenIso (ULift.{u} (Fin 2)) S ⟨0⟩).inv ≫ (standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩).ι

instance : IsOpenImmersion (infinityChart S) := by
  rw [infinityChart]
  infer_instance

@[reassoc (attr := simp)]
lemma infinityChart_over :
    infinityChart S ≫ ProjectiveLine S ↘ S = 𝔸(PUnit.{u + 1}; S) ↘ S := by
  rw [infinityChart, Category.assoc, Category.assoc, standardOpenIso_inv_ι_over,
    AffineSpace.reindex_over]

instance : (infinityChart S).IsOver S := ⟨infinityChart_over⟩

variable (S) in
/-- The image of the chart at infinity is the standard open `D₊(T₀)`. -/
lemma opensRange_infinityChart :
    (infinityChart S).opensRange = standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩ := by
  unfold infinityChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- The point `t = a` of the affine chart is the point `[a : 1]` of `ℙ¹_S`. -/
lemma homOfVector_comp_affineChart (g : X ⟶ S) (a : Γ(X, ⊤)) :
    AffineSpace.homOfVector g (fun _ ↦ a) ≫ affineChart S =
      homOfSections g (pairSections a 1) (span_range_pairSections_one a) := by
  have := Scheme.Opens.isIso_ι_of_eq_top
    (X.basicOpen_of_isUnit (f := pairSections a 1 ⟨1⟩) isUnit_one)
  rw [← cancel_epi (X.basicOpen (pairSections a (1 : Γ(X, ⊤)) ⟨1⟩)).ι,
    ← Scheme.Hom.resLE_comp_ι (homOfSections g (pairSections a 1) (span_range_pairSections_one a))
      (homOfSections_preimage_standardOpen g _ (span_range_pairSections_one a) ⟨1⟩).ge,
    ← Iso.hom_inv_id_assoc (standardOpenIso (ULift.{u} (Fin 2)) S ⟨1⟩) (Scheme.Opens.ι _),
    reassoc_of% homOfSections_resLE_standardOpenIso_hom, affineChart]
  simp only [← Category.assoc]
  congr 2
  refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun j ↦ ?_
  rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
    AffineSpace.homOfVector_appTop_coord]
  obtain ⟨⟨j⟩, hj⟩ := j
  obtain rfl : j = 0 := by grind
  exact X.eq_divBasicOpen (by rw [pairSections_one, map_one, mul_one]; rfl)

/-- The point `z = b` of the chart at infinity is the point `[1 : b]` of `ℙ¹_S`. -/
lemma homOfVector_comp_infinityChart (g : X ⟶ S) (b : Γ(X, ⊤)) :
    AffineSpace.homOfVector g (fun _ ↦ b) ≫ infinityChart S =
      homOfSections g (pairSections 1 b) (span_range_one_pairSections b) := by
  have := Scheme.Opens.isIso_ι_of_eq_top
    (X.basicOpen_of_isUnit (f := pairSections 1 b ⟨0⟩) isUnit_one)
  rw [← cancel_epi (X.basicOpen (pairSections (1 : Γ(X, ⊤)) b ⟨0⟩)).ι,
    ← Scheme.Hom.resLE_comp_ι (homOfSections g (pairSections 1 b) (span_range_one_pairSections b))
      (homOfSections_preimage_standardOpen g _ (span_range_one_pairSections b) ⟨0⟩).ge,
    ← Iso.hom_inv_id_assoc (standardOpenIso (ULift.{u} (Fin 2)) S ⟨0⟩) (Scheme.Opens.ι _),
    reassoc_of% homOfSections_resLE_standardOpenIso_hom, infinityChart]
  simp only [← Category.assoc]
  congr 2
  refine AffineSpace.hom_ext (by simp [AffineSpace.reindex_over]) fun j ↦ ?_
  rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
    AffineSpace.homOfVector_appTop_coord]
  obtain ⟨⟨j⟩, hj⟩ := j
  obtain rfl : j = 1 := by grind
  exact X.eq_divBasicOpen (by rw [pairSections_zero, map_one, mul_one]; rfl)

/-- The coordinate `𝔸¹_S ⟶ 𝔸¹_S` is the identity. -/
lemma homOfVector_over_coord :
    AffineSpace.homOfVector (𝔸(PUnit.{u + 1}; S) ↘ S) (fun _ ↦ AffineSpace.coord S PUnit.unit) =
      𝟙 _ :=
  AffineSpace.hom_ext (by simp) fun _ ↦ by simp

variable (S) in
/-- The affine chart is `t ↦ [t : 1]`. -/
lemma affineChart_eq_homOfSections :
    affineChart S = homOfSections (𝔸(PUnit.{u + 1}; S) ↘ S)
      (pairSections (AffineSpace.coord S PUnit.unit) 1) (span_range_pairSections_one _) := by
  rw [← homOfVector_comp_affineChart, homOfVector_over_coord, Category.id_comp]

variable (S) in
/-- The chart at infinity is `z ↦ [1 : z]`. -/
lemma infinityChart_eq_homOfSections :
    infinityChart S = homOfSections (𝔸(PUnit.{u + 1}; S) ↘ S)
      (pairSections 1 (AffineSpace.coord S PUnit.unit)) (span_range_one_pairSections _) := by
  rw [← homOfVector_comp_infinityChart, homOfVector_over_coord, Category.id_comp]

/-- **The transition map of the two charts of `ℙ¹`**: the point `t = u` of the affine chart is
the point `z = u⁻¹` of the chart at infinity, for a unit `u`. -/
lemma homOfVector_comp_affineChart_eq (g : X ⟶ S) (u : Γ(X, ⊤)ˣ) :
    AffineSpace.homOfVector g (fun _ ↦ (u : Γ(X, ⊤))) ≫ affineChart S =
      AffineSpace.homOfVector g (fun _ ↦ ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))) ≫ infinityChart S := by
  rw [homOfVector_comp_affineChart, homOfVector_comp_infinityChart]
  refine homOfSections_eq_of_unit_mul g u⁻¹ _ _ fun ⟨i⟩ ↦ ?_
  fin_cases i <;> simp [pairSections]

variable (S) in
/-- A point of the affine chart lies in the chart at infinity if and only if `t ≠ 0` there. -/
lemma affineChart_preimage_opensRange_infinityChart :
    affineChart S ⁻¹ᵁ (infinityChart S).opensRange =
      𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit) := by
  rw [opensRange_infinityChart, affineChart_eq_homOfSections,
    homOfSections_preimage_standardOpen, pairSections_zero]

variable (S) in
/-- A point of the chart at infinity lies in the affine chart if and only if `z ≠ 0` there. -/
lemma infinityChart_preimage_opensRange_affineChart :
    infinityChart S ⁻¹ᵁ (affineChart S).opensRange =
      𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit) := by
  rw [opensRange_affineChart, infinityChart_eq_homOfSections,
    homOfSections_preimage_standardOpen, pairSections_one]

variable (S) in
/-- **`ℙ¹_S` is glued from two affine lines along `z = t⁻¹`**: the square
```
  D(t) ──── z = t⁻¹ ───▶ 𝔸¹_S
   │                       │
   ι                 infinityChart
   ▼                       ▼
  𝔸¹_S ── affineChart ──▶ ℙ¹_S
```
is cartesian, where `D(t) ⊆ 𝔸¹_S` is the locus where the coordinate `t` is invertible. Over
`S = Spec F` this is the gluing of `Spec F[t]` and `Spec F[z]` along `F[t, t⁻¹] = F[z, z⁻¹]`. -/
theorem isPullback_affineChart_infinityChart :
    IsPullback
      (AffineSpace.homOfVector
        ((𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit)).ι ≫
          𝔸(PUnit.{u + 1}; S) ↘ S)
        (fun _ ↦ (((𝔸(PUnit.{u + 1}; S).basicOpenUnit (AffineSpace.coord S PUnit.unit))⁻¹ :
          Γ(_, ⊤)ˣ) : Γ(_, ⊤))))
      (𝔸(PUnit.{u + 1}; S).basicOpen (AffineSpace.coord S PUnit.unit)).ι
      (infinityChart S) (affineChart S) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← homOfVector_comp_affineChart_eq]
    congr 1
    exact AffineSpace.hom_ext (by simp) fun _ ↦ by simp [Scheme.basicOpenUnit]
  · rw [affineChart_preimage_opensRange_infinityChart, Scheme.Opens.opensRange_ι]

variable (S) in
/-- The two charts cover `ℙ¹_S`. -/
theorem opensRange_affineChart_sup_opensRange_infinityChart :
    (affineChart S).opensRange ⊔ (infinityChart S).opensRange = ⊤ := by
  rw [opensRange_affineChart, opensRange_infinityChart, eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ i, standardOpen (ULift.{u} (Fin 2)) S i := by
    rw [iSup_standardOpen]
    trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨⟨i⟩, hi⟩ := hx
  fin_cases i
  · exact Or.inr hi
  · exact Or.inl hi

variable (S) in
/-- **The point at infinity** `∞ = [1: 0]` of `ℙ¹_S`, the section `z = 0` of the chart at
infinity. -/
def infinity : S ⟶ ProjectiveLine S :=
  AffineSpace.zeroSection PUnit.{u + 1} S ≫ infinityChart S

/-- `∞` is a section of `ℙ¹_S ⟶ S`. -/
@[reassoc (attr := simp)]
lemma infinity_over : infinity S ≫ ProjectiveLine S ↘ S = 𝟙 S := by
  simp [infinity]

variable (S) in
/-- **The complement of the affine chart is the point at infinity**: a point of `ℙ¹_S` lies
outside the image of `affineChart` if and only if it lies on the section `∞`. -/
theorem range_infinity :
    Set.range (infinity S) = ((affineChart S).opensRange : Set (ProjectiveLine S))ᶜ := by
  have hz := AffineSpace.range_zeroSection PUnit.{u + 1} S
  ext x
  constructor
  · rintro ⟨s, rfl⟩ hx
    have hs : AffineSpace.zeroSection PUnit.{u + 1} S s ∈
        infinityChart S ⁻¹ᵁ (affineChart S).opensRange := hx
    rw [infinityChart_preimage_opensRange_affineChart] at hs
    exact (hz.le ⟨s, rfl⟩ : _) PUnit.unit hs
  · intro hx
    have hx' : x ∈ (affineChart S).opensRange ⊔ (infinityChart S).opensRange := by
      rw [opensRange_affineChart_sup_opensRange_infinityChart]
      trivial
    obtain ⟨y, rfl⟩ : x ∈ Set.range (infinityChart S) := hx'.resolve_left hx
    have hy : y ∈ Set.range (AffineSpace.zeroSection PUnit.{u + 1} S) := by
      rw [hz]
      rintro ⟨⟩ hy
      rw [← infinityChart_preimage_opensRange_affineChart] at hy
      exact hx hy
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s, rfl⟩

/-- Over a field `K`, the complement of the affine chart of `ℙ¹_K` is the single point `∞`. -/
theorem compl_opensRange_affineChart_eq_singleton (K : Type u) [Field K] :
    ((affineChart (Spec (.of K))).opensRange : Set (ProjectiveLine (Spec (.of K))))ᶜ =
      {infinity (Spec (.of K)) (IsLocalRing.closedPoint K)} := by
  rw [← range_infinity]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint K)]
    rfl
  · rintro rfl
    exact ⟨_, rfl⟩

section Frobenius

variable (F : Type u) [Field F] [Finite F]
  {Φ : ProjectiveLine (Spec (.of F)) ⟶ ProjectiveLine (Spec (.of F))}

/-- **Frobenius on the affine chart**: the `q`-power Frobenius `Φ` of `ℙ¹_F`, `q = |F|`, acts
on the affine chart `Spec F[t]` by `t ↦ t ^ q`. -/
theorem affineChart_comp_eq_of_isFrobenius (hΦ : Φ.IsFrobenius (Nat.card F)) :
    (AffineSpace.SpecIso PUnit.{u + 1} (.of F)).inv ≫ affineChart _ ≫ Φ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.expand (Nat.card F)).toRingHom) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of F)).inv ≫ affineChart _ := by
  rw [← Category.assoc]
  exact hΦ _ _ MvPolynomial.expand_natCard

/-- **Frobenius on the chart at infinity**: the `q`-power Frobenius `Φ` of `ℙ¹_F`, `q = |F|`,
acts on the chart at infinity `Spec F[z]` by `z ↦ z ^ q`. -/
theorem infinityChart_comp_eq_of_isFrobenius (hΦ : Φ.IsFrobenius (Nat.card F)) :
    (AffineSpace.SpecIso PUnit.{u + 1} (.of F)).inv ≫ infinityChart _ ≫ Φ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.expand (Nat.card F)).toRingHom) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of F)).inv ≫ infinityChart _ := by
  rw [← Category.assoc]
  exact hΦ _ _ MvPolynomial.expand_natCard

end Frobenius

end AlgebraicGeometry.ProjectiveLine
