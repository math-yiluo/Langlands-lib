/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.RingTheory.GradedAlgebra.Standard

/-!
# Linear projections of `Proj` to projective space

Let `A` be a commutative `k`-algebra graded by `𝒜 : ℕ → Submodule k A`, and let `l : ι → A` be
a family of elements of degree one such that the basic opens `D₊(lᵢ)` cover `Proj 𝒜`. Then
`l` defines a morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)`, `x ↦ [lᵢ(x)]`. On the chart `D₊(lᵢ)` it is the
morphism given by the global sections `lⱼ / lᵢ` of `Spec (A_{lᵢ})₀`, which generate the unit
ideal since `lᵢ / lᵢ = 1`. Two such chart morphisms agree on the overlap `D₊(lᵢ lⱼ)`, as their
sections differ by the unit `lᵢ / lⱼ`, so they glue.

The case of a pair `l₀, l₁` gives the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`, which on `D₊(l₀)`
corresponds to the ring map `k[t] → A_(l₀)`, `t ↦ l₁ / l₀`, and on `D₊(l₁)` to the ring map
`k[t⁻¹] → A_(l₁)`, `t⁻¹ ↦ l₀ / l₁`.

## Main definitions

- `AlgebraicGeometry.Proj.toSpecBase` — the structure morphism `Proj 𝒜 ⟶ Spec k`.
- `AlgebraicGeometry.Proj.linearChartHom` — the morphism `Spec (A_{lᵢ})₀ ⟶ ℙ(ι; Spec k)`
  given by the sections `lⱼ / lᵢ`.
- `AlgebraicGeometry.Proj.linearProjection` — the morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)` defined by
  a family of linear forms without common zero.
- `AlgebraicGeometry.Proj.linearPairProjection` — the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.comp_homOfSections` — naturality of `homOfSections`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_eq_of_unit_mul` — rescaling the sections
  by a unit does not change `homOfSections`.
- `AlgebraicGeometry.Proj.linearChartHom_compatible` — the chart morphisms agree on overlaps.
- `AlgebraicGeometry.Proj.awayι_linearProjection` — on the chart `D₊(lᵢ)` the linear
  projection is `linearChartHom`.
- `AlgebraicGeometry.Proj.linearProjection_over` — the linear projection is a morphism over
  `Spec k`.
- `AlgebraicGeometry.Proj.linearProjection_preimage_standardOpen` — the preimage of `D₊(Tᵢ)` is
  `D₊(lᵢ)`.
- `AlgebraicGeometry.Proj.isFinite_linearProjection` — finiteness criterion for the linear
  projection.
- `AlgebraicGeometry.Proj.isFinite_linearPairProjection` — `π_{l₀,l₁}` is finite for a
  standard graded `k`-algebra.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y S : Scheme.{u}} {n : Type u}

/-- If global sections `s i` generate the unit ideal, so do their pullbacks along any
morphism of schemes. -/
lemma span_range_appTop_eq_top (h : Y ⟶ X) {s : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range fun i ↦ h.appTop.hom (s i)) = ⊤ := by
  rw [Set.range_comp' h.appTop.hom s, ← Ideal.map_span, hs, Ideal.map_top]

/-- `homOfSections` is natural in the source: precomposing with `h : Y ⟶ X` gives the morphism
attached to `h ≫ g` and the pulled back sections. -/
@[reassoc]
lemma comp_homOfSections (h : Y ⟶ X) (g : X ⟶ S) (s : n → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    h ≫ homOfSections g s hs =
      homOfSections (h ≫ g) (fun i ↦ h.appTop.hom (s i)) (span_range_appTop_eq_top h hs) := by
  refine hom_ext n S (by simp) ?_
  rw [Category.assoc, homOfSections_toProjInt, homOfSections_toProjInt,
    Proj.comp_fromOfGlobalSections _ h _ _ (Proj.map_irrelevant_comp_appTop_eq_top _ h _
      (map_irrelevant_evalSections_eq_top s hs))]
  congr 1
  exact comp_evalSections h s

/-- Rescaling all the sections by a unit `u` of `Γ(X, ⊤)` does not change `homOfSections`. -/
lemma homOfSections_eq_of_unit_mul (g : X ⟶ S) (u : Γ(X, ⊤)ˣ) {s s' : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) (hs' : Ideal.span (Set.range s') = ⊤)
    (hss' : ∀ i, s' i = u * s i) :
    homOfSections g s hs = homOfSections g s' hs' := by
  obtain rfl : s' = fun i ↦ u * s i := funext hss'
  refine hom_ext n S (by simp) ?_
  rw [homOfSections_toProjInt, homOfSections_toProjInt]
  exact Proj.fromOfGlobalSections_eq_of_unit_pow_mul _ u _ _
    (fun _ _ ha ↦ evalSections_const_mul _ _ ha) _ _

end ProjectiveSpace

namespace AffineSpace

/-- Let `A` be an `R`-algebra and `v : m → A` a family of elements. The morphism
`Spec A ⟶ 𝔸(m; Spec R)` given by the coordinates `v` is `Spec` of the ring map
`R[Yⱼ] → A`, `Yⱼ ↦ vⱼ`. -/
lemma homOfVector_SpecMap_eq {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type u} (v : m → A) :
    homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (fun j ↦ (Scheme.ΓSpecIso (.of A)).inv (v j)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) v).toRingHom) ≫
        (SpecIso m (.of R)).inv := by
  refine hom_ext ?_ fun j ↦ ?_
  · rw [homOfVector_over, Category.assoc, SpecIso_inv_over, ← Spec.map_comp]
    congr 1
    ext x
    simp
  · rw [homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      SpecIso_inv_appTop_coord]
    have h := congrArg (fun φ ↦ φ.hom (MvPolynomial.X j)) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MvPolynomial.aeval (R := R) v).toRingHom))
    exact (congrArg _ (MvPolynomial.aeval_X (R := R) v j).symm).trans h

/-- Let `A` be an `R`-algebra generated by a family `v : m → A`. Then the morphism
`Spec A ⟶ 𝔸(m; Spec R)` given by the coordinates `v` is a closed immersion. -/
lemma isClosedImmersion_homOfVector_SpecMap {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {m : Type u} (v : m → A) (hv : Algebra.adjoin R (Set.range v) = ⊤) :
    IsClosedImmersion (homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (fun j ↦ (Scheme.ΓSpecIso (.of A)).inv (v j))) := by
  rw [homOfVector_SpecMap_eq]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := R) v).toRingHom)) := by
    refine IsClosedImmersion.spec_of_surjective _ fun x ↦ ?_
    have hx : x ∈ Algebra.adjoin R (Set.range v) := hv ▸ trivial
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, rfl⟩
  infer_instance

/-- Let `A` be an `R`-algebra and `v : m → A` a family such that `A` is a finite module over
the subalgebra `R[v]`. Then the morphism `Spec A ⟶ 𝔸(m; Spec R)` given by the coordinates `v`
is finite: it is `Spec` of the finite ring map `R[Yⱼ] → A`, `Yⱼ ↦ vⱼ`. -/
lemma isFinite_homOfVector_SpecMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type u} (v : m → A) [Module.Finite (Algebra.adjoin R (Set.range v)) A] :
    IsFinite (homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (fun j ↦ (Scheme.ΓSpecIso (.of A)).inv (v j))) := by
  have hfin : (MvPolynomial.aeval (R := R) v).toRingHom.Finite := by
    have hle (p : MvPolynomial m R) :
        MvPolynomial.aeval v p ∈ Algebra.adjoin R (Set.range v) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨p, rfl⟩
    let f := (MvPolynomial.aeval (R := R) v).codRestrict _ hle
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [Algebra.adjoin_range_eq_range_aeval] at hx
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p, rfl⟩
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp
      (RingHom.Finite.of_surjective f.toRingHom hf)
  rw [homOfVector_SpecMap_eq]
  exact MorphismProperty.comp_mem @IsFinite _ _ ((IsFinite.SpecMap_iff _).mpr hfin)
    inferInstance

end AffineSpace

namespace Proj

section Construction

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- The structure morphism `Proj 𝒜 ⟶ Spec k` of the projective spectrum of a graded
`k`-algebra, i.e. `Proj 𝒜 ⟶ Spec A₀ ⟶ Spec k`. -/
def toSpecBase : Proj 𝒜 ⟶ Spec (.of k) :=
  toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))

variable {ι : Type u} (l : ι → A) (hl : ∀ i, l i ∈ 𝒜 1)

/-- The global section `lⱼ / lᵢ` of the chart `Spec (A_{lᵢ})₀` of `Proj 𝒜`. -/
def linearChartSection (i j : ι) : Γ(Spec (.of (Away 𝒜 (l i))), ⊤) :=
  (Scheme.ΓSpecIso _).inv.hom (Away.mk 𝒜 (hl i) 1 (l j) (by simpa using hl j))

@[simp]
lemma linearChartSection_self (i : ι) : linearChartSection 𝒜 l hl i i = 1 := by
  simp [linearChartSection, Away.mk_self]

lemma span_range_linearChartSection (i : ι) :
    Ideal.span (Set.range (linearChartSection 𝒜 l hl i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← linearChartSection_self 𝒜 l hl i]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The linear projection on the chart `D₊(lᵢ) = Spec (A_{lᵢ})₀` of `Proj 𝒜`: the morphism
to `ℙ(ι; Spec k)` sending the homogeneous coordinate `Tⱼ` to `lⱼ / lᵢ`. -/
def linearChartHom (i : ι) : Spec (.of (Away 𝒜 (l i))) ⟶ ℙ(ι; Spec (.of k)) :=
  ProjectiveSpace.homOfSections (awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ toSpecBase 𝒜)
    (linearChartSection 𝒜 l hl i) (span_range_linearChartSection 𝒜 l hl i)

@[reassoc (attr := simp)]
lemma linearChartHom_over (i : ι) :
    linearChartHom 𝒜 l hl i ≫ ℙ(ι; Spec (.of k)) ↘ Spec (.of k) =
      awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ toSpecBase 𝒜 :=
  ProjectiveSpace.homOfSections_over _ _ _

/-- **The chart morphisms of a linear projection agree on overlaps**: on
`D₊(lᵢ) ∩ D₊(lⱼ) = D₊(lᵢ lⱼ)` the sections `lₘ / lᵢ` and `lₘ / lⱼ` differ by the unit
`lᵢ / lⱼ`, so the two chart morphisms coincide. -/
lemma linearChartHom_compatible (i j : ι) :
    pullback.fst (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos) ≫
        linearChartHom 𝒜 l hl i =
      pullback.snd (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos) ≫
        linearChartHom 𝒜 l hl j := by
  have h1 (m : ι) : l m ∈ 𝒜 (1 • 1) := by simpa using hl m
  set p₁ := pullback.fst (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos)
  set p₂ := pullback.snd (awayι 𝒜 (l i) (hl i) Nat.one_pos) (awayι 𝒜 (l j) (hl j) Nat.one_pos)
  have hcond : p₁ ≫ awayι 𝒜 (l i) (hl i) Nat.one_pos = p₂ ≫ awayι 𝒜 (l j) (hl j) Nat.one_pos :=
    pullback.condition
  have hu := isUnit_appTop_awayMk 𝒜 Nat.one_pos (hl i) (hl j) p₁ p₂ hcond (h1 i) (h1 j)
  rw [linearChartHom, linearChartHom, ProjectiveSpace.comp_homOfSections,
    ProjectiveSpace.comp_homOfSections, reassoc_of% hcond]
  refine ProjectiveSpace.homOfSections_eq_of_unit_mul _ hu.unit _ _ fun m ↦ ?_
  rw [IsUnit.unit_spec, mul_comm]
  exact appTop_awayMk_eq_mul 𝒜 Nat.one_pos (hl i) (hl j) p₁ p₂ hcond (h1 i) (l m) (h1 m)

variable (hcov : ⨆ i, basicOpen 𝒜 (l i) = ⊤)

/-- The open cover of `Proj 𝒜` by the charts `Spec (A_{lᵢ})₀ ≅ D₊(lᵢ)`, for a family of
elements `lᵢ` of degree one whose basic opens cover `Proj 𝒜`. -/
def linearCover : (Proj 𝒜).OpenCover :=
  .mkOfCovers ι (fun i ↦ Spec (.of (Away 𝒜 (l i)))) (fun i ↦ awayι 𝒜 (l i) (hl i) Nat.one_pos)
    fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
      rw [← opensRange_awayι 𝒜 _ (hl i) Nat.one_pos] at hi
      exact ⟨i, hi⟩

/-- **The linear projection** `Proj 𝒜 ⟶ ℙ(ι; Spec k)`, `x ↦ [lᵢ(x)]`, defined by a family of
elements `lᵢ` of degree one without common zero on `Proj 𝒜`. It is glued from the chart
morphisms `linearChartHom`. -/
def linearProjection : Proj 𝒜 ⟶ ℙ(ι; Spec (.of k)) :=
  (linearCover 𝒜 l hl hcov).glueMorphisms (linearChartHom 𝒜 l hl)
    (linearChartHom_compatible 𝒜 l hl)

/-- On the chart `D₊(lᵢ) = Spec (A_{lᵢ})₀`, the linear projection is the morphism given by the
sections `lⱼ / lᵢ`. -/
@[reassoc (attr := simp)]
lemma awayι_linearProjection (i : ι) :
    awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ linearProjection 𝒜 l hl hcov = linearChartHom 𝒜 l hl i :=
  (linearCover 𝒜 l hl hcov).ι_glueMorphisms _ _ i

/-- The linear projection is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
lemma linearProjection_over :
    linearProjection 𝒜 l hl hcov ≫ ℙ(ι; Spec (.of k)) ↘ Spec (.of k) = toSpecBase 𝒜 :=
  (linearCover 𝒜 l hl hcov).hom_ext _ _ fun i ↦ by
    rw [← Category.assoc]
    exact (awayι_linearProjection_assoc 𝒜 l hl hcov i _).trans (linearChartHom_over 𝒜 l hl i)

section Finite

open ProjectiveSpace

/-- On the chart `D₊(lⱼ)`, the preimage of the standard open `D₊(Tᵢ)` under the linear
projection is the preimage of `D₊(lᵢ)`, both being the locus where `lᵢ / lⱼ` does not vanish. -/
lemma awayι_preimage_linearProjection_preimage_standardOpen (i j : ι) :
    awayι 𝒜 (l j) (hl j) Nat.one_pos ⁻¹ᵁ
        (linearProjection 𝒜 l hl hcov ⁻¹ᵁ standardOpen ι (Spec (.of k)) i) =
      awayι 𝒜 (l j) (hl j) Nat.one_pos ⁻¹ᵁ basicOpen 𝒜 (l i) := by
  rw [← Scheme.Hom.comp_preimage, awayι_linearProjection, linearChartHom,
    homOfSections_preimage_standardOpen,
    awayι_preimage_basicOpen 𝒜 (hl j) Nat.one_pos (hl i) Nat.one_pos, linearChartSection,
    basicOpen_eq_of_affine]
  congr 2
  exact (pow_one _).symm

/-- The preimage of the standard open `D₊(Tᵢ)` under the linear projection is `D₊(lᵢ)`. -/
lemma linearProjection_preimage_standardOpen (i : ι) :
    linearProjection 𝒜 l hl hcov ⁻¹ᵁ standardOpen ι (Spec (.of k)) i = basicOpen 𝒜 (l i) := by
  ext x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  rw [← opensRange_awayι 𝒜 _ (hl j) Nat.one_pos] at hj
  obtain ⟨y, rfl⟩ := hj
  exact SetLike.ext_iff.mp
    (awayι_preimage_linearProjection_preimage_standardOpen 𝒜 l hl hcov i j) y

/-- On the chart `D₊(lᵢ)`, the structure morphism to `Spec k` is `Spec` of the algebra map. -/
lemma awayι_toSpecBase (i : ι) :
    awayι 𝒜 (l i) (hl i) Nat.one_pos ≫ toSpecBase 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (l i)))) := by
  rw [toSpecBase, awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- Over the standard open `D₊(Tᵢ)`, the linear projection is, up to the chart isomorphisms
`D₊(lᵢ) ≅ Spec A_(lᵢ)` and `D₊(Tᵢ) ≅ 𝔸(ι ∖ {i}; Spec k)`, the morphism given by the coordinates
`lⱼ / lᵢ`. -/
lemma exists_iso_linearProjection_restrict (i : ι) :
    ∃ e : Spec (.of (Away 𝒜 (l i))) ≅
        (linearProjection 𝒜 l hl hcov ⁻¹ᵁ standardOpen ι (Spec (.of k)) i).toScheme,
      e.hom ≫ (linearProjection 𝒜 l hl hcov ∣_ standardOpen ι (Spec (.of k)) i) ≫
        (standardOpenIso ι (Spec (.of k)) i).hom =
      AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (l i)))))
        (fun j ↦ (Scheme.ΓSpecIso (.of (Away 𝒜 (l i)))).inv
          (Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1))) := by
  let κ := IsOpenImmersion.lift
    ((Spec (.of (Away 𝒜 (l i)))).basicOpen (linearChartSection 𝒜 l hl i i)).ι (𝟙 _) (by simp)
  have hκ : κ ≫ (Scheme.basicOpen _ (linearChartSection 𝒜 l hl i i)).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  let e := IsOpenImmersion.isoOfRangeEq (awayι 𝒜 (l i) (hl i) Nat.one_pos)
    (linearProjection 𝒜 l hl hcov ⁻¹ᵁ standardOpen ι (Spec (.of k)) i).ι (by
      rw [linearProjection_preimage_standardOpen, Scheme.Opens.range_ι,
        ← opensRange_awayι 𝒜 _ (hl i) Nat.one_pos]
      rfl)
  have h1 : e.hom ≫ linearProjection 𝒜 l hl hcov ∣_ standardOpen ι (Spec (.of k)) i =
      κ ≫ (linearChartHom 𝒜 l hl i).resLE _ _
        (homOfSections_preimage_standardOpen _ _ _ i).ge := by
    rw [← cancel_mono (standardOpen ι (Spec (.of k)) i).ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, awayι_linearProjection, Category.assoc,
      Scheme.Hom.resLE_comp_ι, reassoc_of% hκ]
  refine ⟨e, ?_⟩
  simp only [linearChartHom] at h1
  rw [reassoc_of% h1, homOfSections_resLE_standardOpenIso_hom,
    AffineSpace.comp_homOfVector, reassoc_of% hκ, awayι_toSpecBase]
  congr 1
  funext j
  have h := congrArg κ.appTop.hom (Scheme.divBasicOpen_mul_self _
    (linearChartSection 𝒜 l hl i j.1) (linearChartSection 𝒜 l hl i i))
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    hκ, Scheme.Hom.id_appTop, CommRingCat.id_apply, CommRingCat.id_apply] at h
  exact (mul_one _).symm.trans
    ((congrArg (_ * ·) (linearChartSection_self 𝒜 l hl i).symm).trans h)

/-- Over the standard open `D₊(Tᵢ)`, the linear projection is finite provided that the
degree-zero part `A_(lᵢ)` of `A[lᵢ⁻¹]` is a finite module over the subalgebra generated by the
quotients `lⱼ / lᵢ`: the restriction is, up to the chart isomorphisms
`D₊(lᵢ) ≅ Spec A_(lᵢ)` and `D₊(Tᵢ) ≅ 𝔸(ι ∖ {i}; Spec k)`, the morphism given by the coordinates
`lⱼ / lᵢ`. -/
lemma isFinite_linearProjection_restrict (i : ι)
    [Module.Finite (Algebra.adjoin k (Set.range fun j : {j // j ≠ i} ↦
      Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1))) (Away 𝒜 (l i))] :
    IsFinite (linearProjection 𝒜 l hl hcov ∣_ standardOpen ι (Spec (.of k)) i) := by
  obtain ⟨e, key⟩ := exists_iso_linearProjection_restrict 𝒜 l hl hcov i
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _
      (standardOpenIso ι (Spec (.of k)) i).hom, Category.assoc, key]
  exact AffineSpace.isFinite_homOfVector_SpecMap _

/-- **The linear projection is finite** as soon as, for every `i`, the degree-zero part
`A_(lᵢ)` of `A[lᵢ⁻¹]` is a finite module over the subalgebra generated by the quotients
`lⱼ / lᵢ`. -/
theorem isFinite_linearProjection
    (hfin : ∀ i, Module.Finite (Algebra.adjoin k (Set.range fun j : {j // j ≠ i} ↦
      Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1))) (Away 𝒜 (l i))) :
    IsFinite (linearProjection 𝒜 l hl hcov) :=
  (IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_standardOpen _ _)).mpr fun i ↦
    isFinite_linearProjection_restrict 𝒜 l hl hcov i

/-- **The linear projection is a closed immersion** as soon as, for every `i`, the degree-zero
part `A_(lᵢ)` of `A[lᵢ⁻¹]` is generated by the quotients `lⱼ / lᵢ`: over the standard open
`D₊(Tᵢ)`, it is then `Spec` of the surjection `k[Tⱼ / Tᵢ] → A_(lᵢ)`. -/
theorem isClosedImmersion_linearProjection
    (hgen : ∀ i, Algebra.adjoin k (Set.range fun j : {j // j ≠ i} ↦
      Away.mk 𝒜 (hl i) 1 (l j.1) (by simpa using hl j.1)) = ⊤) :
    IsClosedImmersion (linearProjection 𝒜 l hl hcov) :=
  (IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_standardOpen _ _)).mpr fun i ↦ by
    obtain ⟨e, key⟩ := exists_iso_linearProjection_restrict 𝒜 l hl hcov i
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom,
      ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
        (standardOpenIso ι (Spec (.of k)) i).hom, Category.assoc, key]
    exact AffineSpace.isClosedImmersion_homOfVector_SpecMap _ (hgen i)

end Finite

end Construction

section Pair

/-- The pair `(l₀, l₁)` as a family indexed by the index type `ULift (Fin 2)` of the
homogeneous coordinates of `ℙ¹`. -/
def linearPair {A : Type u} (l₀ l₁ : A) (i : ULift.{u} (Fin 2)) : A :=
  ![l₀, l₁] i.down

@[simp]
lemma linearPair_zero {A : Type u} (l₀ l₁ : A) : linearPair l₀ l₁ ⟨0⟩ = l₀ := rfl

@[simp]
lemma linearPair_one {A : Type u} (l₀ l₁ : A) : linearPair l₀ l₁ ⟨1⟩ = l₁ := rfl

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜] {l₀ l₁ : A}

omit [GradedAlgebra 𝒜] in
variable {𝒜} in
lemma linearPair_mem (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1) (i : ULift.{u} (Fin 2)) :
    linearPair l₀ l₁ i ∈ 𝒜 1 := by
  obtain ⟨i⟩ := i
  fin_cases i
  exacts [h₀, h₁]

lemma iSup_basicOpen_linearPair
    (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤) :
    ⨆ i, basicOpen 𝒜 (linearPair l₀ l₁ i) = ⊤ :=
  top_le_iff.mp <| hcov.symm.le.trans <|
    sup_le (le_iSup_of_le (⟨0⟩ : ULift.{u} (Fin 2)) le_rfl)
      (le_iSup_of_le (⟨1⟩ : ULift.{u} (Fin 2)) le_rfl)

variable {𝒜} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
  (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤)

/-- **The linear projection** `π_{l₀,l₁}: Proj 𝒜 ⟶ ℙ¹_k`, `x ↦ [l₀(x): l₁(x)]`, attached to
two elements `l₀, l₁` of degree one without common zero on `Proj 𝒜`. On `D₊(l₀)` it is given
by `t ↦ l₁ / l₀` and on `D₊(l₁)` by `t⁻¹ ↦ l₀ / l₁`. -/
def linearPairProjection : Proj 𝒜 ⟶ ProjectiveLine (Spec (.of k)) :=
  linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁)
    (iSup_basicOpen_linearPair 𝒜 hcov)

/-- On the chart `D₊(l₀)`, `π_{l₀,l₁}` is the morphism given by the sections `(1, l₁ / l₀)`. -/
@[reassoc (attr := simp)]
lemma awayι_linearPairProjection_zero :
    awayι 𝒜 l₀ h₀ Nat.one_pos ≫ linearPairProjection h₀ h₁ hcov =
      linearChartHom 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) ⟨0⟩ :=
  awayι_linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) _ ⟨0⟩

/-- On the chart `D₊(l₁)`, `π_{l₀,l₁}` is the morphism given by the sections `(l₀ / l₁, 1)`. -/
@[reassoc (attr := simp)]
lemma awayι_linearPairProjection_one :
    awayι 𝒜 l₁ h₁ Nat.one_pos ≫ linearPairProjection h₀ h₁ hcov =
      linearChartHom 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) ⟨1⟩ :=
  awayι_linearProjection 𝒜 (linearPair l₀ l₁) (linearPair_mem h₀ h₁) _ ⟨1⟩

/-- `π_{l₀,l₁}` is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
lemma linearPairProjection_over :
    linearPairProjection h₀ h₁ hcov ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) =
      toSpecBase 𝒜 :=
  linearProjection_over 𝒜 _ _ _

end Pair

/-- **`π_{l₀,l₁}` is finite** for a standard graded `k`-algebra, i.e. one generated by the
finite-dimensional space `A₁`: over `D₊(T₀)` it is `Spec` of `k[t] → A_(l₀)`, `t ↦ l₁ / l₀`,
which is finite by `GradedAlgebra.IsStandard.finite_away`, and symmetrically over `D₊(T₁)`. -/
theorem isFinite_linearPairProjection {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {𝒜 : ℕ → Submodule k A} [GradedAlgebra 𝒜] [GradedAlgebra.IsStandard 𝒜] {l₀ l₁ : A}
    (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
    (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤) :
    IsFinite (linearPairProjection h₀ h₁ hcov) := by
  refine isFinite_linearProjection 𝒜 _ _ _ fun i ↦ ?_
  match i with
  | ⟨0⟩ =>
    have hS : (Set.range fun j : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦
        Away.mk 𝒜 (linearPair_mem h₀ h₁ ⟨0⟩) 1 (linearPair l₀ l₁ j.1)
          (by simpa using linearPair_mem h₀ h₁ j.1)) = {Away.mk 𝒜 h₀ 1 l₁ h₁} := by
      ext x
      constructor
      · rintro ⟨⟨⟨j⟩, hj⟩, rfl⟩
        fin_cases j
        · exact absurd rfl hj
        · rfl
      · rintro rfl
        exact ⟨⟨⟨1⟩, by decide⟩, rfl⟩
    rw [hS]
    exact GradedAlgebra.IsStandard.finite_away h₀ h₁ hcov
  | ⟨1⟩ =>
    have hS : (Set.range fun j : {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} ↦
        Away.mk 𝒜 (linearPair_mem h₀ h₁ ⟨1⟩) 1 (linearPair l₀ l₁ j.1)
          (by simpa using linearPair_mem h₀ h₁ j.1)) = {Away.mk 𝒜 h₁ 1 l₀ h₀} := by
      ext x
      constructor
      · rintro ⟨⟨⟨j⟩, hj⟩, rfl⟩
        fin_cases j
        · rfl
        · exact absurd rfl hj
      · rintro rfl
        exact ⟨⟨⟨0⟩, by decide⟩, rfl⟩
    rw [hS]
    exact GradedAlgebra.IsStandard.finite_away h₁ h₀ (by rwa [sup_comm])

end Proj

end AlgebraicGeometry
