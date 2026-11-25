/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.Open
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The Segre morphism

The Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ` sends a pair of points with homogeneous
coordinates `(xₖ)ₖ` and `(yₗ)ₗ` to the point with homogeneous coordinates `(xₖ · yₗ)_{k,l}`.
Here `ℙ^σ_ℤ` is the integral model `Proj.projectiveSpaceOverAffine σ (ULift ℤ)` of projective
space, and the product is the fibre product over the terminal scheme, matching the way
`AlgebraicGeometry.ProjectiveSpace` is defined.

There is no formula for the Segre morphism in terms of global sections of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, as
the product has no nonconstant global functions. It is therefore constructed chart by chart:
on the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` the sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` generate the unit ideal,
since the `(i, j)`-th one is `1`, so `AlgebraicGeometry.Proj.fromOfGlobalSections` applies and
gives a morphism to `ℙ^(n×m)_ℤ`. Two such chart morphisms agree on an overlap because their
defining sections differ by the unit `(Xᵢ / Xᵢ') · (Yⱼ / Yⱼ')`, and
`AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_unit_pow_mul` says that rescaling by a unit
does not change the induced morphism. The chart morphisms therefore glue.

The Segre morphism is a closed immersion. Being a closed immersion is Zariski-local on the
target, so this is checked over the standard opens `D₊(W_{k,l})` of `ℙ^(n×m)_ℤ`. The preimage
of `D₊(W_{k,l})` is exactly the chart `D₊(Xₖ) ×_ℤ D₊(Yₗ)`, which is the spectrum of
`ℤ[Xᵣ/Xₖ] ⊗_ℤ ℤ[Yₛ/Yₗ]`; there the Segre morphism is the spectrum of the ring map sending the
affine coordinate `W_{r,s} / W_{k,l}` to `(Xᵣ / Xₖ) ⊗ (Yₛ / Yₗ)`, and this ring map is
surjective because `Xᵣ / Xₖ ⊗ 1` and `1 ⊗ Yₛ / Yₗ` are among its values.

The relative Segre morphism `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(n × m; S)` over an arbitrary base scheme
`S` is obtained from this by base change: `ℙ(n; S)` is *defined* as `S ×_ℤ ℙⁿ_ℤ`, so both sides
are base changes along the structure morphism of `S`, and the relative Segre morphism is a
closed immersion because closed immersions are stable under base change.

## Main definitions

- `AlgebraicGeometry.Proj.segre` — the Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ`.
- `AlgebraicGeometry.Proj.segreCover` — the standard open cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the
  products `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of standard charts.
- `AlgebraicGeometry.Proj.segreChartHom` — the Segre morphism on the `(i, j)`-chart.
- `AlgebraicGeometry.ProjectiveSpace.segre` — the relative Segre morphism
  `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(n × m; S)` over a base scheme `S`.
- `AlgebraicGeometry.ProjectiveSpace.prodToProjInt` — the morphism
  `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` along which the relative Segre morphism is the base
  change of the integral one.

## Main results

- `AlgebraicGeometry.Proj.isClosedImmersion_segre` — the Segre morphism is a closed immersion.
- `AlgebraicGeometry.Proj.segre_preimage_basicOpen` — the preimage under the Segre morphism of
  the locus `D₊(W_{k,l})` is the product of the loci `D₊(Xₖ)` and `D₊(Yₗ)`.
- `AlgebraicGeometry.Proj.segreCover_f_comp_segre` — on the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`, the
  Segre morphism is `segreChartHom i j`.
- `AlgebraicGeometry.Proj.segre_appLE_awayToSection_awayXRatio` — the Segre morphism pulls the
  transition function `W_{k,l} / W_{k',l'}` back to `(Xₖ / Xₖ') · (Yₗ / Yₗ')`.
- `AlgebraicGeometry.ProjectiveSpace.isPullback_segre` — the relative Segre morphism is the
  base change of the Segre morphism of the integral models.
- `AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_segre` — the relative Segre morphism is
  a closed immersion.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

section Cover

variable (σ A : Type u) [CommRing A]

/-- The standard affine open cover of `ℙ^σ_A` by the charts `D₊(Xᵢ) ≅ Spec (A[X]_{Xᵢ})₀`. -/
def projectiveSpaceOverAffineAffineOpenCover :
    (projectiveSpaceOverAffine σ A).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun i : σ ↦ MvPolynomial.X i)
    (fun i ↦ X_mem_homogeneousSubmodule_one A i) (fun _ ↦ Nat.one_pos)
    (toIdeal_irrelevant_homogeneousSubmodule σ A).le

@[simp]
lemma projectiveSpaceOverAffineAffineOpenCover_X (i : σ) :
    (projectiveSpaceOverAffineAffineOpenCover σ A).X i =
      CommRingCat.of (Away (homogeneousSubmodule σ A) (MvPolynomial.X i)) := rfl

@[simp]
lemma projectiveSpaceOverAffineAffineOpenCover_f (i : σ) :
    (projectiveSpaceOverAffineAffineOpenCover σ A).f i =
      awayι _ (MvPolynomial.X i) (X_mem_homogeneousSubmodule_one A i) Nat.one_pos := rfl

end Cover

variable (n m : Type u)

/-- The open cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the products `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of standard charts
of the two factors. -/
def segreCover :
    (pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
      (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projectiveSpaceOverAffineAffineOpenCover n (ULift.{u} ℤ)).openCover
    (projectiveSpaceOverAffineAffineOpenCover m (ULift.{u} ℤ)).openCover _ _

variable {n m}

/-- The projection of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `i`-th standard chart of
the first factor. -/
def segreCoverFst (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶
      Spec (.of <| Away (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i)) :=
  pullback.fst _ _

/-- The projection of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `j`-th standard chart of
the second factor. -/
def segreCoverSnd (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶
      Spec (.of <| Away (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X j)) :=
  pullback.snd _ _

@[reassoc]
lemma segreCoverFst_awayι (i : n) (j : m) :
    segreCoverFst i j ≫ awayι _ (MvPolynomial.X i)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos =
      (segreCover n m).f (i, j) ≫ pullback.fst _ _ := by
  simp [segreCover, segreCoverFst]

@[reassoc]
lemma segreCoverSnd_awayι (i : n) (j : m) :
    segreCoverSnd i j ≫ awayι _ (MvPolynomial.X j)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j) Nat.one_pos =
      (segreCover n m).f (i, j) ≫ pullback.snd _ _ := by
  simp [segreCover, segreCoverSnd]

/-- The section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. It is the
image of the homogeneous coordinate `W_{k,l}` of `ℙ^(n×m)_ℤ` under the Segre morphism. -/
def segreChartSection (i : n) (j : m) (kl : n × m) : Γ((segreCover n m).X (i, j), ⊤) :=
  ((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst i j).appTop).hom
      (awayXRatio (ULift.{u} ℤ) i kl.1) *
    ((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd i j).appTop).hom
      (awayXRatio (ULift.{u} ℤ) j kl.2)

@[simp]
lemma segreChartSection_self (i : n) (j : m) : segreChartSection i j (i, j) = 1 := by
  simp [segreChartSection]

lemma span_range_segreChartSection_eq_top (i : n) (j : m) :
    Ideal.span (Set.range (segreChartSection i j)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← segreChartSection_self i j]
  exact Ideal.subset_span ⟨(i, j), rfl⟩

/-- The Segre morphism on the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the morphism to
`ℙ^(n×m)_ℤ` sending the homogeneous coordinate `W_{k,l}` to `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
def segreChartHom (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶ projectiveSpaceOverAffine (n × m) (ULift.{u} ℤ) :=
  fromOfGlobalSections _ (ProjectiveSpace.evalSections (segreChartSection i j))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top i j))

section Compatibility

variable (i i' : n) (j j' : m)

/-- The chart morphisms `segreChartHom` agree on the overlap of two charts of the standard
cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the two chart morphisms differ by rescaling the homogeneous
coordinates of `ℙ^(n×m)_ℤ` by the unit `(Xᵢ / Xᵢ') · (Yⱼ / Yⱼ')`. -/
lemma segreChartHom_compatible :
    pullback.fst ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫ segreChartHom i j =
      pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫
        segreChartHom i' j' := by
  have hXi : ∀ k : n, (MvPolynomial.X k : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXj : ∀ l : m, (MvPolynomial.X l : MvPolynomial m (ULift.{u} ℤ)) ∈
      homogeneousSubmodule m (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXi1 : ∀ k : n, (MvPolynomial.X k : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) (1 • 1) := fun k ↦ by simpa using hXi k
  have hXj1 : ∀ l : m, (MvPolynomial.X l : MvPolynomial m (ULift.{u} ℤ)) ∈
      homogeneousSubmodule m (ULift.{u} ℤ) (1 • 1) := fun l ↦ by simpa using hXj l
  set p₁ := pullback.fst ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j'))
  set p₂ := pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j'))
  have hcond : p₁ ≫ (segreCover n m).f (i, j) = p₂ ≫ (segreCover n m).f (i', j') :=
    pullback.condition
  have ha : (p₁ ≫ segreCoverFst i j) ≫ awayι _ (MvPolynomial.X i) (hXi i) Nat.one_pos =
      (p₂ ≫ segreCoverFst i' j') ≫ awayι _ (MvPolynomial.X i') (hXi i') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverFst_awayι, segreCoverFst_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hb : (p₁ ≫ segreCoverSnd i j) ≫ awayι _ (MvPolynomial.X j) (hXj j) Nat.one_pos =
      (p₂ ≫ segreCoverSnd i' j') ≫ awayι _ (MvPolynomial.X j') (hXj j') Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverSnd_awayι, segreCoverSnd_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hA : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
      (awayXRatio (ULift.{u} ℤ) i' i)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXi i) (hXi i') _ _ ha (hXi1 i) (hXi1 i')
  have hB : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
      (awayXRatio (ULift.{u} ℤ) j' j)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXj j) (hXj j') _ _ hb (hXj1 j) (hXj1 j')
  have hpull : ∀ {R : CommRingCat.{u}} {W V : Scheme.{u}} (c : V ⟶ W) (q : W ⟶ Spec R) (z : R),
      c.appTop.hom (((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom z) =
        ((Scheme.ΓSpecIso R).inv ≫ (c ≫ q).appTop).hom z := fun _ _ _ ↦ rfl
  have hvar : ∀ kl : n × m, p₂.appTop.hom (segreChartSection i' j' kl) =
      ((hA.unit * hB.unit : Γ(_, ⊤)ˣ) : Γ(_, ⊤)) *
        p₁.appTop.hom (segreChartSection i j kl) := by
    intro kl
    have h1 : ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
        (awayXRatio (ULift.{u} ℤ) i' kl.1) =
        ((Scheme.ΓSpecIso _).inv ≫ (p₁ ≫ segreCoverFst i j).appTop).hom
            (awayXRatio (ULift.{u} ℤ) i kl.1) *
          ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverFst i' j').appTop).hom
            (awayXRatio (ULift.{u} ℤ) i' i) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXi i) (hXi i') _ _ ha (hXi1 i)
        (MvPolynomial.X kl.1) (hXi1 kl.1)
    have h2 : ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
        (awayXRatio (ULift.{u} ℤ) j' kl.2) =
        ((Scheme.ΓSpecIso _).inv ≫ (p₁ ≫ segreCoverSnd i j).appTop).hom
            (awayXRatio (ULift.{u} ℤ) j kl.2) *
          ((Scheme.ΓSpecIso _).inv ≫ (p₂ ≫ segreCoverSnd i' j').appTop).hom
            (awayXRatio (ULift.{u} ℤ) j' j) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXj j) (hXj j') _ _ hb (hXj1 j)
        (MvPolynomial.X kl.2) (hXj1 kl.2)
    simp only [segreChartSection, map_mul, hpull, h1, h2, Units.val_mul, IsUnit.unit_spec]
    ring
  simp only [segreChartHom]
  rw [comp_fromOfGlobalSections _ p₁ _ _ (map_irrelevant_comp_appTop_eq_top _ p₁ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top i j))),
    comp_fromOfGlobalSections _ p₂ _ _ (map_irrelevant_comp_appTop_eq_top _ p₂ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top i' j')))]
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ (hA.unit * hB.unit) _ _ (fun d a hda ↦ ?_) _ _
  rw [ProjectiveSpace.comp_evalSections, ProjectiveSpace.comp_evalSections]
  simp only [hvar]
  exact ProjectiveSpace.evalSections_const_mul _ _ hda

end Compatibility

variable (n m)

/-- **The Segre morphism** `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ` between the integral models of
projective spaces, sending a pair of points with homogeneous coordinates `(xₖ)` and `(yₗ)` to
the point with homogeneous coordinates `(xₖ · yₗ)`.

It is glued from the morphisms `segreChartHom i j` on the standard cover of the product by the
charts `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`. -/
def segre :
    pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
        (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⟶
      projectiveSpaceOverAffine (n × m) (ULift.{u} ℤ) :=
  (segreCover n m).glueMorphisms (fun ij ↦ segreChartHom ij.1 ij.2)
    fun ij ij' ↦ segreChartHom_compatible ij.1 ij'.1 ij.2 ij'.2

variable {n m}

/-- On the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the Segre morphism is the morphism
`segreChartHom i j` given by the sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
@[reassoc]
lemma segreCover_f_comp_segre (i : n) (j : m) :
    (segreCover n m).f (i, j) ≫ segre n m = segreChartHom i j :=
  (segreCover n m).ι_glueMorphisms _ _ (i, j)

section ClosedImmersion

/-- The `(i, j)`-chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` is the fibre product of the two
affine charts over the terminal scheme. -/
lemma isPullback_segreCoverFst_segreCoverSnd (i : n) (j : m) :
    IsPullback (segreCoverFst i j) (segreCoverSnd i j)
      (terminal.from (Spec (.of <| Away (homogeneousSubmodule n (ULift.{u} ℤ))
        (MvPolynomial.X i))))
      (terminal.from (Spec (.of <| Away (homogeneousSubmodule m (ULift.{u} ℤ))
        (MvPolynomial.X j)))) := by
  have h1 : awayι _ (MvPolynomial.X i) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
      Nat.one_pos ≫ terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)) =
      terminal.from _ := terminal.hom_ext _ _
  have h2 : awayι _ (MvPolynomial.X j) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)
      Nat.one_pos ≫ terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)) =
      terminal.from _ := terminal.hom_ext _ _
  rw [← h1, ← h2]
  exact IsPullback.of_hasPullback _ _

instance isAffine_segreCover_X (i : n) (j : m) : IsAffine ((segreCover n m).X (i, j)) :=
  IsAffine.of_isIso (isPullback_segreCoverFst_segreCoverSnd i j).isoPullback.hom

/-- **The chart sections generate the sections of the chart**: the global sections of
`D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` are generated as a ring by the products `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma closure_range_segreChartSection_eq_top (i : n) (j : m) :
    Subring.closure (Set.range (segreChartSection i j)) = ⊤ := by
  have hR : Function.Surjective ((↑) : ℤ → ULift.{u} ℤ) := fun r ↦ ⟨r.down, by ext; simp⟩
  exact closure_range_mul_appTop_eq_top (isPullback_segreCoverFst_segreCoverSnd i j)
    (MvPolynomial.closure_range_awayXRatio_eq_top _ hR i)
    (MvPolynomial.closure_range_awayXRatio_eq_top _ hR j)
    (awayXRatio_self (ULift.{u} ℤ) i) (awayXRatio_self (ULift.{u} ℤ) j)

/-- The `(i, j)`-chart of the standard cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` is the locus where the `i`-th
homogeneous coordinate of the first factor and the `j`-th homogeneous coordinate of the second
factor do not vanish. -/
lemma opensRange_segreCover_f (i : n) (j : m) :
    ((segreCover n m).f (i, j)).opensRange =
      pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i) ⊓
      pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X j) := by
  have h1 : ((projectiveSpaceOverAffineAffineOpenCover n (ULift.{u} ℤ)).openCover.f i).opensRange =
      basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i) :=
    opensRange_awayι _ _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos
  have h2 : ((projectiveSpaceOverAffineAffineOpenCover m (ULift.{u} ℤ)).openCover.f j).opensRange =
      basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X j) :=
    opensRange_awayι _ _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j) Nat.one_pos
  rw [← h1, ← h2]
  exact Scheme.Pullback.opensRange_openCoverOfLeftRight_f
    (projectiveSpaceOverAffineAffineOpenCover n (ULift.{u} ℤ)).openCover
    (projectiveSpaceOverAffineAffineOpenCover m (ULift.{u} ℤ)).openCover
    (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
    (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) (i, j)

set_option backward.isDefEq.respectTransparency.types false in
/-- Inside the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the locus where the `k`-th and `l`-th
homogeneous coordinates of the two factors do not vanish is the basic open of the chart
section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma segreCover_f_preimage_inf (i : n) (j : m) (k : n) (l : m) :
    (segreCover n m).f (i, j) ⁻¹ᵁ
        (pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k) ⊓
        pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l)) =
      ((segreCover n m).X (i, j)).basicOpen (segreChartSection i j (k, l)) := by
  have e1 : (segreCover n m).f (i, j) ⁻¹ᵁ
      (pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k)) =
      ((segreCover n m).X (i, j)).basicOpen
        (((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst i j).appTop).hom
          (awayXRatio (ULift.{u} ℤ) i k)) := by
    rw [← Scheme.Hom.comp_preimage, ← segreCoverFst_awayι, Scheme.Hom.comp_preimage,
      awayι_preimage_basicOpen _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) k) Nat.one_pos,
      isLocalizationElem_X]
    refine Eq.trans (congrArg (segreCoverFst i j ⁻¹ᵁ ·) (basicOpen_eq_of_affine
      (R := CommRingCat.of (Away (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i)))
      (awayXRatio (ULift.{u} ℤ) i k)).symm) ?_
    exact Scheme.preimage_basicOpen _ _
  have e2 : (segreCover n m).f (i, j) ⁻¹ᵁ
      (pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l)) =
      ((segreCover n m).X (i, j)).basicOpen
        (((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd i j).appTop).hom
          (awayXRatio (ULift.{u} ℤ) j l)) := by
    rw [← Scheme.Hom.comp_preimage, ← segreCoverSnd_awayι, Scheme.Hom.comp_preimage,
      awayι_preimage_basicOpen _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j) Nat.one_pos
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) l) Nat.one_pos,
      isLocalizationElem_X]
    refine Eq.trans (congrArg (segreCoverSnd i j ⁻¹ᵁ ·) (basicOpen_eq_of_affine
      (R := CommRingCat.of (Away (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X j)))
      (awayXRatio (ULift.{u} ℤ) j l)).symm) ?_
    exact Scheme.preimage_basicOpen _ _
  have hs : segreChartSection i j (k, l) =
      ((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst i j).appTop).hom
          (awayXRatio (ULift.{u} ℤ) i k) *
        ((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd i j).appTop).hom
          (awayXRatio (ULift.{u} ℤ) j l) := rfl
  rw [hs, Scheme.basicOpen_mul, ← e1, ← e2]
  rfl

/-- Inside the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the preimage under the Segre morphism of the
locus where the homogeneous coordinate `W_{k,l}` does not vanish is the basic open of the chart
section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma segreCover_f_preimage_segre_preimage (i : n) (j : m) (k : n) (l : m) :
    (segreCover n m).f (i, j) ⁻¹ᵁ (segre n m ⁻¹ᵁ
        basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ)) (MvPolynomial.X (k, l))) =
      ((segreCover n m).X (i, j)).basicOpen (segreChartSection i j (k, l)) := by
  rw [← Scheme.Hom.comp_preimage, segreCover_f_comp_segre, segreChartHom,
    fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (k, l)),
    ProjectiveSpace.evalSections_X]

/-- **The preimage of a standard open under the Segre morphism.** The locus in
`ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` where the homogeneous coordinate `W_{k,l}` of `ℙ^(n×m)_ℤ` does not vanish is
the product of the loci where `Xₖ` and `Yₗ` do not vanish. -/
theorem segre_preimage_basicOpen (k : n) (l : m) :
    segre n m ⁻¹ᵁ basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
        (MvPolynomial.X (k, l)) =
      pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X k) ⊓
      pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X l) := by
  refine Scheme.Opens.ext_of_openCover (segreCover n m) fun ij ↦ ?_
  obtain ⟨i, j⟩ := ij
  rw [segreCover_f_preimage_segre_preimage, segreCover_f_preimage_inf]

/-- The preimage under the Segre morphism of the locus where `W_{k,l}` does not vanish is the
`(k, l)`-chart of the standard cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. -/
lemma opensRange_segreCover_f_eq_preimage (k : n) (l : m) :
    ((segreCover n m).f (k, l)).opensRange =
      segre n m ⁻¹ᵁ basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
        (MvPolynomial.X (k, l)) := by
  rw [segre_preimage_basicOpen, opensRange_segreCover_f]

/-- **The Segre morphism is a closed immersion.** -/
instance isClosedImmersion_segre : IsClosedImmersion (segre n m) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun kl : n × m ↦ basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
      (MvPolynomial.X kl))
    (iSup_basicOpen_eq_top _ _
      (toIdeal_irrelevant_homogeneousSubmodule (n × m) (ULift.{u} ℤ)).le) ?_
  rintro ⟨k, l⟩
  have hgen : Subring.closure {y : Γ((segreCover n m).X (k, l), ⊤) | ∃ e : ℕ,
      ∃ a ∈ homogeneousSubmodule (n × m) (ULift.{u} ℤ) (e • 1),
        ProjectiveSpace.evalSections (segreChartSection k l) a = y} = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← closure_range_segreChartSection_eq_top k l]
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨rs, rfl⟩
    exact Subring.subset_closure ⟨1, MvPolynomial.X rs,
      by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) rs,
      ProjectiveSpace.evalSections_X _ _⟩
  obtain ⟨q, hq, hqw⟩ := exists_isClosedImmersion_of_fromOfGlobalSections
    (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
    (ProjectiveSpace.evalSections (segreChartSection k l))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top k l))
    Nat.one_pos (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (k, l))
    (by rw [ProjectiveSpace.evalSections_X, segreChartSection_self]) hgen
  have e : Arrow.mk (segre n m ∣_ (awayι (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
      (MvPolynomial.X (k, l)) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (k, l))
      Nat.one_pos).opensRange) ≅ Arrow.mk q :=
    morphismRestrictArrowIso (segre n m) q
      ((segreCover_f_comp_segre k l).trans hqw.symm)
      (by rw [opensRange_awayι, ← opensRange_segreCover_f_eq_preimage])
  have H : IsClosedImmersion (segre n m ∣_ (awayι (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
      (MvPolynomial.X (k, l)) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (k, l))
      Nat.one_pos).opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).mpr hq
  rwa [opensRange_awayι] at H

end ClosedImmersion

set_option backward.isDefEq.respectTransparency.types false in
/-- **The Segre morphism on the transition functions.** On the chart `D₊(Xₖ') ×_ℤ D₊(Yₗ')`, the
Segre morphism pulls the function `W_{k,l} / W_{k',l'}` back to `(Xₖ / Xₖ') · (Yₗ / Yₗ')`. -/
lemma segre_appLE_awayToSection_awayXRatio (k k' : n) (l l' : m) :
    (segre n m).appLE (basicOpen _ (X (k', l')))
        (pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X k') ⊓
        pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (X l'))
        (segre_preimage_basicOpen k' l').ge
        (awayToSection _ _ (awayXRatio (ULift.{u} ℤ) (k', l') (k, l))) =
      (pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).appLE
          (basicOpen _ (X k')) _ inf_le_left
          (awayToSection _ _ (awayXRatio (ULift.{u} ℤ) k' k)) *
        (pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).appLE
          (basicOpen _ (X l')) _ inf_le_right
          (awayToSection _ _ (awayXRatio (ULift.{u} ℤ) l' l)) := by
  set c := (segreCover n m).f (k', l')
  have hc : c ''ᵁ ⊤ = pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X k') ⊓
        pullback.snd (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule m (ULift.{u} ℤ)) (X l') := by
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_segreCover_f]
  have hle : ⊤ ≤ c ⁻¹ᵁ (c ''ᵁ ⊤) := (Scheme.Hom.preimage_image_eq c ⊤).ge
  have hcongr : ∀ {Y : Scheme.{u}} {f g : (segreCover n m).X (k', l') ⟶ Y} (h : f = g) (U) (e),
      f.appLE U ⊤ e = g.appLE U ⊤ (h ▸ e) := by
    rintro Y f g rfl U e
    rfl
  have hinj : Function.Injective (c.appLE _ ⊤ (hc ▸ hle)) := by
    have e : c.appLE _ ⊤ (hc ▸ hle) =
        ((pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).presheaf.map
            (eqToHom hc).op) ≫ c.appLE (c ''ᵁ ⊤) ⊤ hle := by
      rw [Scheme.Hom.map_appLE]
    have e' : c.appLE (c ''ᵁ ⊤) ⊤ hle = (c.appIso ⊤).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [e, e']
    exact (ConcreteCategory.bijective_of_isIso (c.appIso ⊤).hom).1.comp
      (ConcreteCategory.bijective_of_isIso
        ((pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))).presheaf.map
            (eqToHom hc).op)).1
  obtain ⟨q, hq, hqv⟩ := exists_comp_awayι_eq_fromOfGlobalSections
    (homogeneousSubmodule (n × m) (ULift.{u} ℤ))
    (ProjectiveSpace.evalSections (segreChartSection k' l'))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top k' l'))
    Nat.one_pos (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (k', l'))
    (by rw [ProjectiveSpace.evalSections_X, segreChartSection_self])
  apply hinj
  rw [map_mul, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE, hcongr ((segreCover_f_comp_segre k' l').trans hq.symm),
    hcongr (segreCoverFst_awayι k' l').symm, hcongr (segreCoverSnd_awayι k' l').symm,
]
  erw [comp_awayι_appLE_awayToSection, comp_awayι_appLE_awayToSection,
    comp_awayι_appLE_awayToSection]
  rw [awayXRatio, hqv, ProjectiveSpace.evalSections_X]
  rfl

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

variable (n m : Type u) (S : Scheme.{u})

/-- The morphism `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the product of the integral models,
induced by the two maps `ProjectiveSpace.toProjInt` to the integral models. -/
def prodToProjInt :
    pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⟶
      pullback (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))
        (terminal.from (Proj.projectiveSpaceOverAffine m (ULift.{u} ℤ))) :=
  pullback.lift (pullback.fst _ _ ≫ toProjInt n S) (pullback.snd _ _ ≫ toProjInt m S)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma prodToProjInt_fst :
    prodToProjInt n m S ≫ pullback.fst _ _ = pullback.fst _ _ ≫ toProjInt n S :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma prodToProjInt_snd :
    prodToProjInt n m S ≫ pullback.snd _ _ = pullback.snd _ _ ≫ toProjInt m S :=
  pullback.lift_snd _ _ _

/-- `ℙ(n; S) ×_S ℙ(m; S)` is the base change of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` along the structure morphism
of `S`. -/
lemma isPullback_prodToProjInt :
    IsPullback (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ≫ (ℙ(n; S) ↘ S))
      (prodToProjInt n m S) (terminal.from S)
      (terminal.from (pullback
        (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))
        (terminal.from (Proj.projectiveSpaceOverAffine m (ULift.{u} ℤ))))) := by
  have h := IsPullback.baseChange_pullback' (isPullback_over_toProjInt n S)
    (isPullback_over_toProjInt m S)
    (IsPullback.of_hasPullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S))
    (IsPullback.of_hasPullback _ _) (prodToProjInt_fst n m S) (prodToProjInt_snd n m S)
  rwa [terminal.hom_ext (pullback.fst
    (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))
    (terminal.from (Proj.projectiveSpaceOverAffine m (ULift.{u} ℤ))) ≫ terminal.from _)
    (terminal.from _)] at h

/-- **The relative Segre morphism** `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(n × m; S)`, obtained from the
Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(n×m)_ℤ` of the integral models by base change along the
structure morphism of `S`. -/
def segre : pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⟶ ℙ(n × m; S) :=
  pullback.lift (pullback.fst _ _ ≫ (ℙ(n; S) ↘ S))
    (prodToProjInt n m S ≫ Proj.segre n m) (terminal.hom_ext _ _)

/-- The relative Segre morphism is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma segre_over :
    segre n m S ≫ (ℙ(n × m; S) ↘ S) = pullback.fst _ _ ≫ (ℙ(n; S) ↘ S) :=
  pullback.lift_fst _ _ _

/-- The relative Segre morphism is compatible with the Segre morphism of the integral models. -/
@[reassoc (attr := simp)]
lemma segre_toProjInt :
    segre n m S ≫ toProjInt (n × m) S = prodToProjInt n m S ≫ Proj.segre n m :=
  pullback.lift_snd _ _ _

/-- **The relative Segre morphism is the base change of the Segre morphism of the integral
models** along the map `ℙ(n × m; S) ⟶ ℙ^(n×m)_ℤ`. -/
lemma isPullback_segre :
    IsPullback (prodToProjInt n m S) (segre n m S) (Proj.segre n m) (toProjInt (n × m) S) := by
  refine IsPullback.of_bot ?_ (segre_toProjInt n m S).symm
    (isPullback_over_toProjInt (n × m) S).flip
  rw [segre_over, terminal.hom_ext (Proj.segre n m ≫
    terminal.from (Proj.projectiveSpaceOverAffine (n × m) (ULift.{u} ℤ))) (terminal.from _)]
  exact (isPullback_prodToProjInt n m S).flip

/-- **The relative Segre morphism is a closed immersion**, being the base change of the Segre
morphism of the integral models. -/
instance isClosedImmersion_segre : IsClosedImmersion (segre n m S) :=
  MorphismProperty.of_isPullback (isPullback_segre n m S) inferInstance

/-- For finite index types, the projection `ℙ(n; S) ×_S ℙ(m; S) ⟶ S` is proper: it factors as
the relative Segre closed immersion followed by the proper structure morphism of
`ℙ(n × m; S)`. -/
instance isProper_pullback_fst_comp_over [Finite n] [Finite m] :
    IsProper (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ≫ (ℙ(n; S) ↘ S)) := by
  have : IsProper (segre n m S ≫ (ℙ(n × m; S) ↘ S)) := inferInstance
  rwa [segre_over] at this

end AlgebraicGeometry.ProjectiveSpace
