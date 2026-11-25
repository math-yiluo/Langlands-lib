/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre

/-!
# Bilinear morphisms of projective spaces

Let `ℓ : ι → ℤ[W_{k,l}]` be a family of linear forms in the homogeneous coordinates `W_{k,l}` of
the Segre target `ℙ^(n×m)_ℤ`. Pulled back along the Segre morphism, they become bihomogeneous
forms of bidegree `(1, 1)` on `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. If on every chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` the
dehomogenised forms generate the unit ideal ("the forms have no common zero"), they define a
morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^ι_ℤ`, glued from the chart morphisms exactly as the Segre morphism.

Such a *bilinear morphism* is finite whenever `n` and `m` are finite: it is proper, and it is
affine because the preimage of the standard open `D₊(T_c)` is the preimage of the affine open
`D₊(ℓ c)` under the Segre closed immersion. Finally we compute the composite of a bilinear
morphism with a pair of morphisms given by global sections, and we show that every morphism into
a standard chart is given by global sections; this gives a criterion for surjectivity in terms of
points with values in algebraically closed fields.

## Main definitions

- `AlgebraicGeometry.Proj.bilinear` — the bilinear morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^ι_ℤ`.
- `AlgebraicGeometry.ProjectiveSpace.bilinear` — its base change
  `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(ι; S)` to an arbitrary base scheme.

## Main results

- `AlgebraicGeometry.Proj.bilinear_preimage_basicOpen` — the preimage of `D₊(T_c)` is the
  preimage of `D₊(ℓ c)` under the Segre morphism.
- `AlgebraicGeometry.Proj.isFinite_bilinear` — bilinear morphisms are finite.
- `AlgebraicGeometry.Proj.surjective_bilinear` — the surjectivity criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n m ι : Type u}

/-- Rescaling a family of generating global sections by a unit does not change the induced
morphism to the integral model of projective space. -/
lemma fromOfGlobalSections_evalSections_eq_of_unit_mul {X : Scheme.{u}} {σ : Type u}
    (u : Γ(X, ⊤)ˣ) {s s' : σ → Γ(X, ⊤)} (h : ∀ k, s' k = u * s k)
    (hs : (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ (ULift.{u} ℤ))).toIdeal.map
      (ProjectiveSpace.evalSections s) = ⊤)
    (hs' : (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ (ULift.{u} ℤ))).toIdeal.map
      (ProjectiveSpace.evalSections s') = ⊤) :
    fromOfGlobalSections _ (ProjectiveSpace.evalSections s) hs =
      fromOfGlobalSections _ (ProjectiveSpace.evalSections s') hs' := by
  obtain rfl : s' = fun k ↦ (u : Γ(X, ⊤)) * s k := funext h
  exact fromOfGlobalSections_eq_of_unit_pow_mul _ u _ _
    (fun _ _ hda ↦ ProjectiveSpace.evalSections_const_mul _ _ hda) _ _

/-- **The transition functions of the Segre chart sections.** On the overlap of the charts
`(i, j)` and `(i', j')` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the chart sections `(Xₖ / Xᵢ') · (Yₗ / Yⱼ')` are the
chart sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` times a common unit. -/
lemma exists_unit_segreChartSection_transition (i i' : n) (j j' : m) :
    ∃ u : Γ(pullback ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')), ⊤)ˣ,
      ∀ kl : n × m,
        (pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j'))).appTop.hom
            (segreChartSection i' j' kl) =
          u * (pullback.fst ((segreCover n m).f (i, j))
            ((segreCover n m).f (i', j'))).appTop.hom (segreChartSection i j kl) := by
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
  refine ⟨hA.unit * hB.unit, fun kl ↦ ?_⟩
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

section Bilinear

variable (ℓ : ι → MvPolynomial (n × m) (ULift.{u} ℤ))

/-- The section `ℓ_c((Xₖ / Xᵢ) · (Yₗ / Yⱼ))` of the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the
linear form `ℓ c` evaluated at the Segre chart sections. -/
def bilinearChartSection (i : n) (j : m) (c : ι) : Γ((segreCover n m).X (i, j), ⊤) :=
  ProjectiveSpace.evalSections (segreChartSection i j) (ℓ c)

variable (hℓ : ∀ c, ℓ c ∈ homogeneousSubmodule (n × m) (ULift.{u} ℤ) 1)
  (hspan : ∀ i j, Ideal.span (Set.range (bilinearChartSection ℓ i j)) = ⊤)

/-- The bilinear morphism on the `(i, j)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the morphism to `ℙ^ι_ℤ`
sending the homogeneous coordinate `T_c` to the chart section `bilinearChartSection ℓ i j c`. -/
def bilinearChartHom (i : n) (j : m) :
    (segreCover n m).X (i, j) ⟶ projectiveSpaceOverAffine ι (ULift.{u} ℤ) :=
  fromOfGlobalSections _ (ProjectiveSpace.evalSections (bilinearChartSection ℓ i j))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i j))

include hℓ in
/-- Two chart morphisms `bilinearChartHom` agree after precomposition with `p₁` and `p₂` if the
pulled back Segre chart sections differ by a unit. -/
lemma comp_bilinearChartHom_eq_of_unit_mul {V : Scheme.{u}} {i i' : n} {j j' : m}
    (p₁ : V ⟶ (segreCover n m).X (i, j)) (p₂ : V ⟶ (segreCover n m).X (i', j'))
    (u : Γ(V, ⊤)ˣ)
    (hu : ∀ kl : n × m, p₂.appTop.hom (segreChartSection i' j' kl) =
      u * p₁.appTop.hom (segreChartSection i j kl)) :
    p₁ ≫ bilinearChartHom ℓ hspan i j = p₂ ≫ bilinearChartHom ℓ hspan i' j' := by
  have hvar (c : ι) : p₂.appTop.hom (bilinearChartSection ℓ i' j' c) =
      (u : Γ(V, ⊤)) * p₁.appTop.hom (bilinearChartSection ℓ i j c) := by
    rw [bilinearChartSection, bilinearChartSection, ← RingHom.comp_apply,
      ProjectiveSpace.comp_evalSections, ← RingHom.comp_apply, ProjectiveSpace.comp_evalSections]
    simp only [hu]
    rw [ProjectiveSpace.evalSections_const_mul _ _ (hℓ c), pow_one]
  have e₁ := comp_fromOfGlobalSections (homogeneousSubmodule ι (ULift.{u} ℤ)) p₁
    (ProjectiveSpace.evalSections (bilinearChartSection ℓ i j))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i j))
    (map_irrelevant_comp_appTop_eq_top _ p₁ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i j)))
  have e₂ := comp_fromOfGlobalSections (homogeneousSubmodule ι (ULift.{u} ℤ)) p₂
    (ProjectiveSpace.evalSections (bilinearChartSection ℓ i' j'))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i' j'))
    (map_irrelevant_comp_appTop_eq_top _ p₂ _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i' j')))
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ u _ _ (fun d a hda ↦ ?_) _ _
  rw [ProjectiveSpace.comp_evalSections, ProjectiveSpace.comp_evalSections]
  simp only [hvar]
  exact ProjectiveSpace.evalSections_const_mul _ _ hda

include hℓ in
/-- The chart morphisms `bilinearChartHom` agree on the overlaps of the charts: their defining
sections differ by the unit by which the Segre chart sections differ. -/
lemma bilinearChartHom_compatible (i i' : n) (j j' : m) :
    pullback.fst ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫
        bilinearChartHom ℓ hspan i j =
      pullback.snd ((segreCover n m).f (i, j)) ((segreCover n m).f (i', j')) ≫
        bilinearChartHom ℓ hspan i' j' := by
  obtain ⟨u, hu⟩ := exists_unit_segreChartSection_transition i i' j j'
  exact comp_bilinearChartHom_eq_of_unit_mul ℓ hℓ hspan _ _ u hu

variable (n m) in
/-- **The bilinear morphism** `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^ι_ℤ` attached to a family `ℓ` of linear forms
in the Segre coordinates without common zero on `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: it sends a pair of points with
homogeneous coordinates `(xₖ)` and `(yₗ)` to the point with homogeneous coordinates
`(ℓ_c(xₖ yₗ))_c`. It is glued from the chart morphisms `bilinearChartHom`. -/
def bilinear :
    pullback (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
        (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ))) ⟶
      projectiveSpaceOverAffine ι (ULift.{u} ℤ) :=
  (segreCover n m).glueMorphisms (fun ij ↦ bilinearChartHom ℓ hspan ij.1 ij.2)
    fun ij ij' ↦ bilinearChartHom_compatible ℓ hℓ hspan ij.1 ij'.1 ij.2 ij'.2

/-- On the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`, the bilinear morphism is `bilinearChartHom ℓ hspan i j`. -/
@[reassoc]
lemma segreCover_f_comp_bilinear (i : n) (j : m) :
    (segreCover n m).f (i, j) ≫ bilinear n m ℓ hℓ hspan = bilinearChartHom ℓ hspan i j :=
  (segreCover n m).ι_glueMorphisms _ _ (i, j)

/-- Inside the `(i, j)`-chart, the preimage of `D₊(T_c)` under the bilinear morphism is the
basic open of the chart section `bilinearChartSection ℓ i j c`. -/
lemma segreCover_f_preimage_bilinear_preimage (i : n) (j : m) (c : ι) :
    (segreCover n m).f (i, j) ⁻¹ᵁ (bilinear n m ℓ hℓ hspan ⁻¹ᵁ
        basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c)) =
      ((segreCover n m).X (i, j)).basicOpen (bilinearChartSection ℓ i j c) := by
  rw [← Scheme.Hom.comp_preimage, segreCover_f_comp_bilinear, bilinearChartHom,
    fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) c),
    ProjectiveSpace.evalSections_X]

include hℓ in
/-- Inside the `(i, j)`-chart, the preimage of `D₊(ℓ c)` under the Segre morphism is the basic
open of the chart section `bilinearChartSection ℓ i j c`. -/
lemma segreCover_f_preimage_segre_preimage_basicOpen (i : n) (j : m) (c : ι) :
    (segreCover n m).f (i, j) ⁻¹ᵁ (segre n m ⁻¹ᵁ
        basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ)) (ℓ c)) =
      ((segreCover n m).X (i, j)).basicOpen (bilinearChartSection ℓ i j c) := by
  rw [← Scheme.Hom.comp_preimage, segreCover_f_comp_segre, segreChartHom,
    fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos (hℓ c)]
  rfl

/-- **The preimage of a standard open under a bilinear morphism.** The locus where the
homogeneous coordinate `T_c` of `ℙ^ι_ℤ` does not vanish is the preimage under the Segre morphism
of the locus where the linear form `ℓ c` does not vanish. -/
theorem bilinear_preimage_basicOpen (c : ι) :
    bilinear n m ℓ hℓ hspan ⁻¹ᵁ
        basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) =
      segre n m ⁻¹ᵁ basicOpen (homogeneousSubmodule (n × m) (ULift.{u} ℤ)) (ℓ c) := by
  refine Scheme.Opens.ext_of_openCover (segreCover n m) fun ij ↦ ?_
  obtain ⟨i, j⟩ := ij
  rw [segreCover_f_preimage_bilinear_preimage, segreCover_f_preimage_segre_preimage_basicOpen]
  exact hℓ

/-- A bilinear morphism is affine: the preimage of the affine open `D₊(T_c)` is the preimage of
the affine open `D₊(ℓ c)` under the Segre closed immersion. -/
instance isAffineHom_bilinear : IsAffineHom (bilinear n m ℓ hℓ hspan) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  have hx : x ∈ ⨆ c : ι, basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) := by
    rw [iSup_basicOpen_eq_top _ _ (toIdeal_irrelevant_homogeneousSubmodule ι (ULift.{u} ℤ)).le]
    trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨_, hc, isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one _ c) Nat.one_pos, ?_⟩
  rw [bilinear_preimage_basicOpen]
  exact (isAffineOpen_basicOpen _ _ (hℓ c) Nat.one_pos).preimage _

/-- The structure morphism `ℙ^σ_ℤ ⟶ ⊤_` of the integral model of projective space is proper
for a finite index type `σ`. -/
lemma isProper_terminal_from_projectiveSpaceOverAffine (σ : Type u) [Finite σ] :
    IsProper (terminal.from (projectiveSpaceOverAffine σ (ULift.{u} ℤ))) := by
  have hZ : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have hP : terminal.from (projectiveSpaceOverAffine σ (ULift.{u} ℤ)) =
      projectiveSpaceOverAffineToSpec σ (ULift.{u} ℤ) ≫ terminal.from _ := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := hZ ▸ inferInstance
  exact hP ▸ inferInstance

/-- A bilinear morphism is proper, its source being proper and its target separated over the
terminal scheme. -/
instance isProper_bilinear [Finite n] [Finite m] : IsProper (bilinear n m ℓ hℓ hspan) := by
  have := isProper_terminal_from_projectiveSpaceOverAffine n
  have := isProper_terminal_from_projectiveSpaceOverAffine m
  have : IsProper (pullback.fst (terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))
      (terminal.from (projectiveSpaceOverAffine m (ULift.{u} ℤ)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsProper (bilinear n m ℓ hℓ hspan ≫
      terminal.from (projectiveSpaceOverAffine ι (ULift.{u} ℤ))) := by
    rw [terminal.hom_ext (bilinear n m ℓ hℓ hspan ≫ terminal.from _)
      (pullback.fst _ _ ≫ terminal.from (projectiveSpaceOverAffine n (ULift.{u} ℤ)))]
    infer_instance
  have : (projectiveSpaceOverAffine ι (ULift.{u} ℤ)).IsSeparated :=
    inferInstanceAs (Proj _).IsSeparated
  exact IsProper.of_comp _ (terminal.from (projectiveSpaceOverAffine ι (ULift.{u} ℤ)))

/-- **Bilinear morphisms are finite**: they are proper and affine. -/
instance isFinite_bilinear [Finite n] [Finite m] : IsFinite (bilinear n m ℓ hℓ hspan) :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩,
      inferInstance⟩

/-- **The bilinear morphism on points given by global sections.** If `s` and `t` are families of
global sections of a scheme `T` with `s i = 1` and `t j = 1`, the composite of the bilinear
morphism with the pair of morphisms `T ⟶ ℙⁿ_ℤ`, `T ⟶ ℙᵐ_ℤ` given by `s` and `t` is the morphism
given by the sections `ℓ_c(sₖ tₗ)`. -/
lemma pullbackLift_comp_bilinear {T : Scheme.{u}} (s : n → Γ(T, ⊤)) (t : m → Γ(T, ⊤))
    {i : n} {j : m} (hsi : s i = 1) (htj : t j = 1)
    (hs : Ideal.span (Set.range s) = ⊤) (ht : Ideal.span (Set.range t) = ⊤)
    (hst : Ideal.span (Set.range fun c ↦
      ProjectiveSpace.evalSections (fun kl : n × m ↦ s kl.1 * t kl.2) (ℓ c)) = ⊤) :
    pullback.lift
        (fromOfGlobalSections _ (ProjectiveSpace.evalSections s)
          (ProjectiveSpace.map_irrelevant_evalSections_eq_top s hs))
        (fromOfGlobalSections _ (ProjectiveSpace.evalSections t)
          (ProjectiveSpace.map_irrelevant_evalSections_eq_top t ht))
        (terminal.hom_ext _ _) ≫ bilinear n m ℓ hℓ hspan =
      fromOfGlobalSections _ (ProjectiveSpace.evalSections fun c ↦
          ProjectiveSpace.evalSections (fun kl : n × m ↦ s kl.1 * t kl.2) (ℓ c))
        (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ hst) := by
  obtain ⟨qa, hqa, hqa'⟩ := exists_comp_awayι_eq_fromOfGlobalSections
    (homogeneousSubmodule n (ULift.{u} ℤ)) (ProjectiveSpace.evalSections s)
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top s hs) Nat.one_pos
    (X_mem_homogeneousSubmodule_one _ i) (by rw [ProjectiveSpace.evalSections_X, hsi])
  obtain ⟨qb, hqb, hqb'⟩ := exists_comp_awayι_eq_fromOfGlobalSections
    (homogeneousSubmodule m (ULift.{u} ℤ)) (ProjectiveSpace.evalSections t)
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top t ht) Nat.one_pos
    (X_mem_homogeneousSubmodule_one _ j) (by rw [ProjectiveSpace.evalSections_X, htj])
  set w : T ⟶ (segreCover n m).X (i, j) := pullback.lift qa qb (terminal.hom_ext _ _) with hw
  have hwa : w ≫ segreCoverFst i j = qa := pullback.lift_fst _ _ _
  have hwb : w ≫ segreCoverSnd i j = qb := pullback.lift_snd _ _ _
  have hlift : pullback.lift
        (fromOfGlobalSections _ (ProjectiveSpace.evalSections s)
          (ProjectiveSpace.map_irrelevant_evalSections_eq_top s hs))
        (fromOfGlobalSections _ (ProjectiveSpace.evalSections t)
          (ProjectiveSpace.map_irrelevant_evalSections_eq_top t ht))
        (terminal.hom_ext _ _) = w ≫ (segreCover n m).f (i, j) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, ← segreCoverFst_awayι, ← Category.assoc, hwa, hqa]
    · rw [pullback.lift_snd, Category.assoc, ← segreCoverSnd_awayι, ← Category.assoc, hwb, hqb]
  have key : ∀ {R : CommRingCat.{u}} (c : (segreCover n m).X (i, j) ⟶ Spec R) (q : T ⟶ Spec R),
      w ≫ c = q → ∀ z, w.appTop.hom (((Scheme.ΓSpecIso R).inv ≫ c.appTop).hom z) =
        ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom z := by
    rintro R c q rfl z
    rfl
  have hsec (kl : n × m) : w.appTop.hom (segreChartSection i j kl) = s kl.1 * t kl.2 := by
    rw [segreChartSection, map_mul, key _ _ hwa, key _ _ hwb]
    exact congrArg₂ (· * ·) ((hqa' 1 (MvPolynomial.X kl.1) _).trans
      (ProjectiveSpace.evalSections_X s kl.1)) ((hqb' 1 (MvPolynomial.X kl.2) _).trans
      (ProjectiveSpace.evalSections_X t kl.2))
  have hbil (c : ι) : w.appTop.hom (bilinearChartSection ℓ i j c) =
      ProjectiveSpace.evalSections (fun kl : n × m ↦ s kl.1 * t kl.2) (ℓ c) := by
    rw [bilinearChartSection, ← RingHom.comp_apply, ProjectiveSpace.comp_evalSections]
    simp only [hsec]
  rw [hlift, Category.assoc, segreCover_f_comp_bilinear, bilinearChartHom]
  refine (comp_fromOfGlobalSections _ w _ _ (map_irrelevant_comp_appTop_eq_top _ w _
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ (hspan i j)))).trans ?_
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ 1 _ _ (fun d a hda ↦ ?_) _ _
  rw [Units.val_one, one_pow, one_mul, ProjectiveSpace.comp_evalSections]
  simp only [hbil]

/-- **Morphisms into a standard chart are given by global sections.** A morphism
`p : T ⟶ ℙ^ι_ℤ` mapping `T` into the standard open `D₊(T_c)` is the morphism given by the
global sections `p^*(T_l / T_c)`. -/
lemma exists_eq_fromOfGlobalSections {T : Scheme.{u}}
    (p : T ⟶ projectiveSpaceOverAffine ι (ULift.{u} ℤ)) (c : ι)
    (hp : p ⁻¹ᵁ basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) = ⊤) :
    ∃ (v : ι → Γ(T, ⊤)) (hv : Ideal.span (Set.range v) = ⊤), v c = 1 ∧
      p = fromOfGlobalSections _ (ProjectiveSpace.evalSections v)
        (ProjectiveSpace.map_irrelevant_evalSections_eq_top v hv) := by
  have hc := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) c
  have hr : Set.range p ⊆
      Set.range (awayι (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) hc
        Nat.one_pos) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ p ⁻¹ᵁ basicOpen _ (MvPolynomial.X c) := hp ▸ trivial
    rw [← opensRange_awayι _ _ hc Nat.one_pos] at hx
    exact hx
  set r := IsOpenImmersion.lift (awayι _ (MvPolynomial.X c) hc Nat.one_pos) p hr
  have hrp : r ≫ awayι _ _ hc Nat.one_pos = p := IsOpenImmersion.lift_fac _ _ _
  set v : ι → Γ(T, ⊤) := fun l ↦
    ((Scheme.ΓSpecIso _).inv ≫ r.appTop).hom (awayXRatio (ULift.{u} ℤ) c l) with hvdef
  have hvc : v c = 1 := by simp [v]
  have hv : Ideal.span (Set.range v) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hvc]
    exact Ideal.subset_span ⟨c, rfl⟩
  refine ⟨v, hv, hvc, ?_⟩
  obtain ⟨q, hq, hq'⟩ := exists_comp_awayι_eq_fromOfGlobalSections _
    (ProjectiveSpace.evalSections v) (ProjectiveSpace.map_irrelevant_evalSections_eq_top v hv)
    Nat.one_pos hc (by rw [ProjectiveSpace.evalSections_X, hvc])
  rw [← hq, ← hrp]
  congr 1
  have hR : Function.Surjective ((↑) : ℤ → ULift.{u} ℤ) := fun r ↦ ⟨r.down, by ext; simp⟩
  have hon : Set.EqOn ((Scheme.ΓSpecIso _).inv ≫ r.appTop).hom
      ((Scheme.ΓSpecIso _).inv ≫ q.appTop).hom
      (Set.range (awayXRatio (ULift.{u} ℤ) c)) := by
    rintro _ ⟨l, rfl⟩
    exact ((hq' 1 (MvPolynomial.X l) _).trans (ProjectiveSpace.evalSections_X v l)).symm
  refine ext_to_Spec (CommRingCat.hom_ext (RingHom.ext fun z ↦ RingHom.eqOn_set_closure hon ?_))
  rw [MvPolynomial.closure_range_awayXRatio_eq_top _ hR c]
  trivial

/-- Ring homomorphisms commute with evaluation of polynomials with coefficients in `ULift ℤ`. -/
lemma map_eval₂_ulift {σ R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : σ → R)
    (p : MvPolynomial σ (ULift.{u} ℤ)) :
    φ (MvPolynomial.eval₂ ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) g p) =
      MvPolynomial.eval₂ ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom) (φ ∘ g) p := by
  have h : φ.comp ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) =
      (Int.castRingHom S).comp ULift.ringEquiv.toRingHom := RingHom.ext fun x ↦ by simp
  rw [← MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, h,
    MvPolynomial.coe_eval₂Hom]
  rfl

/-- **A surjectivity criterion for bilinear morphisms.** If over every algebraically closed
field `K`, every nonzero vector `v` of homogeneous coordinates is, up to a nonzero scalar, of
the form `ℓ_c(aₖ bₗ)` for nonzero vectors `a` and `b`, then the bilinear morphism is
surjective. -/
theorem surjective_bilinear
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (v : ι → K), (∃ c, v c ≠ 0) →
      ∃ (a : n → K) (b : m → K) (i : n) (j : m) (κ : K), a i = 1 ∧ b j = 1 ∧ κ ≠ 0 ∧ ∀ c,
        MvPolynomial.eval₂ ((Int.castRingHom K).comp ULift.ringEquiv.toRingHom)
          (fun kl : n × m ↦ a kl.1 * b kl.2) (ℓ c) = κ * v c) :
    Surjective (bilinear n m ℓ hℓ hspan) := by
  refine ⟨fun y ↦ ?_⟩
  have hy : y ∈ ⨆ c : ι, basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) := by
    rw [iSup_basicOpen_eq_top _ _ (toIdeal_irrelevant_homogeneousSubmodule ι (ULift.{u} ℤ)).le]
    trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  set K := AlgebraicClosure ((projectiveSpaceOverAffine ι (ULift.{u} ℤ)).residueField y)
  set p : Spec (.of K) ⟶ projectiveSpaceOverAffine ι (ULift.{u} ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap
      ((projectiveSpaceOverAffine ι (ULift.{u} ℤ)).residueField y : Type u) K)) ≫
      (projectiveSpaceOverAffine ι (ULift.{u} ℤ)).fromSpecResidueField y with hpdef
  have hpy (x : Spec (.of K)) : p x = y := by
    rw [hpdef, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hp : p ⁻¹ᵁ basicOpen (homogeneousSubmodule ι (ULift.{u} ℤ)) (MvPolynomial.X c) = ⊤ :=
    top_unique fun x _ ↦ by
      rw [Scheme.Hom.mem_preimage, hpy]
      exact hc
  obtain ⟨v, hv, hvc, hpv⟩ := exists_eq_fromOfGlobalSections p c hp
  set e := Scheme.ΓSpecIso (.of K)
  obtain ⟨a, b, i, j, κ, hai, hbj, hκ, habv⟩ := H K (fun l ↦ e.hom (v l))
    ⟨c, by simp [hvc]⟩
  set φ : K →+* Γ(Spec (.of K), ⊤) := e.inv.hom
  have hφ (z : Γ(Spec (.of K), ⊤)) : φ (e.hom z) = z := by
    simp [φ]
  have hsi : (φ ∘ a) i = 1 := by simp [hai]
  have htj : (φ ∘ b) j = 1 := by simp [hbj]
  have hst (c' : ι) : ProjectiveSpace.evalSections
      (fun kl : n × m ↦ (φ ∘ a) kl.1 * (φ ∘ b) kl.2) (ℓ c') = φ κ * v c' := by
    have := congrArg φ (habv c')
    rw [map_eval₂_ulift, map_mul, hφ] at this
    have hfun : (φ ∘ fun kl : n × m ↦ a kl.1 * b kl.2) =
        fun kl ↦ (φ ∘ a) kl.1 * (φ ∘ b) kl.2 := funext fun kl ↦ map_mul φ _ _
    rw [hfun] at this
    exact this
  have hκu : IsUnit (φ κ) := (IsUnit.mk0 κ hκ).map φ
  have hspan_st : Ideal.span (Set.range fun c' ↦ ProjectiveSpace.evalSections
      (fun kl : n × m ↦ (φ ∘ a) kl.1 * (φ ∘ b) kl.2) (ℓ c')) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hmem : φ κ ∈ Ideal.span (Set.range fun c' ↦ ProjectiveSpace.evalSections
        (fun kl : n × m ↦ (φ ∘ a) kl.1 * (φ ∘ b) kl.2) (ℓ c')) :=
      Ideal.subset_span ⟨c, (hst c).trans (by rw [hvc, mul_one])⟩
    simpa using Ideal.mul_mem_left _ (hκu.unit⁻¹ : Γ(Spec (.of K), ⊤)ˣ).1 hmem
  have hspan_a : Ideal.span (Set.range (φ ∘ a)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsi]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hspan_b : Ideal.span (Set.range (φ ∘ b)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← htj]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hlift := pullbackLift_comp_bilinear ℓ hℓ hspan (φ ∘ a) (φ ∘ b) hsi htj hspan_a hspan_b
    hspan_st
  have heq : fromOfGlobalSections _ (ProjectiveSpace.evalSections fun c' ↦
      ProjectiveSpace.evalSections (fun kl : n × m ↦ (φ ∘ a) kl.1 * (φ ∘ b) kl.2) (ℓ c'))
        (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ hspan_st) = p := by
    rw [hpv]
    exact (fromOfGlobalSections_evalSections_eq_of_unit_mul hκu.unit
      (fun c' ↦ (hst c').trans (by rw [IsUnit.unit_spec])) _ _).symm
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine ⟨pullback.lift
      (fromOfGlobalSections _ (ProjectiveSpace.evalSections (φ ∘ a))
        (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ hspan_a))
      (fromOfGlobalSections _ (ProjectiveSpace.evalSections (φ ∘ b))
        (ProjectiveSpace.map_irrelevant_evalSections_eq_top _ hspan_b))
      (terminal.hom_ext _ _) x, ?_⟩
  rw [← Scheme.Hom.comp_apply, hlift, heq, hpy]

end Bilinear

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n m ι : Type u} (ℓ : ι → MvPolynomial (n × m) (ULift.{u} ℤ))
  (hℓ : ∀ c, ℓ c ∈ homogeneousSubmodule (n × m) (ULift.{u} ℤ) 1)
  (hspan : ∀ i j, Ideal.span (Set.range (Proj.bilinearChartSection ℓ i j)) = ⊤) (S : Scheme.{u})

/-- **The relative bilinear morphism** `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(ι; S)`, obtained from the
bilinear morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^ι_ℤ` of the integral models by base change along the
structure morphism of `S`. -/
def bilinear : pullback (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S) ⟶ ℙ(ι; S) :=
  pullback.lift (pullback.fst _ _ ≫ (ℙ(n; S) ↘ S))
    (prodToProjInt n m S ≫ Proj.bilinear n m ℓ hℓ hspan) (terminal.hom_ext _ _)

/-- The relative bilinear morphism is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma bilinear_over :
    bilinear ℓ hℓ hspan S ≫ (ℙ(ι; S) ↘ S) = pullback.fst _ _ ≫ (ℙ(n; S) ↘ S) :=
  pullback.lift_fst _ _ _

/-- The relative bilinear morphism is compatible with the bilinear morphism of the integral
models. -/
@[reassoc (attr := simp)]
lemma bilinear_toProjInt :
    bilinear ℓ hℓ hspan S ≫ toProjInt ι S = prodToProjInt n m S ≫ Proj.bilinear n m ℓ hℓ hspan :=
  pullback.lift_snd _ _ _

/-- **The relative bilinear morphism is the base change of the bilinear morphism of the
integral models** along the map `ℙ(ι; S) ⟶ ℙ^ι_ℤ`. -/
lemma isPullback_bilinear :
    IsPullback (prodToProjInt n m S) (bilinear ℓ hℓ hspan S) (Proj.bilinear n m ℓ hℓ hspan)
      (toProjInt ι S) := by
  refine IsPullback.of_bot ?_ (bilinear_toProjInt ℓ hℓ hspan S).symm
    (isPullback_over_toProjInt ι S).flip
  rw [bilinear_over, terminal.hom_ext (Proj.bilinear n m ℓ hℓ hspan ≫
    terminal.from (Proj.projectiveSpaceOverAffine ι (ULift.{u} ℤ))) (terminal.from _)]
  exact (isPullback_prodToProjInt n m S).flip

/-- The relative bilinear morphism is finite, being a base change of a finite morphism. -/
instance isFinite_bilinear [Finite n] [Finite m] : IsFinite (bilinear ℓ hℓ hspan S) :=
  MorphismProperty.of_isPullback (isPullback_bilinear ℓ hℓ hspan S) inferInstance

/-- The relative bilinear morphism is surjective if the bilinear morphism of the integral models
is, being a base change of it. -/
lemma surjective_bilinear (h : Surjective (Proj.bilinear n m ℓ hℓ hspan)) :
    Surjective (bilinear ℓ hℓ hspan S) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_bilinear ℓ hℓ hspan S) h

end AlgebraicGeometry.ProjectiveSpace
