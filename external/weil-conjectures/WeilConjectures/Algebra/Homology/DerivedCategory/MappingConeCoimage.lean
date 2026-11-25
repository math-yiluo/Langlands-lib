/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# The mapping cone of a morphism and of its coimage

Let `f : X ⟶ Y` be a morphism of cochain complexes in an abelian category, and let
`f = coimage.π f ≫ factorThruCoimage f` be its factorisation through its coimage
`W = X / ker f`. The induced morphism `ρ : cone(f) ⟶ cone(factorThruCoimage f)` is a degreewise
epimorphism, so that there is a short exact sequence

```
  0 ⟶ ker ρ ⟶ cone(f) ⟶ cone(W ⟶ Y) ⟶ 0,
```

and since `W ⟶ Y` is a monomorphism, `cone(W ⟶ Y)` is quasi-isomorphic to `coker f`. All of this
is functorial in the arrow `f`. In the derived category this gives a triangle
`ker ρ ⟶ cone(f) ⟶ coker f ⟶ (ker ρ)⟦1⟧`, natural in `f`, whose first term is concentrated on
`ker f` (shifted by one): a morphism of arrows which kills `ker f` induces zero on `ker ρ`.

## Main definitions

- `CochainComplex.ConeCoimage.cone`: the functor `f ↦ cone(f)` from arrows.
- `CochainComplex.ConeCoimage.ρ`: the natural map `cone(f) ⟶ cone(factorThruCoimage f)`.
- `CochainComplex.ConeCoimage.ker`: the functor `f ↦ ker ρ`.
- `CochainComplex.ConeCoimage.triangle`: the triangle `ker ρ ⟶ cone(f) ⟶ coker f ⟶ (ker ρ)⟦1⟧`
  in the derived category.

## Main results

- `CochainComplex.ConeCoimage.triangle_distinguished`: the triangle is distinguished.
- `CochainComplex.ConeCoimage.ker_map_eq_zero`: a morphism of arrows `u : f ⟶ g` with
  `kernel.ι f ≫ u.left = 0` induces the zero map `ker ρ_f ⟶ ker ρ_g`.

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CochainComplex.ConeCoimage

open HomComplex mappingCone

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "𝒞" => CochainComplex 𝒜 ℤ

section

variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂)
  (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)

@[reassoc]
lemma map_f_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫ (fst φ₂).1.v p q hpq =
      (fst φ₁).1.v p q hpq ≫ a.f q := by
  subst hpq
  simp [mappingCone.map, ext_from_iff _ (p + 1) p rfl]

@[reassoc]
lemma map_f_snd_v (p : ℤ) :
    (mappingCone.map φ₁ φ₂ a b comm).f p ≫ (snd φ₂).v p p (add_zero p) =
      (snd φ₁).v p p (add_zero p) ≫ b.f p := by
  simp [mappingCone.map, ext_from_iff _ (p + 1) p rfl]

end

/-- The functor sending an arrow `f : X ⟶ Y` to the monomorphism `coimage f ⟶ Y`. -/
@[simps]
noncomputable abbrev coimArrow : Arrow 𝒞 ⥤ Arrow 𝒞 where
  obj f := Arrow.mk (Abelian.factorThruCoimage f.hom)
  map {f g} u := Arrow.homMk
    (cokernel.desc (kernel.ι f.hom) (u.left ≫ Abelian.coimage.π g.hom) (by
      simp [← Category.assoc, Abelian.coimage.comp_π_eq_zero]; simp)) u.right (by
    rw [← cancel_epi (Abelian.coimage.π f.hom)]
    simp)
  map_id f := Arrow.hom_ext _ _ (coequalizer.hom_ext (by simp)) (by simp)
  map_comp u v := Arrow.hom_ext _ _ (coequalizer.hom_ext (by simp)) (by simp)

/-- The functor sending an arrow `f` to its mapping cone. -/
@[simps]
noncomputable abbrev cone : Arrow 𝒞 ⥤ 𝒞 where
  obj f := mappingCone f.hom
  map {f g} u := mappingCone.map f.hom g.hom u.left u.right (Arrow.w u).symm
  map_id _ := mappingCone.map_id _
  map_comp _ _ := mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- The morphism `cone(f) ⟶ cone(factorThruCoimage f)` induced by the projection of the source
of `f` onto its coimage. -/
@[simps]
noncomputable def ρ : cone (𝒜 := 𝒜) ⟶ coimArrow ⋙ cone where
  app f := mappingCone.map f.hom (Abelian.factorThruCoimage f.hom) (Abelian.coimage.π f.hom)
    (𝟙 _) (by simp)
  naturality f g u := by
    have key (p : ℤ) : (Abelian.coimage.π f.hom).f p ≫
        (cokernel.desc (kernel.ι f.hom) (u.left ≫ Abelian.coimage.π g.hom) (by
          simp [← Category.assoc, Abelian.coimage.comp_π_eq_zero]; simp)).f p =
          u.left.f p ≫ (Abelian.coimage.π g.hom).f p := by
      rw [← HomologicalComplex.comp_f, cokernel.π_desc, HomologicalComplex.comp_f]
    ext n
    simp [ext_from_iff _ (n + 1) n rfl, mappingCone.map, reassoc_of% key]

lemma inr_ρ_app (f : Arrow 𝒞) : inr f.hom ≫ (ρ.app f) = inr _ := by
  simp [mappingCone.map]

lemma inl_v_ρ_app_f (f : Arrow 𝒞) (p q : ℤ) (hpq : p + (-1) = q) :
    (inl f.hom).v p q hpq ≫ (ρ.app f).f q =
      (Abelian.coimage.π f.hom).f p ≫ (inl (coimArrow.obj f).hom).v p q hpq := by
  simp [mappingCone.map]

instance (f : Arrow 𝒞) : Epi (ρ.app f) := by
  refine HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z g hg
  rw [ext_from_iff _ (n + 1) n rfl]
  constructor
  · rw [← cancel_epi ((Abelian.coimage.π f.hom).f (n + 1)), ← assoc, ← inl_v_ρ_app_f, assoc, hg]
    simp
  · rw [comp_zero, ← inr_ρ_app, HomologicalComplex.comp_f, assoc, hg, comp_zero]

/-- The kernel of `ρ`, as a functor of the arrow. -/
@[simps]
noncomputable def ker : Arrow 𝒞 ⥤ 𝒞 where
  obj f := kernel (ρ.app f)
  map {f g} u := kernel.map _ _ (cone.map u) ((coimArrow ⋙ cone).map u) (ρ.naturality u).symm
  map_id f := by
    apply equalizer.hom_ext
    simp [mappingCone.map_id]
  map_comp u v := by
    apply equalizer.hom_ext
    simp only [cone_obj, Functor.comp_obj, coimArrow_obj, Arrow.mk_left, Arrow.mk_right,
      Arrow.mk_hom, Arrow.comp_left, Arrow.comp_right, Functor.comp_map, equalizer_as_kernel,
      coequalizer_as_cokernel, assoc, Arrow.homMk_left, Arrow.homMk_right, kernel.lift_ι,
      kernel.lift_ι_assoc]
    rw [← mappingCone.map_comp]

/-- The inclusion `ker ρ ⟶ cone`. -/
@[simps]
noncomputable def kerι : ker (𝒜 := 𝒜) ⟶ cone where
  app f := kernel.ι (ρ.app f)

/-- The short exact sequence `0 ⟶ ker ρ ⟶ cone(f) ⟶ cone(factorThruCoimage f) ⟶ 0`. -/
@[simps]
noncomputable def sequence (f : Arrow 𝒞) : ShortComplex 𝒞 :=
  ShortComplex.mk (kerι.app f) (ρ.app f) (kernel.condition _)

lemma sequence_shortExact (f : Arrow 𝒞) : (sequence f).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := by change Mono (kernel.ι _); infer_instance
  epi_g := by change Epi (ρ.app f); infer_instance

/-- The morphism of short exact sequences induced by a morphism of arrows. -/
@[simps]
noncomputable def sequenceMap {f g : Arrow 𝒞} (u : f ⟶ g) : sequence f ⟶ sequence g where
  τ₁ := ker.map u
  τ₂ := cone.map u
  τ₃ := (coimArrow ⋙ cone).map u
  comm₁₂ := by simp
  comm₂₃ := ρ.naturality u

/-- The short exact sequence `0 ⟶ coimage f ⟶ Y ⟶ coker f ⟶ 0`. -/
@[simps]
noncomputable def cokerSequence (f : Arrow 𝒞) : ShortComplex 𝒞 :=
  ShortComplex.mk (Abelian.factorThruCoimage f.hom) (cokernel.π f.hom) (by
    rw [← cancel_epi (Abelian.coimage.π f.hom)]
    simp)

lemma cokerSequence_shortExact (f : Arrow 𝒞) : (cokerSequence f).ShortExact where
  mono_f := by change Mono (Abelian.factorThruCoimage _); infer_instance
  epi_g := by change Epi (cokernel.π _); infer_instance
  exact := by
    let φ : ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition _) ⟶ cokerSequence f :=
      { τ₁ := Abelian.coimage.π f.hom
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))

/-- The cokernel of an arrow, as a functor. -/
@[simps]
noncomputable abbrev coker : Arrow 𝒞 ⥤ 𝒞 where
  obj f := cokernel f.hom
  map {f g} u := cokernel.map f.hom g.hom u.left u.right (Arrow.w u).symm
  map_id f := by
    apply coequalizer.hom_ext
    simp
  map_comp u v := by
    apply coequalizer.hom_ext
    simp

/-- The quasi-isomorphism `cone(factorThruCoimage f) ⟶ coker f`. -/
@[simps]
noncomputable def desc : coimArrow ⋙ cone (𝒜 := 𝒜) ⟶ coker where
  app f := descShortComplex (cokerSequence f)
  naturality f g u := by
    have := descShortComplex_naturality (S₁ := cokerSequence f) (S₂ := cokerSequence g)
      { τ₁ := ((coimArrow (𝒜 := 𝒜)).map u).left
        τ₂ := u.right
        τ₃ := coker.map u
        comm₁₂ := Arrow.w ((coimArrow (𝒜 := 𝒜)).map u) }
    exact this

instance (f : Arrow 𝒞) : QuasiIso ((desc (𝒜 := 𝒜)).app f) :=
  quasiIso_descShortComplex (cokerSequence_shortExact f)

lemma inr_ρ_desc (f : Arrow 𝒞) : inr f.hom ≫ ρ.app f ≫ desc.app f = cokernel.π f.hom := by
  rw [← assoc, inr_ρ_app]
  exact inr_descShortComplex (cokerSequence f)

/-- A morphism of arrows `u : f ⟶ g` such that `kernel.ι f.hom ≫ u.left = 0` induces the zero
morphism `ker ρ_f ⟶ ker ρ_g`. -/
lemma ker_map_eq_zero {f g : Arrow 𝒞} (u : f ⟶ g) (hu : kernel.ι f.hom ≫ u.left = 0) :
    ker.map u = 0 := by
  rw [← cancel_mono (kernel.ι (ρ.app g)), zero_comp]
  have hk : ker.map u ≫ kernel.ι (ρ.app g) = kernel.ι (ρ.app f) ≫ cone.map u := by
    simp [ker]
  rw [hk]
  have h := kernel.condition (ρ.app f)
  ext n
  rw [HomologicalComplex.zero_f, HomologicalComplex.comp_f, ext_to_iff _ n (n + 1) rfl]
  have h₁ : (kernel.ι (ρ.app f)).f n ≫ (fst f.hom).1.v n (n + 1) rfl ≫
      (Abelian.coimage.π f.hom).f (n + 1) = 0 := by
    have := congrArg (fun φ ↦ φ.f n ≫
      (fst (Abelian.factorThruCoimage f.hom)).1.v n (n + 1) rfl) h
    simpa only [HomologicalComplex.comp_f, assoc, ρ_app, map_f_fst_v,
      HomologicalComplex.zero_f, zero_comp] using this
  have h₂ : (kernel.ι (ρ.app f)).f n ≫ (snd f.hom).v n n (add_zero n) = 0 := by
    have := congrArg (fun φ ↦ φ.f n ≫
      (snd (Abelian.factorThruCoimage f.hom)).v n n (add_zero n)) h
    simpa only [HomologicalComplex.comp_f, assoc, ρ_app, map_f_snd_v, HomologicalComplex.id_f,
      comp_id, HomologicalComplex.zero_f, zero_comp] using this
  simp only [assoc, zero_comp]
  refine ⟨?_, by rw [map_f_snd_v, reassoc_of% h₂, zero_comp]⟩
  rw [map_f_fst_v]
  -- the component in degree `n + 1` of `ker ρ_f ⟶ cone(f) ⟶ X` lands in `ker f`
  have hS : (ShortComplex.mk (kernel.ι f.hom) (Abelian.coimage.π f.hom)
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have hS' := hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (n + 1))
  have := hS'.mono_f
  obtain ⟨y, hy⟩ : ∃ y, y ≫ (kernel.ι f.hom).f (n + 1) =
      (kernel.ι (ρ.app f)).f n ≫ (fst f.hom).1.v n (n + 1) rfl :=
    ⟨hS'.exact.fIsKernel.lift (KernelFork.ofι _ (by simpa using h₁)),
      hS'.exact.fIsKernel.fac _ WalkingParallelPair.zero⟩
  rw [← reassoc_of% hy, ← HomologicalComplex.comp_f, hu, HomologicalComplex.zero_f, comp_zero]

variable [HasDerivedCategory 𝒜]

/-- The triangle `ker ρ ⟶ cone(f) ⟶ coker f ⟶ (ker ρ)⟦1⟧` in the derived category. -/
noncomputable def triangle (f : Arrow 𝒞) : Triangle (DerivedCategory 𝒜) :=
  Triangle.mk (DerivedCategory.Q.map (kerι.app f))
    (DerivedCategory.Q.map (ρ.app f ≫ desc.app f))
    (inv (DerivedCategory.Q.map (desc.app f)) ≫
      DerivedCategory.triangleOfSESδ (sequence_shortExact f))

lemma triangle_distinguished (f : Arrow 𝒞) : triangle f ∈ distTriang _ := by
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished
    (sequence_shortExact f)) _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso (DerivedCategory.Q.map (desc.app f))).symm ?_ ?_ ?_)
  · simp [triangle]
  · simp [triangle]
  · simp [triangle]

lemma triangle_mor₃_naturality {f g : Arrow 𝒞} (u : f ⟶ g) :
    (triangle f).mor₃ ≫ (DerivedCategory.Q.map (ker.map u))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (coker.map u) ≫ (triangle g).mor₃ := by
  have h₁ : DerivedCategory.triangleOfSESδ (sequence_shortExact f) ≫
      (DerivedCategory.Q.map (ker.map u))⟦(1 : ℤ)⟧' =
        DerivedCategory.Q.map ((coimArrow ⋙ cone).map u) ≫
          DerivedCategory.triangleOfSESδ (sequence_shortExact g) :=
    DerivedCategory.triangleOfSESδ_naturality (sequence_shortExact f)
      (sequence_shortExact g) (sequenceMap u)
  have h₂ := DerivedCategory.Q.congr_map (desc.naturality u)
  simp only [Functor.map_comp] at h₂
  simp only [triangle, Triangle.mk_mor₃, assoc]
  rw [h₁, ← assoc, ← assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← assoc, ← h₂, assoc, IsIso.hom_inv_id, comp_id]

end CochainComplex.ConeCoimage
