/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.GeometricFiber

/-!
# Pointed decompositions of the base change of an integral morphism

Let `f : X ⟶ Y` be integral, `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically closed
and `(U₀, u₀)` an affine pointed étale neighbourhood of `y`, with `U₀ ×_Y X = Spec B`. Suppose
that to every geometric point `t` of `X` over `y` is attached a standard étale `B`-algebra
`P (m t)` and a point `χ t` of it over `t`, in a way which only depends on the values of `t` on
finitely many elements of `B`. Then there is a smaller pointed étale neighbourhood `(U, u)` of
`y` and a decomposition of `U ×_Y X` into pairwise disjoint opens, each mapping to one of the
`Spec (P j)` over `Spec B`, such that the point `(u, t)` is carried to `χ t`
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`).

This is the pointed refinement of `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`,
and it is proved in the same way: the data descend to a subalgebra `B₂ ⊆ B` finite over `A`,
where the pieces of a split neighbourhood of the finite morphism `Spec B₂ ⟶ U₀` realise them
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_pieceFunctor_obj_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

namespace AlgebraicGeometry
/-- The ring homomorphism `Γ(Z, ⊤) →+* Ω` of global sections at a geometric point
`p : Spec Ω ⟶ Z`. -/
noncomputable def Scheme.Hom.appTopPoint {Ω : Type u} [Field Ω] {Z : Scheme.{u}}
    (p : Spec (.of Ω) ⟶ Z) : Γ(Z, ⊤) →+* Ω :=
  (p.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom

lemma Scheme.Hom.comp_toSpecΓ {Ω : Type u} [Field Ω] {Z : Scheme.{u}}
    (p : Spec (.of Ω) ⟶ Z) : p ≫ Z.toSpecΓ = Spec.map (CommRingCat.ofHom p.appTopPoint) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

lemma Scheme.Hom.appTopPoint_comp {Ω : Type u} [Field Ω] {Z Z' : Scheme.{u}}
    (p : Spec (.of Ω) ⟶ Z) (g : Z ⟶ Z') :
    (p ≫ g).appTopPoint = p.appTopPoint.comp g.appTop.hom := by
  simp [Scheme.Hom.appTopPoint]

-- Restrict a point of a base-changed algebra before specializing the coefficient rings.
private lemma tensorPoint_restrict_comp {R A C D Ω : Type*}
    [CommRing R] [CommRing A] [CommRing C] [CommRing D] [CommRing Ω]
    [Algebra R A] [Algebra R C] [Algebra A D]
    (e : A ⊗[R] C ≃ₐ[A] D) (χ : D →+* Ω) (ψ : A →+* Ω)
    (hχ : χ.comp (algebraMap A D) = ψ) :
    (χ.comp (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := A)).toRingHom)).comp
        (algebraMap R C) = ψ.comp (algebraMap R A) := by
  ext b
  change χ (e (Algebra.TensorProduct.includeRight (algebraMap R C b))) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A (A ⊗[R] C),
    AlgEquiv.commutes, ← RingHom.comp_apply, hχ]
  rfl

-- A point of the tensor-product chart is determined by its two projections.
private lemma specTensorPoint_eq_of_comp {R A C D Ω : Type u}
    [CommRing R] [CommRing A] [CommRing C] [CommRing D] [CommRing Ω]
    [Algebra R A] [Algebra R C] [Algebra A D]
    (e : A ⊗[R] C ≃ₐ[A] D) (χ : D →+* Ω) (ψ : A →+* Ω)
    (hχ : χ.comp (algebraMap A D) = ψ)
    {T : Scheme.{u}} (q : Spec (.of Ω) ⟶ T)
    (μ₁ : T ⟶ Spec (.of A)) (μ₂ : T ⟶ Spec (.of C))
    (hμ : μ₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      μ₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (h₁ : q ≫ μ₁ = Spec.map (CommRingCat.ofHom ψ))
    (h₂ : q ≫ μ₂ = Spec.map (CommRingCat.ofHom (χ.comp (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := A)).toRingHom)))) :
    q ≫ pullback.lift μ₁ μ₂ hμ ≫ (pullbackSpecIso R A C).hom ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) =
        Spec.map (CommRingCat.ofHom χ) := by
  have key : q ≫ pullback.lift μ₁ μ₂ hμ =
      Spec.map (CommRingCat.ofHom (χ.comp e.toAlgHom.toRingHom)) ≫
        (pullbackSpecIso R A C).inv := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
        ← Spec.map_comp, h₁]
      congr 1
      ext b
      have hb : (Algebra.TensorProduct.includeLeftRingHom b : A ⊗[R] C) =
          algebraMap A _ b := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      change ψ b = χ (e (Algebra.TensorProduct.includeLeftRingHom b))
      rw [hb, AlgEquiv.commutes, ← RingHom.comp_apply, hχ]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
        ← Spec.map_comp, h₂]
      rfl
  rw [reassoc_of% key, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  congr 2
  ext x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact congrArg χ (e.apply_symm_apply x)

namespace Scheme.Hom.Nbhd

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

/-- **Pointed lifting along an integral morphism.** -/
theorem exists_pointed_disjoint_cover (c₀ : Nbhd y) [IsAffine c₀.1.left]
    {J : Type*} (P : J → StandardEtalePair Γ(pullback c₀.1.hom f, ⊤))
    (m : GeometricFiber f y → J) (hmfin : (Set.range m).Finite)
    (χ : ∀ j, {t // m t = j} → ((P j).Ring →+* Ω))
    (hχ : ∀ j t, (χ j t).comp (algebraMap _ _) = (basePt f c₀ t.1).appTopPoint)
    (hm : ∃ S : Finset Γ(pullback c₀.1.hom f, ⊤), ∀ t₁ t₂, (∀ b ∈ S,
      (basePt f c₀ t₁).appTopPoint b = (basePt f c₀ t₂).appTopPoint b) → m t₁ = m t₂)
    (hχS : ∀ j (ζ : (P j).Ring), ∃ S : Finset Γ(pullback c₀.1.hom f, ⊤),
      ∀ t₁ t₂ : {t // m t = j}, (∀ b ∈ S,
        (basePt f c₀ t₁.1).appTopPoint b = (basePt f c₀ t₂.1).appTopPoint b) →
        χ j t₁ ζ = χ j t₂ ζ) :
    ∃ (c : Nbhd y) (h : c ⟶ c₀) (ι : Type u) (Q : ι → (pullback c.1.hom f).Opens) (k : ι → J)
      (ν : ∀ l, (Q l).toScheme ⟶ Spec (.of (P (k l)).Ring)),
      (∀ l l', l ≠ l' → Disjoint (Q l) (Q l')) ∧ ⨆ l, Q l = ⊤ ∧
      (∀ l, ν l ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (P (k l)).Ring)) =
        (Q l).ι ≫ (f.Etale.map h.val).left ≫ (pullback c₀.1.hom f).toSpecΓ) ∧
      ∀ t l (q : Spec (.of Ω) ⟶ Q l), q ≫ (Q l).ι = basePt f c t →
        ∃ e : m t = k l, q ≫ ν l = Spec.map (CommRingCat.ofHom (χ (k l) ⟨t, e⟩)) := by
  classical
  have : IsAffine ((𝟭 Scheme).obj c₀.1.left) := ‹IsAffine c₀.1.left›
  have : IsAffine (pullback c₀.1.hom f) := isAffine_of_isAffineHom (pullback.fst c₀.1.hom f)
  -- `U₀ = Spec A` and `U₀ ×_Y X = Spec B` with `B` integral over `A`
  let A := Γ(c₀.1.left, ⊤)
  let B := Γ(pullback c₀.1.hom f, ⊤)
  let _ : Algebra A B := (pullback.fst c₀.1.hom f).appTop.hom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨fun b ↦
    ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)).mp
      (inferInstance : IsIntegralHom (pullback.fst c₀.1.hom f))).2 b⟩
  -- the finitely many standard étale pairs which occur
  let J' := Set.range m
  have : Finite J' := hmfin.to_subtype
  have := Fintype.ofFinite J'
  obtain ⟨S₀, hS₀⟩ := hm
  -- they descend to `B₁ = A[coefficients]`
  let s₁ : Finset B := Finset.univ.biUnion fun j : J' ↦ (P j.1).f.coeffs ∪ (P j.1).g.coeffs
  let B₁ : Subalgebra A B := Algebra.adjoin A (s₁ : Set B)
  have hs₁ (j : J') (p : Polynomial B) (hp : p.coeffs ⊆ (P j.1).f.coeffs ∪ (P j.1).g.coeffs) :
      ↑p.coeffs ⊆ Set.range (algebraMap B₁ B) := by
    intro b hb
    refine ⟨⟨b, Algebra.subset_adjoin ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp hb⟩
  have hQ₁ (j : J') : ∃ Q : StandardEtalePair B₁, Nonempty (B ⊗[B₁] Q.Ring ≃ₐ[B] (P j.1).Ring) :=
    StandardEtalePair.exists_algEquiv_tensor_ring_of_coeffs_subset (P j.1)
      (hs₁ j _ Finset.subset_union_left) (hs₁ j _ Finset.subset_union_right)
  choose Q₁ hQ₁ using hQ₁
  let e₁ (j : J') := (hQ₁ j).some
  -- the generators `ζ j` of the descended algebras, and the finite sets which determine them
  let ζ (j : J') : (P j.1).Ring := e₁ j (1 ⊗ₜ (Q₁ j).X)
  choose Sζ hSζ using fun j : J' ↦ hχS j.1 (ζ j)
  -- `B₂ = A[coefficients, S₀, Sζ]`, finite over `A`
  let s₂ : Finset B := s₁ ∪ S₀ ∪ Finset.univ.biUnion Sζ
  let B₂ : Subalgebra A B := Algebra.adjoin A (s₂ : Set B)
  have hB₁₂ : B₁ ≤ B₂ := Algebra.adjoin_mono (by
    intro b hb
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hb))
  have : Algebra.FiniteType A B₂ :=
    (Subalgebra.fg_iff_finiteType B₂).mp (Subalgebra.fg_adjoin_finset s₂)
  have : Algebra.IsIntegral A B₂ := ⟨fun x ↦
    (isIntegral_algHom_iff B₂.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral _)⟩
  have : Module.Finite A B₂ := Algebra.IsIntegral.finite
  have : Algebra.IsIntegral B₂ B := Algebra.IsIntegral.tower_top A
  -- the finite morphism `Spec B₂ ⟶ U₀` and the projection `ρ: U₀ ×_Y X ⟶ Spec B₂`
  let gU : Spec (.of B₂) ⟶ c₀.1.left :=
    Spec.map (CommRingCat.ofHom (algebraMap A B₂)) ≫ c₀.1.left.isoSpec.inv
  have : IsFinite gU := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B₂))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
    infer_instance
  let ρ : pullback c₀.1.hom f ⟶ Spec (.of B₂) :=
    (pullback c₀.1.hom f).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap B₂ B))
  have hρ : ρ ≫ gU = pullback.fst c₀.1.hom f := by
    simp only [ρ, gU, Category.assoc]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    change _ ≫ Spec.map (pullback.fst c₀.1.hom f).appTop ≫ _ = _
    rw [← Scheme.isoSpec_hom, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  -- the image in `Spec B₂` of a geometric point of `X` over `y`
  let img (t : GeometricFiber f y) : GeometricFiber gU c₀.2.left :=
    ⟨basePt f c₀ t ≫ ρ, by rw [Category.assoc, hρ, basePt_fst]⟩
  -- every geometric point of `Spec B₂` over `u₀` lifts
  have hlift (t'' : GeometricFiber gU c₀.2.left) : ∃ t : GeometricFiber f y, img t = t'' := by
    let τ'' : B₂ →+* Ω := (Spec.preimage t''.1).hom
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker τ'')
      (⊥ : Ideal B) (by
        rw [Ideal.under_def, Ideal.comap_bot_of_injective _ Subtype.val_injective]
        exact bot_le)
    have : Q.LiesOver (RingHom.ker τ'') := ⟨hQc.symm⟩
    obtain ⟨τ, -⟩ := PointsOver.exists_ker_eq (φ := τ'') Q
    let x : Spec (.of Ω) ⟶ pullback c₀.1.hom f :=
      Spec.map (CommRingCat.ofHom τ.1) ≫ (pullback c₀.1.hom f).isoSpec.inv
    have hx : x ≫ ρ = t''.1 := by
      simp only [x, ρ, Category.assoc]
      rw [← Scheme.isoSpec_hom, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        τ.2]
      simp [τ'']
    have hx' : x ≫ pullback.fst c₀.1.hom f = c₀.2.left := by
      rw [← hρ, ← Category.assoc, hx, t''.2]
    refine ⟨⟨x ≫ pullback.snd c₀.1.hom f, by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hx']
      exact CategoryTheory.Over.w c₀.2⟩, ?_⟩
    apply Subtype.ext
    change basePt f c₀ _ ≫ ρ = _
    rw [basePt_eq_of_comp_fst_eq f c₀ x hx', hx]
  choose L hL using hlift
  -- the image in `Spec B₂` is `Spec` of the restriction of the point to `B₂`
  have himg (t : GeometricFiber f y) : (img t).1 = Spec.map (CommRingCat.ofHom
      ((basePt f c₀ t).appTopPoint.comp (algebraMap B₂ B))) := by
    change basePt f c₀ t ≫ ρ = _
    simp only [ρ]
    rw [← Category.assoc, Scheme.Hom.comp_toSpecΓ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  -- points with the same image agree on `B₂`
  have hagree (t₁ t₂ : GeometricFiber f y) (h : img t₁ = img t₂) (b : B) (hb : b ∈ s₂) :
      (basePt f c₀ t₁).appTopPoint b = (basePt f c₀ t₂).appTopPoint b := by
    have h' := congrArg Subtype.val h
    rw [himg, himg] at h'
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
    simp only [CommRingCat.hom_ofHom] at this
    exact congrArg (fun φ ↦ φ ⟨b, Algebra.subset_adjoin hb⟩) this
  -- `m` only depends on the image in `Spec B₂`
  have hmL (t : GeometricFiber f y) : m t = m (L (img t)) :=
    hS₀ _ _ fun b hb ↦ hagree _ _ (hL _).symm b
      (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
  -- the descended data at a geometric point `t''` of `Spec B₂` over `u₀`
  let j (t'' : GeometricFiber gU c₀.2.left) : J' := ⟨m (L t''), Set.mem_range_self _⟩
  let σ (t'' : GeometricFiber gU c₀.2.left) : (Q₁ (j t'')).Ring →+* Ω :=
    (χ (m (L t'')) ⟨L t'', rfl⟩).comp ((e₁ (j t'')).toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := B₁) (A := B)).toRingHom)
  have hσ (t'' : GeometricFiber gU c₀.2.left) : (σ t'').comp (algebraMap B₁ _) =
      (basePt f c₀ (L t'')).appTopPoint.comp (algebraMap B₁ B) := by
    exact tensorPoint_restrict_comp (e₁ (j t'')) _ _ (hχ _ _)
  -- the inclusion `B₁ ⊆ B₂`
  let ι₁₂ : B₁ →+* B₂ := (Subalgebra.inclusion hB₁₂).toRingHom
  have hι₁₂ : (algebraMap B₂ B).comp ι₁₂ = algebraMap B₁ B := rfl
  -- the pointed étale neighbourhood `Spec B₂ ×_{Spec B₁} Spec Q₁` of `t''`
  have hQet (t'' : GeometricFiber gU c₀.2.left) : AlgebraicGeometry.Etale
      (Spec.map (CommRingCat.ofHom (algebraMap B₁ (Q₁ (j t'')).Ring))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr
      (inferInstanceAs (Algebra.Etale B₁ (Q₁ (j t'')).Ring)))
  let W (t'' : GeometricFiber gU c₀.2.left) : (Spec (.of B₂)).Etale :=
    Scheme.Etale.mk (pullback.fst (Spec.map (CommRingCat.ofHom ι₁₂))
      (Spec.map (CommRingCat.ofHom (algebraMap B₁ (Q₁ (j t'')).Ring))))
  have hpt (t'' : GeometricFiber gU c₀.2.left) : t''.1 ≫ Spec.map (CommRingCat.ofHom ι₁₂) =
      Spec.map (CommRingCat.ofHom (σ t'')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B₁ (Q₁ (j t'')).Ring)) := by
    have h := congrArg Subtype.val (hL t'')
    conv_lhs => rw [← h, himg]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hσ]
    rfl
  let pt (t'' : GeometricFiber gU c₀.2.left) : (pointSmallEtale t''.1).fiber.obj (W t'') :=
    CategoryTheory.Over.homMk (pullback.lift t''.1 (Spec.map (CommRingCat.ofHom (σ t'')))
      (hpt t'')) (pullback.lift_fst _ _ _)
  -- a split neighbourhood whose pieces map to these pointed neighbourhoods
  have hs (t'' : GeometricFiber gU c₀.2.left) : ∃ s : SplitNbhd gU c₀.2.left,
      Nonempty ((SplitNbhd.pieceFunctor t'').obj s ⟶ Functor.elementsMk _ (W t'') (pt t'')) :=
    SplitNbhd.exists_pieceFunctor_obj_hom gU t'' _
  choose s a using hs
  have := Fintype.ofFinite (GeometricFiber gU c₀.2.left)
  obtain ⟨s₀, hs₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image s)
  let a₀ (t'' : GeometricFiber gU c₀.2.left) :
      (SplitNbhd.pieceFunctor t'').obj s₀ ⟶ Functor.elementsMk _ (W t'') (pt t'') :=
    (SplitNbhd.pieceFunctor t'').map
      (hs₀ (Finset.mem_image_of_mem s (Finset.mem_univ t''))).some ≫ (a t'').some
  -- the neighbourhood `(U, u)` of `y` and the map `U ×_Y X ⟶ U ×_{U₀} Spec B₂`
  let c := c₀.comp s₀.obj
  let gm := c₀.compHom s₀.obj
  let θ : pullback c.1.hom f ⟶ pullback s₀.obj.1.hom gU :=
    pullback.lift (pullback.fst _ f) ((f.Etale.map gm.val).left ≫ ρ) (by
      rw [Category.assoc, hρ, Hom.etale_map_left_comp_fst]
      rfl)
  let μ₁ (t'' : GeometricFiber gU c₀.2.left) : (θ ⁻¹ᵁ s₀.piece t'').toScheme ⟶ Spec B :=
    (θ ⁻¹ᵁ s₀.piece t'').ι ≫ (f.Etale.map gm.val).left ≫ (pullback c₀.1.hom f).toSpecΓ
  let μ₂ (t'' : GeometricFiber gU c₀.2.left) :
      (θ ⁻¹ᵁ s₀.piece t'').toScheme ⟶ Spec (.of (Q₁ (j t'')).Ring) :=
    θ.resLE (s₀.piece t'') _ le_rfl ≫ (a₀ t'').val.left ≫ pullback.snd _ _
  have hμ (t'' : GeometricFiber gU c₀.2.left) :
      μ₁ t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ B)) =
        μ₂ t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ (Q₁ (j t'')).Ring)) := by
    have h₁ : (a₀ t'').val.left ≫ pullback.fst _ _ =
        (s₀.piece t'').ι ≫ pullback.snd s₀.obj.1.hom gU :=
      MorphismProperty.Over.w (a₀ t'').val
    simp only [μ₁, μ₂, Category.assoc]
    rw [← pullback.condition, reassoc_of% h₁, ← hι₁₂, CommRingCat.ofHom_comp, Spec.map_comp,
      Scheme.Hom.resLE_comp_ι_assoc]
    simp [θ, ρ]
  let ν (t'' : GeometricFiber gU c₀.2.left) :
      (θ ⁻¹ᵁ s₀.piece t'').toScheme ⟶ Spec (.of (P (j t'').1).Ring) :=
    pullback.lift (μ₁ t'') (μ₂ t'') (hμ t'') ≫ (pullbackSpecIso B₁ B (Q₁ (j t'')).Ring).hom ≫
      Spec.map (CommRingCat.ofHom (e₁ (j t'')).symm.toRingEquiv.toRingHom)
  refine ⟨c, gm, GeometricFiber gU c₀.2.left, fun t'' ↦ θ ⁻¹ᵁ s₀.piece t'',
    fun t'' ↦ (j t'').1, ν, ?_, ?_, ?_, ?_⟩
  · intro t t' htt'
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (s₀.disjoint t t' htt').eq_bot,
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, s₀.iSup_eq, Scheme.Hom.preimage_top]
  · intro t''
    have h : CommRingCat.ofHom (algebraMap B (P (j t'').1).Ring) ≫
        CommRingCat.ofHom (e₁ (j t'')).symm.toRingEquiv.toRingHom =
          CommRingCat.ofHom (algebraMap B (B ⊗[B₁] (Q₁ (j t'')).Ring)) := by
      ext b
      exact (e₁ (j t'')).symm.commutes b
    simp only [ν, Category.assoc]
    rw [← Spec.map_comp, h, pullbackSpecIso_hom_fst', pullback.lift_fst]
  · intro t l q hq
    -- `θ` carries `(u, t)` to the point `(u₀', img t)`
    have hθ : basePt f c t ≫ θ = basePt gU s₀.obj (img t) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, basePt_fst, basePt_fst]
        rfl
      · rw [Category.assoc, pullback.lift_snd, basePt_snd, ← Category.assoc,
          basePt_comp_etale_map_left]
    -- so the piece containing `(u, t)` is the one of `img t`
    have hl : img t = l := by
      by_contra hne
      have h₁ : basePt gU s₀.obj (img t) default ∈ s₀.piece l := by
        rw [← hθ, ← hq]
        have hmem : (θ ⁻¹ᵁ s₀.piece l).ι (q default) ∈ θ ⁻¹ᵁ s₀.piece l :=
          (Scheme.Opens.range_ι _).subset ⟨_, rfl⟩
        simp only [Scheme.Hom.comp_apply]
        exact hmem
      exact (s₀.disjoint _ _ hne).le_bot ⟨s₀.mem (img t), h₁⟩
    subst hl
    refine ⟨hmL t, ?_⟩
    let j₀ := j (img t)
    -- the points `L (img t)` and `t` agree on `B₂`
    have hB₂ : (basePt f c₀ (L (img t))).appTopPoint.comp (algebraMap B₂ B) =
        (basePt f c₀ t).appTopPoint.comp (algebraMap B₂ B) := by
      have h' := congrArg Subtype.val (hL (img t))
      rw [himg, himg] at h'
      have := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
      simpa only [CommRingCat.hom_ofHom] using this
    -- the restriction of `χ t` to `Q₁`
    let σt : (Q₁ j₀).Ring →+* Ω :=
      (χ j₀.1 ⟨t, hmL t⟩).comp ((e₁ j₀).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := B₁) (A := B)).toRingHom)
    have hσt' : σt.comp (algebraMap B₁ _) =
        (basePt f c₀ t).appTopPoint.comp (algebraMap B₁ B) := by
      exact tensorPoint_restrict_comp (e₁ j₀) _ _ (hχ _ _)
    have hσt : σ (img t) = σt := by
      let : Algebra B₁ Ω := ((basePt f c₀ t).appTopPoint.comp (algebraMap B₁ B)).toAlgebra
      let φ₁ : (Q₁ j₀).Ring →ₐ[B₁] Ω :=
        { σ (img t) with
          commutes' := fun b ↦ by
            have h₁ := congrArg (fun φ : B₁ →+* Ω ↦ φ b) (hσ (img t))
            have h₂ := congrArg (fun φ : B₂ →+* Ω ↦ φ (ι₁₂ b)) hB₂
            exact h₁.trans h₂ }
      let φ₂ : (Q₁ j₀).Ring →ₐ[B₁] Ω :=
        { σt with
          commutes' := fun b ↦ congrArg (fun φ : B₁ →+* Ω ↦ φ b) hσt' }
      have : φ₁ = φ₂ := StandardEtalePair.hom_ext (by
        change χ j₀.1 ⟨L (img t), rfl⟩ (ζ j₀) = χ j₀.1 ⟨t, hmL t⟩ (ζ j₀)
        refine hSζ j₀ _ _ fun b hb ↦ hagree _ _ (hL (img t)) b ?_
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j₀, Finset.mem_univ _, hb⟩))
      exact congrArg AlgHom.toRingHom this
    -- the point of the piece over `(u, t)`
    have hq₂ : q ≫ θ.resLE (s₀.piece (img t)) _ le_rfl = (s₀.piecePt (img t)).left := by
      rw [← cancel_mono (s₀.piece (img t)).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
        reassoc_of% hq, hθ, SplitNbhd.piecePt_left_ι]
    have ha₀ : (s₀.piecePt (img t)).left ≫ (a₀ (img t)).val.left = (pt (img t)).left :=
      congrArg CommaMorphism.left (a₀ (img t)).map_val
    change q ≫ pullback.lift (μ₁ (img t)) (μ₂ (img t)) (hμ (img t)) ≫
      (pullbackSpecIso B₁ B (Q₁ j₀).Ring).hom ≫
        Spec.map (CommRingCat.ofHom (e₁ j₀).symm.toRingEquiv.toRingHom) = _
    apply specTensorPoint_eq_of_comp (e₁ j₀) (χ j₀.1 ⟨t, hmL t⟩)
      (basePt f c₀ t).appTopPoint (hχ _ _) q _ _ _
    · simp only [μ₁]
      rw [reassoc_of% hq, ← Category.assoc (basePt f c t), basePt_comp_etale_map_left]
      exact Scheme.Hom.comp_toSpecΓ _
    · simp only [μ₂]
      rw [reassoc_of% hq₂, reassoc_of% ha₀]
      erw [pullback.lift_snd]
      rw [hσt]

end Scheme.Hom.Nbhd

end AlgebraicGeometry
