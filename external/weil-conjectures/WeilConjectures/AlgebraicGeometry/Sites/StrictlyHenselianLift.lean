/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Lifting étale neighbourhoods to a strictly henselian local scheme

Let `A` be a strictly henselian local ring with residue field `κ`, and `a : Spec A ⟶ X` a
morphism of schemes. Write `s̄ : Spec κ ⟶ Spec A ⟶ X` for the closed geometric point. For an
étale `X`-scheme `V` and a lift `v : Spec κ ⟶ V` of `s̄`, there is a unique lift
`ℓ : Spec A ⟶ V` of `a` restricting to `v` on the closed point
(`AlgebraicGeometry.Scheme.existsUnique_lift_of_isStrictlyHenselianLocalRing`): existence is the
section of the étale `V ×_X Spec A ⟶ Spec A` through the point of `v`, and uniqueness holds since
two lifts agree on an open subscheme of the local scheme `Spec A`
(`AlgebraicGeometry.FormallyUnramified.eqLocus`) containing the closed point.

This is the specialization from the geometric points of `Spec A` to its closed geometric point:
the étale neighbourhoods of `s̄` are the étale neighbourhoods of `Spec A ⟶ X`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_section_comp_eq_of_isStrictlyHenselianLocalRing`: a section
  of an étale `Y ⟶ Spec A` through a given geometric point over the closed point.
- `AlgebraicGeometry.Scheme.existsUnique_lift_of_isStrictlyHenselianLocalRing`: unique lifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Field

variable {X Y : Scheme.{u}} {K : Type u} [Field K]

/-- Two morphisms `Spec K ⟶ X` from the spectrum of a field through the same point `x` agree as
soon as they agree after composition with a morphism `f : X ⟶ Y` whose residue field map at `x`
is surjective. -/
lemma eq_of_comp_eq_of_surjective_residueFieldMap (f : X ⟶ Y) (g₁ g₂ : Spec (.of K) ⟶ X)
    (h : g₁ ≫ f = g₂ ≫ f) (hpt : g₁ (IsLocalRing.closedPoint K) = g₂ (IsLocalRing.closedPoint K))
    (hsurj : Function.Surjective (f.residueFieldMap (g₁ (IsLocalRing.closedPoint K)))) :
    g₁ = g₂ := by
  apply (SpecToEquivOfField K X).injective
  rw [SpecToEquivOfField_eq_iff]
  refine ⟨hpt, ?_⟩
  have h' := congrArg (SpecToEquivOfField K Y) h
  rw [SpecToEquivOfField_eq_iff] at h'
  obtain ⟨e, he⟩ := h'
  simp only [SpecToEquivOfField_apply_snd, descResidueField_stalkClosedPointTo_comp] at he ⊢
  have hepi : Epi (f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))) :=
    ConcreteCategory.epi_of_surjective _ hsurj
  rw [← cancel_epi (f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))), he,
    Hom.residueFieldMap_congr'_assoc]
  rfl

end Field

variable {A : Type u} [CommRing A]

section Local

variable [IsLocalRing A]

variable (A) in
/-- The closed geometric point `Spec κ ⟶ Spec A` of a local ring `A` with residue field `κ`. -/
noncomputable abbrev closedGeometricPoint :
    Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

lemma closedGeometricPoint_apply (x : Spec (.of (IsLocalRing.ResidueField A))) :
    closedGeometricPoint A x = IsLocalRing.closedPoint A := by
  rw [Subsingleton.elim x (IsLocalRing.closedPoint _)]
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)

/-- The residue field map at the closed point of `Spec A` of the closed geometric point
`Spec κ ⟶ Spec A` is surjective. -/
lemma surjective_descResidueField_closedGeometricPoint :
    Function.Surjective (descResidueField (stalkClosedPointTo (closedGeometricPoint A))) := by
  intro c
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  have h := congrArg (fun φ ↦ φ ((ΓSpecIso (.of A)).inv a))
    (germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (IsLocalRing.residue A)))
  refine ⟨(Spec (.of A)).residue _ ((Spec (.of A)).presheaf.germ ⊤ _ trivial
    ((ΓSpecIso (.of A)).inv a)), ?_⟩
  rw [← CommRingCat.comp_apply, residue_descResidueField, ← CommRingCat.comp_apply]
  refine h.trans ?_
  simp

/-- Let `f : Y ⟶ Spec A` be étale and `y : Spec κ ⟶ Y` a lift of the closed geometric point.
Then the residue field map of `f` at the point of `y` is surjective (indeed bijective): the
residue field of `Y` there embeds into `κ` over the residue field of `A`. -/
lemma surjective_residueFieldMap_of_comp_eq_closedGeometricPoint {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) (y : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Y)
    (hy : y ≫ f = closedGeometricPoint A) :
    Function.Surjective
      (f.residueFieldMap (y (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)))) := by
  have h' := congrArg (SpecToEquivOfField (IsLocalRing.ResidueField A) _) hy
  rw [SpecToEquivOfField_eq_iff] at h'
  obtain ⟨e, he⟩ := h'
  simp only [SpecToEquivOfField_apply_snd, descResidueField_stalkClosedPointTo_comp] at he
  have hc : Function.Surjective
      (f.residueFieldMap (y (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))) ≫
        descResidueField (stalkClosedPointTo y)) := by
    intro c
    obtain ⟨z, hz⟩ := surjective_descResidueField_closedGeometricPoint (A := A) c
    refine ⟨((Spec (.of A)).residueFieldCongr e).inv z, ?_⟩
    rw [he, CommRingCat.comp_apply]
    convert hz
    all_goals first
      | rfl
      | exact ConcreteCategory.congr_hom ((Spec (.of A)).residueFieldCongr e).inv_hom_id z
  have hd : Function.Bijective (descResidueField (stalkClosedPointTo y)) := by
    refine ⟨(descResidueField (stalkClosedPointTo y)).hom.injective, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := hc c
    exact ⟨_, rfl⟩
  intro w
  obtain ⟨z, hz⟩ := hc ((descResidueField (stalkClosedPointTo y)) w)
  exact ⟨z, hd.1 hz⟩

end Local

section Henselian

variable [IsStrictlyHenselianLocalRing A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Over a strictly henselian local ring `A`, an étale morphism `f : Y ⟶ Spec A` has a section
through every point `y` of `Y` over the closed point. -/
theorem exists_section_apply_eq_of_isStrictlyHenselianLocalRing {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) [AlgebraicGeometry.Etale f] (y : Y)
    (hy : f y = IsLocalRing.closedPoint A) :
    ∃ σ : Spec (.of A) ⟶ Y, σ ≫ f = 𝟙 _ ∧ σ (IsLocalRing.closedPoint A) = y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen V := hV
  let B := Γ(Y, V)
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (hV.fromSpec ≫ f)
  have hφ : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  let n := hV.primeIdealOf ⟨y, hyV⟩
  have hn : n.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal A := by
    have h : (Spec.map φ) n = IsLocalRing.closedPoint A := by
      change (Spec.map φ) (hV.primeIdealOf ⟨y, hyV⟩) = _
      rw [hφ, Scheme.Hom.comp_apply, hV.fromSpec_primeIdealOf, hy]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bn := Localization.AtPrime n.asIdeal
  have : Algebra.WeaklyEtale A B := inferInstance
  have : Algebra.WeaklyEtale A Bn := Algebra.WeaklyEtale.trans A B Bn
  have : IsLocalHom (algebraMap A Bn) := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply A B Bn,
      IsLocalization.AtPrime.isUnit_to_map_iff Bn n.asIdeal] at hx
    by_contra hx'
    exact hx (by
      have : x ∈ IsLocalRing.maximalIdeal A := hx'
      rw [← hn] at this
      exact this)
  have hbij := Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := A) (S := Bn)
  let e : A ≃+* Bn := RingEquiv.ofBijective (algebraMap A Bn) hbij
  let ψ : B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap B Bn))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext x
    change e.symm (algebraMap B Bn (algebraMap A B x)) = x
    rw [← IsScalarTower.algebraMap_apply A B Bn]
    exact e.symm_apply_apply x
  refine ⟨Spec.map ψ ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [Scheme.Hom.comp_apply]
    have hpt : (Spec.map ψ) (IsLocalRing.closedPoint A) = n := by
      apply PrimeSpectrum.ext
      change Ideal.comap (e.symm.toRingHom.comp (algebraMap B Bn))
        (IsLocalRing.maximalIdeal A) = n.asIdeal
      rw [← Ideal.comap_comap]
      have he : Ideal.comap e.symm.toRingHom (IsLocalRing.maximalIdeal A) =
          IsLocalRing.maximalIdeal Bn := by
        ext b
        simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact (isUnit_map_iff e.symm b).not
      rw [he]
      exact Localization.AtPrime.under_maximalIdeal
    rw [hpt]
    exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩

/-- Over a strictly henselian local ring `A` with residue field `κ`, an étale morphism
`f : Y ⟶ Spec A` has a section through every lift `y : Spec κ ⟶ Y` of the closed geometric
point. -/
theorem exists_section_comp_eq_of_isStrictlyHenselianLocalRing {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) [AlgebraicGeometry.Etale f]
    (y : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Y) (hy : y ≫ f = closedGeometricPoint A) :
    ∃ σ : Spec (.of A) ⟶ Y, σ ≫ f = 𝟙 _ ∧ closedGeometricPoint A ≫ σ = y := by
  have hy₀ : f (y (IsLocalRing.closedPoint (IsLocalRing.ResidueField A))) =
      IsLocalRing.closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hy, closedGeometricPoint_apply]
  obtain ⟨σ, hσ, hσy⟩ := exists_section_apply_eq_of_isStrictlyHenselianLocalRing f _ hy₀
  refine ⟨σ, hσ, (eq_of_comp_eq_of_surjective_residueFieldMap f y _ ?_ ?_
    (surjective_residueFieldMap_of_comp_eq_closedGeometricPoint f y hy)).symm⟩
  · rw [hy, Category.assoc, hσ, Category.comp_id]
  · rw [Scheme.Hom.comp_apply, closedGeometricPoint_apply, hσy]

variable {X V : Scheme.{u}} (a : Spec (.of A) ⟶ X)

/-- Two lifts `Spec A ⟶ V` of `a : Spec A ⟶ X` to an unramified `X`-scheme `V` which agree on the
closed geometric point agree: their agreement locus is open and contains the closed point. -/
lemma lift_ext (p : V ⟶ X) [FormallyUnramified p] [LocallyOfFiniteType p]
    {ℓ₁ ℓ₂ : Spec (.of A) ⟶ V} (h₁ : ℓ₁ ≫ p = a) (h₂ : ℓ₂ ≫ p = a)
    (h : closedGeometricPoint A ≫ ℓ₁ = closedGeometricPoint A ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
  have hp : ℓ₁ ≫ p = ℓ₂ ≫ p := h₁.trans h₂.symm
  have hmem : IsLocalRing.closedPoint A ∈ FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp := by
    have := FormallyUnramified.range_subset_eqLocus p ℓ₁ ℓ₂ hp _ h
      ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField A), closedGeometricPoint_apply _⟩
    exact this
  have htop : FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp = ⊤ := by
    simpa using preimage_eq_top_of_closedPoint_mem (𝟙 (Spec (.of A))) hmem
  have hι := FormallyUnramified.eqLocus_ι_comp_eq p ℓ₁ ℓ₂ hp
  have : IsIso (FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp).ι := by
    rw [htop]
    exact (Spec (.of A)).topIso.isIso_hom
  exact (cancel_epi _).1 hι

/-- **Lifting étale neighbourhoods of the closed geometric point.** Let `A` be strictly
henselian with residue field `κ`, `a : Spec A ⟶ X` and `p : V ⟶ X` étale. Every lift
`v : Spec κ ⟶ V` of the closed geometric point `Spec κ ⟶ Spec A ⟶ X` extends uniquely to a lift
`Spec A ⟶ V` of `a`. -/
theorem existsUnique_lift_of_isStrictlyHenselianLocalRing (p : V ⟶ X)
    [AlgebraicGeometry.Etale p] (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) :
    ∃! ℓ : Spec (.of A) ⟶ V, ℓ ≫ p = a ∧ closedGeometricPoint A ≫ ℓ = v := by
  obtain ⟨σ, hσ, hσy⟩ := exists_section_comp_eq_of_isStrictlyHenselianLocalRing
    (pullback.snd p a) (pullback.lift v (closedGeometricPoint A) hv) (pullback.lift_snd _ _ _)
  refine ⟨σ ≫ pullback.fst p a, ⟨?_, ?_⟩, fun ℓ ⟨hℓ, hℓv⟩ ↦ ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · rw [← Category.assoc, hσy, pullback.lift_fst]
  · refine lift_ext a p hℓ ?_ ?_
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
    · rw [hℓv, ← Category.assoc, hσy, pullback.lift_fst]

/-- The lift `Spec A ⟶ V` of `a` restricting to a given lift `v : Spec κ ⟶ V` of the closed
geometric point, for `V` étale over `X`. -/
noncomputable def henselianLift (p : V ⟶ X) [AlgebraicGeometry.Etale p]
    (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) : Spec (.of A) ⟶ V :=
  (existsUnique_lift_of_isStrictlyHenselianLocalRing a p v hv).exists.choose

@[reassoc (attr := simp)]
lemma henselianLift_comp (p : V ⟶ X) [AlgebraicGeometry.Etale p]
    (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) : henselianLift a p v hv ≫ p = a :=
  (existsUnique_lift_of_isStrictlyHenselianLocalRing a p v hv).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma closedGeometricPoint_henselianLift (p : V ⟶ X) [AlgebraicGeometry.Etale p]
    (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) :
    closedGeometricPoint A ≫ henselianLift a p v hv = v :=
  (existsUnique_lift_of_isStrictlyHenselianLocalRing a p v hv).exists.choose_spec.2

lemma henselianLift_eq (p : V ⟶ X) [AlgebraicGeometry.Etale p]
    (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) (ℓ : Spec (.of A) ⟶ V) (hℓ : ℓ ≫ p = a)
    (hℓv : closedGeometricPoint A ≫ ℓ = v) : henselianLift a p v hv = ℓ :=
  (existsUnique_lift_of_isStrictlyHenselianLocalRing a p v hv).unique
    ⟨henselianLift_comp a p v hv, closedGeometricPoint_henselianLift a p v hv⟩ ⟨hℓ, hℓv⟩

/-- The lift is natural in the étale `X`-scheme `V`. -/
lemma henselianLift_comp_hom {V' : Scheme.{u}} (p : V ⟶ X) [AlgebraicGeometry.Etale p]
    (p' : V' ⟶ X) [AlgebraicGeometry.Etale p'] (k : V ⟶ V') (hk : k ≫ p' = p)
    (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) :
    henselianLift a p v hv ≫ k = henselianLift a p' (v ≫ k) (by rw [Category.assoc, hk, hv]) :=
  (henselianLift_eq _ _ _ _ _ (by rw [Category.assoc, hk, henselianLift_comp])
    (by rw [closedGeometricPoint_henselianLift_assoc])).symm

end Henselian

end AlgebraicGeometry.Scheme
