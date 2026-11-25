/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections

/-!
# The universal property of the strict localization

Let `s: Spec Ω ⟶ S` be a geometric point. We show that the strict localization `S_(s)` is
universal among strictly henselian local schemes `Spec B` over `S` equipped with a geometric
point `p₀: Spec Ω ⟶ Spec B` over the closed point and over `s`: there is a morphism
`Spec B ⟶ S_(s)` over `S` carrying `p₀` to the canonical geometric point of `S_(s)`
(`exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing`), and it is unique, even for
`B` only local (`hom_strictLocalization_ext`).

Indeed, `S_(s)` is the limit of the affine pointed étale neighbourhoods `(V, v)` of `s`, and
a strictly henselian local scheme lifts uniquely through each of them
(`exists_lift_comp_eq_of_isStrictlyHenselianLocalRing`, `lift_ext_of_comp_eq`).

## References

- Stacks Project, Lemma 59.33.1, <https://stacks.math.columbia.edu/tag/04HX>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Lift

variable {A : Type u} [CommRing A] {X V : Scheme.{u}}

/-- Two morphisms `ℓ₁ ℓ₂ : Spec A ⟶ V` from a local scheme to an unramified `X`-scheme which agree
over `X` and after composition with a morphism `c` hitting the closed point are equal: their
agreement locus is open and contains the closed point. -/
lemma lift_ext_of_comp_eq [IsLocalRing A] (p : V ⟶ X) [FormallyUnramified p] [LocallyOfFiniteType p]
    {ℓ₁ ℓ₂ : Spec (.of A) ⟶ V} (hp : ℓ₁ ≫ p = ℓ₂ ≫ p) {T : Scheme.{u}} (c : T ⟶ Spec (.of A))
    (t : T) (ht : c t = IsLocalRing.closedPoint A) (h : c ≫ ℓ₁ = c ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
  have hmem : IsLocalRing.closedPoint A ∈ FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp :=
    FormallyUnramified.range_subset_eqLocus p ℓ₁ ℓ₂ hp c h ⟨t, ht⟩
  have htop : FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp = ⊤ := by
    simpa using preimage_eq_top_of_closedPoint_mem (𝟙 (Spec (.of A))) hmem
  have : IsIso (FormallyUnramified.eqLocus p ℓ₁ ℓ₂ hp).ι := by
    rw [htop]
    exact (Spec (.of A)).topIso.isIso_hom
  exact (cancel_epi _).1 (FormallyUnramified.eqLocus_ι_comp_eq p ℓ₁ ℓ₂ hp)

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue field of `Spec A` at the closed point is separably closed if the residue field
of the local ring `A` is. -/
lemma isSepClosed_residueField_closedPoint [IsLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] :
    IsSepClosed ((Spec (.of A)).residueField (IsLocalRing.closedPoint A)) :=
  have : IsSepClosed (CommRingCat.of (IsLocalRing.closedPoint A).asIdeal.ResidueField) :=
    IsSepClosed.of_ringEquiv (k := IsLocalRing.ResidueField A) (RingEquiv.ofBijective _
      (IsLocalRing.maximalIdeal A).bijective_algebraMap_quotient_residueField)
  IsSepClosed.of_ringEquiv
    (Spec.residueFieldIso (.of A) (IsLocalRing.closedPoint A)).commRingCatIsoToRingEquiv.symm

variable [IsStrictlyHenselianLocalRing A]

/-- **Lifting through étale morphisms.** Let `A` be strictly henselian, `a : Spec A ⟶ X`,
`p : V ⟶ X` étale and `p₀ : Spec Ω ⟶ Spec A` a morphism from the spectrum of a field hitting
the closed point. Every lift `w : Spec Ω ⟶ V` of `p₀ ≫ a` extends to a lift `Spec A ⟶ V` of
`a`. -/
theorem exists_lift_comp_eq_of_isStrictlyHenselianLocalRing (a : Spec (.of A) ⟶ X) (p : V ⟶ X)
    [AlgebraicGeometry.Etale p] {Ω : Type u} [Field Ω] (p₀ : Spec (.of Ω) ⟶ Spec (.of A))
    (hp₀ : p₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A)
    (w : Spec (.of Ω) ⟶ V) (hw : w ≫ p = p₀ ≫ a) :
    ∃ ℓ : Spec (.of A) ⟶ V, ℓ ≫ p = a ∧ p₀ ≫ ℓ = w := by
  obtain ⟨σ, hσ, hσy⟩ := exists_section_apply_eq_of_isStrictlyHenselianLocalRing
    (pullback.snd p a) (pullback.lift w p₀ hw (IsLocalRing.closedPoint Ω))
    (by rw [← Scheme.Hom.comp_apply, pullback.lift_snd, hp₀])
  refine ⟨σ ≫ pullback.fst p a, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  · have hpt : (p₀ ≫ σ) (IsLocalRing.closedPoint Ω) =
        pullback.lift w p₀ hw (IsLocalRing.closedPoint Ω) := by
      rw [Scheme.Hom.comp_apply, hp₀, hσy]
    have hsnd : pullback.snd p a ((p₀ ≫ σ) (IsLocalRing.closedPoint Ω)) =
        IsLocalRing.closedPoint A := by
      rw [Scheme.Hom.comp_apply, hp₀, ← Scheme.Hom.comp_apply, hσ]
      rfl
    have hsep : IsSepClosed ((Spec (.of A)).residueField
        (pullback.snd p a ((p₀ ≫ σ) (IsLocalRing.closedPoint Ω)))) := by
      rw [hsnd]
      exact isSepClosed_residueField_closedPoint
    have hd : (default : Spec (.of Ω)) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    have : p₀ ≫ σ = pullback.lift w p₀ hw := by
      refine eq_of_comp_eq_of_isSepClosed (pullback.snd p a) ?_ ?_ ?_
      · rw [Category.assoc, hσ, Category.comp_id, pullback.lift_snd]
      · rw [hd]
        exact hpt
      · rw [hd]
        exact hsep
    rw [← Category.assoc, this, pullback.lift_fst]

end Lift

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The evaluation `𝒪^{sh}_{S,s} ⟶ Ω` at the geometric point is a local homomorphism. -/
instance isLocalHom_strictHenselizationEval : IsLocalHom (strictHenselizationEval s).hom :=
  ⟨fun a ha ↦ (isUnit_iff_strictHenselizationEval_ne_zero a).2 ha.ne_zero⟩

/-- The canonical geometric point of the strict localization lies over the closed point. -/
lemma spec_map_strictHenselizationEval_apply (x : Spec (.of Ω)) :
    Spec.map (strictHenselizationEval s) x = IsLocalRing.closedPoint (strictHenselization s) := by
  rw [Subsingleton.elim x (IsLocalRing.closedPoint _)]
  exact IsLocalRing.comap_closedPoint (strictHenselizationEval s).hom

/-- The strict henselization is a strictly henselian local ring. -/
lemma isStrictlyHenselianLocalRing_strictHenselization' :
    IsStrictlyHenselianLocalRing (strictHenselization s) :=
  isStrictlyHenselianLocalRing_strictHenselization.{u} s

variable {B : Type u} [CommRing B]

/-- **Uniqueness of morphisms to the strict localization.** Two morphisms from a local scheme
`Spec B` to the strict localization `S_(s)` which agree over `S` and after composition with a
morphism `p₀` hitting the closed point are equal. -/
lemma hom_strictLocalization_ext {R : CommRingCat.{u}} [IsLocalRing R]
    {ℓ₁ ℓ₂ : Spec R ⟶ strictLocalization s}
    (h : ℓ₁ ≫ strictLocalizationToBase s = ℓ₂ ≫ strictLocalizationToBase s)
    {T : Scheme.{u}} (p₀ : T ⟶ Spec R) (t : T) (ht : p₀ t = IsLocalRing.closedPoint R)
    (hp₀ : p₀ ≫ ℓ₁ = p₀ ≫ ℓ₂) : ℓ₁ = ℓ₂ := by
  refine (isLimitStrictLocalizationCone s).hom_ext fun x ↦ ?_
  refine lift_ext_of_comp_eq (A := R) x.obj.1.hom ?_ p₀ t ht ?_
  · rw [Category.assoc, Category.assoc, strictLocalizationCone_π_app_hom, h]
  · rw [reassoc_of% hp₀]

variable [IsStrictlyHenselianLocalRing B]

/-- The cone over the affine pointed étale neighbourhoods of `s` with point a strictly henselian
local scheme `Spec B` over `S`, given by the lifts of the geometric point `p₀`. -/
noncomputable def strictlyHenselianCone (a : Spec (.of B) ⟶ S) (p₀ : Spec (.of Ω) ⟶ Spec (.of B))
    (hp₀ : p₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint B) (ha : p₀ ≫ a = s) :
    Cone (affineNeighborhoodDiagram s) where
  pt := Spec (.of B)
  π :=
    { app x := (exists_lift_comp_eq_of_isStrictlyHenselianLocalRing a x.obj.1.hom p₀ hp₀
        x.obj.2.left ((CategoryTheory.Over.w x.obj.2).trans ha.symm)).choose
      naturality x y f := by
        have hx := (exists_lift_comp_eq_of_isStrictlyHenselianLocalRing a x.obj.1.hom p₀ hp₀
          x.obj.2.left ((CategoryTheory.Over.w x.obj.2).trans ha.symm)).choose_spec
        have hy := (exists_lift_comp_eq_of_isStrictlyHenselianLocalRing a y.obj.1.hom p₀ hp₀
          y.obj.2.left ((CategoryTheory.Over.w y.obj.2).trans ha.symm)).choose_spec
        refine (Category.id_comp _).trans
          (lift_ext_of_comp_eq y.obj.1.hom ?_ p₀ _ hp₀ ?_).symm
        · rw [hy.1, Category.assoc]
          exact (congrArg (_ ≫ ·) f.hom.1.w).trans hx.1
        · rw [hy.2, reassoc_of% hx.2]
          exact congrArg CommaMorphism.left f.hom.2 }

/-- **Existence of morphisms to the strict localization.** A strictly henselian local scheme
`Spec B` over `S` with a geometric point `p₀` over `s` and over the closed point maps to the
strict localization `S_(s)` over `S`, carrying `p₀` to the canonical geometric point. -/
theorem exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing (a : Spec (.of B) ⟶ S)
    (p₀ : Spec (.of Ω) ⟶ Spec (.of B))
    (hp₀ : p₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint B) (ha : p₀ ≫ a = s) :
    ∃ k : Spec (.of B) ⟶ strictLocalization s,
      k ≫ strictLocalizationToBase s = a ∧
        p₀ ≫ k = Spec.map (strictHenselizationEval s) := by
  let c := strictlyHenselianCone s a p₀ hp₀ ha
  have hc (x : AffinePointedEtaleNeighborhood s) :=
    (exists_lift_comp_eq_of_isStrictlyHenselianLocalRing a x.obj.1.hom p₀ hp₀ x.obj.2.left
      ((CategoryTheory.Over.w x.obj.2).trans ha.symm)).choose_spec
  obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood s)
  refine ⟨(isLimitStrictLocalizationCone s).lift c, ?_, ?_⟩
  · rw [← strictLocalizationCone_π_app_hom s x, (isLimitStrictLocalizationCone s).fac_assoc]
    exact (hc x).1
  · refine (isLimitStrictLocalizationCone s).hom_ext fun y ↦ ?_
    rw [Category.assoc, (isLimitStrictLocalizationCone s).fac,
      spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app]
    exact (hc y).2

end AlgebraicGeometry.Scheme
