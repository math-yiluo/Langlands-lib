import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Affine cocycle reductions over arbitrary base schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeUnipotent.AffineCocycle

open SplitUnipotentAffineTorsor

variable {B : Scheme.{u}}

/-- Cocycles vanish after passage to every affine test scheme and every affine
flat surjective cover of that test scheme. -/
def CocyclesVanish (H : GroupScheme B) : Prop :=
  ∀ (T : Over B) [IsAffine T.left] (U : Over T.left) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj H) U), ξ.IsTrivial

/-- On a spectrum this predicate is the existing split-torsor predicate. -/
theorem cocyclesVanish_overSpec_iff {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) :
    CocyclesVanish H ↔ SplitUnipotentAffineTorsor.CocyclesVanish H := Iff.rfl

/-- For the trivial group every cocycle is trivial. -/
theorem cocyclesVanish_of_range_id_eq_bot {H : GroupScheme B}
    (hH : SubgroupFunctor.range (𝟙 H) = ⊥) : CocyclesVanish H := by
  intro T _ U _ _ _ ξ
  have hpt : ∀ {Z : Over T.left} (x : Z ⟶ ((GroupScheme.baseChange T.hom).obj H).X), x = 1 := by
    intro Z x
    apply (baseChangePointsEquiv T.hom H Z).injective
    have hmem : baseChangePointsEquiv T.hom H Z x ∈
        (SubgroupFunctor.range (𝟙 H)).carrier ((Over.map T.hom).obj Z) :=
      SubgroupFunctor.mem_range.mpr ⟨_, Category.comp_id _⟩
    rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  exact ⟨1, fun a b => (hpt _).trans (hpt _).symm⟩

section Step

variable {K H V : GroupScheme B} (j : K ⟶ H) (q : H ⟶ V) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

include hjq in
/-- A quotient map onto `V` with cocycle-trivial kernel has a section as a morphism of
schemes over the base. -/
theorem exists_section [IsAffine H.X.left] [IsAffine V.X.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hK : CocyclesVanish K) : ∃ σ : V.X ⟶ H.X, σ ≫ q.hom.hom = 𝟙 V.X := by
  let b := V.X.hom
  let U' : Over V.X.left := Over.mk q.hom.hom.left
  have : IsAffine U'.left := ‹IsAffine H.X.left›
  have : Flat U'.hom := ‹Flat q.hom.hom.left›
  have : Surjective U'.hom := ‹Surjective q.hom.hom.left›
  have : EffectiveEpi U'.hom := (inferInstance : EffectiveEpi q.hom.hom.left)
  let e : (Over.map b).obj U' ⟶ H.X :=
    Over.homMk (𝟙 H.X.left) ((Category.id_comp _).trans (Over.w q.hom.hom).symm)
  let F : U' ⟶ ((GroupScheme.baseChange b).obj H).X := (baseChangePointsEquiv b H U').symm e
  let q' := ((GroupScheme.baseChange b).map q).hom.hom
  let j' := ((GroupScheme.baseChange b).map j).hom.hom
  have hFq : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'), a₁ ≫ F ≫ q' = a₂ ≫ F ≫ q' := by
    intro Z a₁ a₂
    apply (baseChangePointsEquiv b V Z).injective
    rw [← Category.assoc, ← Category.assoc, baseChangePointsEquiv_comp,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_naturality,
      baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change a₁.left ≫ 𝟙 _ ≫ q.hom.hom.left = a₂.left ≫ 𝟙 _ ≫ q.hom.hom.left
    exact (Over.w a₁).trans (Over.w a₂).symm
  have hval : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'),
      ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
        k ≫ j' = (Cocycle.coboundary F).toFun a₁ a₂ := by
    intro Z a₁ a₂
    refine baseChange_exists_comp_eq b hjq _ ?_
    change ((a₁ ≫ F) * (a₂ ≫ F)⁻¹) ≫ q' = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hFq a₁ a₂,
      mul_inv_cancel]
  obtain ⟨f₂, hf₂⟩ := hK V.X U' ((Cocycle.coboundary F).lift _ hval)
  let J : U' ⟶ ((GroupScheme.baseChange b).obj H).X := f₂ ≫ j'
  have hJ : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'),
      (a₁ ≫ J) * (a₂ ≫ J)⁻¹ = (a₁ ≫ F) * (a₂ ≫ F)⁻¹ := by
    intro Z a₁ a₂
    have h := Cocycle.lift_toFun _ _ hval a₁ a₂
    rw [hf₂ a₁ a₂, MonObj.mul_comp, GrpObj.inv_comp] at h
    simp only [J, Category.assoc] at h ⊢
    exact h
  obtain ⟨s, hs, hs'⟩ := exists_section_of_forall_eq (J⁻¹ * F) fun {Z} a₁ a₂ => by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
    calc (a₁ ≫ J)⁻¹ * (a₁ ≫ F)
        = (a₁ ≫ J)⁻¹ * ((a₁ ≫ F) * (a₂ ≫ F)⁻¹) * (a₂ ≫ F) := by group
      _ = (a₁ ≫ J)⁻¹ * ((a₁ ≫ J) * (a₂ ≫ J)⁻¹) * (a₂ ≫ F) := by rw [hJ]
      _ = (a₂ ≫ J)⁻¹ * (a₂ ≫ F) := by group
  let p : ((GroupScheme.baseChange b).obj H).X.left ⟶ H.X.left := Limits.pullback.fst H.X.hom b
  have hp : p ≫ H.X.hom = ((GroupScheme.baseChange b).obj H).X.hom ≫ b :=
    Limits.pullback.condition
  refine ⟨Over.homMk (s ≫ p) ?_, ?_⟩
  · change (s ≫ p) ≫ H.X.hom = b
    rw [Category.assoc, hp, ← Category.assoc, hs', Category.id_comp]
  · have hFJ : baseChangePointsEquiv b H U' (J⁻¹ * F) ≫ q.hom.hom = e ≫ q.hom.hom := by
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MonObj.mul_comp, GrpObj.inv_comp]
      have : baseChangePointsEquiv b H U' J ≫ q.hom.hom = 1 := by
        rw [← baseChangePointsEquiv_comp, Category.assoc,
          baseChange_comp_comp_eq_one b hjq f₂, map_one]
      rw [this, inv_one, one_mul]
    apply Over.OverMorphism.ext
    change (s ≫ p) ≫ q.hom.hom.left = 𝟙 V.X.left
    rw [← cancel_epi U'.hom, ← Category.assoc, ← Category.assoc, hs, Category.comp_id]
    have h := congrArg (fun g => g.left) hFJ
    change ((J⁻¹ * F).left ≫ p) ≫ q.hom.hom.left = 𝟙 H.X.left ≫ q.hom.hom.left at h
    rw [h, Category.id_comp]
    rfl

include hjq in
/-- The induction step: cocycles of `H` vanish once those of the kernel and quotient do and the
quotient map has a section. -/
theorem cocyclesVanish_of_section (σ : V.X ⟶ H.X) (hσ : σ ≫ q.hom.hom = 𝟙 V.X)
    (hV : CocyclesVanish V) (hK : CocyclesVanish K) : CocyclesVanish H := by
  intro T _ U _ _ _ ξ
  let b := T.hom
  let q' := ((GroupScheme.baseChange b).map q).hom.hom
  obtain ⟨f₀, hf₀⟩ := hV T U (ξ.map ((GroupScheme.baseChange b).map q))
  let f₁ : U ⟶ ((GroupScheme.baseChange b).obj H).X :=
    (baseChangePointsEquiv b H U).symm (baseChangePointsEquiv b V U f₀ ≫ σ)
  have hf₁ : f₁ ≫ q' = f₀ := by
    apply (baseChangePointsEquiv b V U).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, Category.assoc, hσ,
      Category.comp_id]
  have hval : ∀ {Z : Over T.left} (a₁ a₂ : Z ⟶ U),
      ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
        k ≫ ((GroupScheme.baseChange b).map j).hom.hom = (ξ.twist f₁).toFun a₁ a₂ := by
    intro Z a₁ a₂
    refine baseChange_exists_comp_eq b hjq _ ?_
    have h : ξ.toFun a₁ a₂ ≫ q' = (a₁ ≫ f₀) * (a₂ ≫ f₀)⁻¹ := hf₀ a₁ a₂
    change ((a₁ ≫ f₁)⁻¹ * ξ.toFun a₁ a₂ * (a₂ ≫ f₁)) ≫ q' = 1
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hf₁,
      h]
    group
  exact Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift (hK T U ((ξ.twist f₁).lift _ hval)))

end Step

/-- A torsor has a section over an affine scheme once all cocycles of the group vanish. -/
theorem exists_section_of_cocyclesVanish {H : GroupScheme B} (hH : CocyclesVanish H)
    (T : Over B) [IsAffine T.left] (X : Over T.left)
    [ModObj ((GroupScheme.baseChange T.hom).obj H).X X] (hflat : Flat X.hom)
    (hsurj : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hX : IsIso (ModObj.leftSMul ((GroupScheme.baseChange T.hom).obj H).X X)) :
    ∃ s : T.left ⟶ X.left, s ≫ X.hom = 𝟙 T.left := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities @Flat := ⟨fun Y => (inferInstance : Flat (𝟙 Y))⟩
  obtain ⟨W, p, hp, hpf, hW⟩ := X.left.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
  let U : Over T.left := Over.mk (p ≫ X.hom)
  have : IsAffine U.left := hW
  have : Flat U.hom := Flat.comp p X.hom
  have : Surjective U.hom := (inferInstance : Surjective (p ≫ X.hom))
  have : EffectiveEpi U.hom := (inferInstance : EffectiveEpi (p ≫ X.hom))
  exact exists_section_of_isTrivial hX (Over.homMk p rfl : U ⟶ X) (hH T U _)

/-- Vanishing on affine tests also trivializes cocycles in the original group
on an affine base, using the identity base-change comparison. -/
theorem cocycle_isTrivial {H : GroupScheme B} (hH : CocyclesVanish H)
    [IsAffine B] {U : Over B} [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsTrivial := by
  let e := baseChangeIdIso H
  let T : Over B := Over.mk (𝟙 B)
  let : IsAffine T.left := inferInstanceAs (IsAffine B)
  obtain ⟨f, hf⟩ := hH T U (ξ.map e.inv)
  refine ⟨f ≫ e.hom.hom.hom, fun a b => ?_⟩
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
    congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have h := congrArg (fun z => z ≫ e.hom.hom.hom) (hf a b)
  change (ξ.toFun a b ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = _ at h
  simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, he,
    Category.comp_id] using h

/-- An actual fpqc torsor over an affine base has a section whenever the
arbitrary-base cocycle predicate holds for its acting group. -/
theorem exists_section_of_cocyclesVanish_at_base {H : GroupScheme B}
    [IsAffine B] (hH : CocyclesVanish H) (X : Over B) [ModObj H.X X]
    (hflat : Flat X.hom) (hsurj : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hX : IsIso (ModObj.leftSMul H.X X)) :
    ∃ s : B ⟶ X.left, s ≫ X.hom = 𝟙 B := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  let : MorphismProperty.ContainsIdentities @Flat := ⟨fun Y => (inferInstance : Flat (𝟙 Y))⟩
  obtain ⟨W, p, hp, hpf, hW⟩ := X.left.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
  let U : Over B := Over.mk (p ≫ X.hom)
  let : IsAffine U.left := hW
  let : Flat U.hom := Flat.comp p X.hom
  let : Surjective U.hom := (inferInstance : Surjective (p ≫ X.hom))
  let : EffectiveEpi U.hom := (inferInstance : EffectiveEpi (p ≫ X.hom))
  exact exists_section_of_isTrivial hX (Over.homMk p rfl : U ⟶ X)
    (cocycle_isTrivial hH _)

end Langlands.GroupScheme.RelativeUnipotent.AffineCocycle
