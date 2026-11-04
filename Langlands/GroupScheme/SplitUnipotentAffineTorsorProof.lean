import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.SplitUnipotentTorsor.VectorCocycle
import Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement
import Langlands.GroupScheme.Rational.VectorCoordinateGeometry
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # Sections of split-unipotent torsors over affine schemes

Cocycles of a split-unipotent group on affine fpqc covers of affine schemes are trivial, by
induction along the split series; a torsor therefore has a section over every affine scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

namespace SplitUnipotentAffineTorsor

variable {R : CommRingCat.{u}}

/-- Every cocycle of the base change of `H` to an affine scheme over the base, on an affine
flat surjective cover of that scheme, is trivial. -/
def CocyclesVanish (H : GroupScheme (Spec R)) : Prop :=
  ∀ (T : Over (Spec R)) [IsAffine T.left] (U : Over T.left) [IsAffine U.left] [Flat U.hom]
    [Surjective U.hom] (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj H) U), ξ.IsTrivial

section Kernel

variable {B : Scheme.{u}} {K H V : GroupScheme B} {j : K ⟶ H} {q : H ⟶ V}

theorem comp_comp_eq_one (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {Z : Over B} (k : Z ⟶ K.X) : k ≫ j.hom.hom ≫ q.hom.hom = 1 := by
  have hj : j.hom.hom ∈ (SubgroupFunctor.range j).carrier K.X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  rw [← hjq] at hj
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hj
  have h1 : (y ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 := (kernelPointsEquiv q K.X y).property
  rw [← hy, h1, MonObj.comp_one]

theorem exists_comp_eq_of_comp_eq_one
    (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {Z : Over B} (x : Z ⟶ H.X) (hx : x ≫ q.hom.hom = 1) : ∃ k : Z ⟶ K.X, k ≫ j.hom.hom = x := by
  have hmem : x ∈ (SubgroupFunctor.range (kernelι q)).carrier Z :=
    SubgroupFunctor.mem_range.mpr ⟨(kernelPointsEquiv q Z).symm ⟨x, hx⟩,
      congrArg Subtype.val ((kernelPointsEquiv q Z).apply_symm_apply ⟨x, hx⟩)⟩
  rw [hjq] at hmem
  exact SubgroupFunctor.mem_range.mp hmem

variable {S' : Scheme.{u}} (b : S' ⟶ B)

theorem baseChange_comp_comp_eq_one
    (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {Z : Over S'} (k : Z ⟶ ((GroupScheme.baseChange b).obj K).X) :
    k ≫ ((GroupScheme.baseChange b).map j).hom.hom ≫
      ((GroupScheme.baseChange b).map q).hom.hom = 1 := by
  apply (baseChangePointsEquiv b V Z).injective
  rw [← Category.assoc, baseChangePointsEquiv_comp, baseChangePointsEquiv_comp, map_one,
    Category.assoc, comp_comp_eq_one hjq]

theorem baseChange_exists_comp_eq
    (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {Z : Over S'} (x : Z ⟶ ((GroupScheme.baseChange b).obj H).X)
    (hx : x ≫ ((GroupScheme.baseChange b).map q).hom.hom = 1) :
    ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
      k ≫ ((GroupScheme.baseChange b).map j).hom.hom = x := by
  have hx' : baseChangePointsEquiv b H Z x ≫ q.hom.hom = 1 := by
    rw [← baseChangePointsEquiv_comp, hx, map_one]
  obtain ⟨k, hk⟩ := exists_comp_eq_of_comp_eq_one hjq _ hx'
  refine ⟨(baseChangePointsEquiv b K Z).symm k, ?_⟩
  apply (baseChangePointsEquiv b H Z).injective
  rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, hk]

instance baseChange_mono [Mono j.hom.hom] : Mono ((GroupScheme.baseChange b).map j).hom.hom :=
  Functor.map_mono (Over.pullback b) j.hom.hom

end Kernel

/-- For the trivial group every cocycle is trivial. -/
theorem cocyclesVanish_of_range_id_eq_bot {H : GroupScheme (Spec R)}
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

variable {K H V : GroupScheme (Spec R)} (j : K ⟶ H) (q : H ⟶ V) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

include hjq in
/-- A quotient map onto `V` with split-unipotent-type kernel has a section as a morphism of
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

variable (hvec : ∀ V : GroupScheme (Spec R), IsVectorGroupOfDimension V 1 → CocyclesVanish V)

include hvec in
/-- Cocycles of an affine group with a split series vanish. -/
theorem cocyclesVanish_of_hasSplitSeries :
    ∀ (n : ℕ) (H : GroupScheme (Spec R)), HasSplitSeries n H → IsAffineHom H.X.hom →
      CocyclesVanish H
  | 0, _, h, _ => cocyclesVanish_of_range_id_eq_bot h
  | n + 1, H, ⟨K, V, j, q, hj, _, _, _, ⟨_, _, _, hjq⟩, hV, hK⟩, _ => by
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : IsAffineHom K.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hKv := cocyclesVanish_of_hasSplitSeries n K hK this
    have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    have : IsAffineHom V.X.hom := hV.isAffineHom_overRing
    have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
    obtain ⟨σ, hσ⟩ := exists_section j q hjq hKv
    exact cocyclesVanish_of_section j q hjq σ hσ (hvec V hV) hKv

/-- A torsor has a section over an affine scheme once all cocycles of the group vanish. -/
theorem exists_section_of_cocyclesVanish {H : GroupScheme (Spec R)} (hH : CocyclesVanish H)
    (T : Over (Spec R)) [IsAffine T.left] (X : Over T.left)
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

end SplitUnipotentAffineTorsor

open SplitUnipotentAffineTorsor in
/-- Sections of split-unipotent torsors over affine schemes, given the vanishing of cocycles of
one-dimensional vector groups. -/
theorem splitUnipotentAffineTorsorStatement_of_vector
    (hvec : ∀ {R : CommRingCat.{u}} (V : GroupScheme (Spec R)), IsVectorGroupOfDimension V 1 →
      CocyclesVanish V) :
    SplitUnipotentAffineTorsorStatement.{u} := by
  intro k _ H _ _ ⟨n, hn⟩ T _ X _ hflat hsurj hqc hX
  exact exists_section_of_cocyclesVanish
    (cocyclesVanish_of_hasSplitSeries (fun V hV => hvec V hV) n H hn inferInstance)
    T X hflat hsurj hqc hX

/-- Every fpqc torsor under the base change of a smooth affine split-unipotent group over a
field has a section over every affine scheme over that field. -/
theorem splitUnipotentAffineTorsorStatement : SplitUnipotentAffineTorsorStatement.{u} :=
  splitUnipotentAffineTorsorStatement_of_vector fun _ hV T _ U _ _ _ ξ =>
    Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV T U ξ

end Langlands.GroupScheme
