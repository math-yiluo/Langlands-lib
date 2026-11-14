import Langlands.AlgebraicGeometry.Picard.LinearSystemAffineTheorem
import Langlands.AlgebraicGeometry.Picard.LinearSystemTransport
import Langlands.AlgebraicGeometry.Picard.LinearSystemGluingUniversal
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement

/-! # Assembly of the linear system over a locally noetherian base

The linear system of an invertible module on `Y` over a locally noetherian base `T` is glued from
the Grassmannian models over the affine opens of `T`. This file proves the representability part
of `ProperFlatIntegralLinearSystemStatement` and reduces its flatness clause to a statement local
on affine opens of the base (`LocalFibreFlatness`). -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemGluing

open PicardHilbertPiecesReduction (mapX mapX_comp mapX_congr mapX_fst mapX_snd dcl dcl_congr
  pb_comp_apply pb_iso_inv_hom pb_mapX_fst icl icl_eq_iff icl_tensor icl_pullback
  nonempty_iso_tensor_of_icl isInvertible_tensor isInvertible_pullback dcl_eq_icl icl_lineBundle)
open ProperFlatIntegralSheafClassTwist (lineBundleOfIsInvertible isInvertible_lineBundle)
open Modules.DerivedSections
open LinearSystemCechModule (affPt range_affPt classOf_pbLB pbLB exists_affine_universal)

/-- A morphism property stable under base change and isomorphisms passes from `l'` to the
restriction of `l' ≫ a` over the open image of an open immersion `a`. -/
lemma prop_pullback_snd_comp (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    [Q.RespectsIso] {P S' S : Scheme.{u}} (l' : P ⟶ S') (a : S' ⟶ S) [IsOpenImmersion a]
    (V : S.Opens) (hV : Set.range a = (V : Set S)) (hl' : Q l') :
    Q (pullback.snd (l' ≫ a) V.ι) := by
  let e := IsOpenImmersion.isoOfRangeEq a V.ι (by rw [Scheme.Opens.range_ι, hV])
  have he : e.hom ≫ V.ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hcomm : pullback.fst (l' ≫ a) V.ι ≫ l' ≫ e.hom = pullback.snd (l' ≫ a) V.ι ≫ 𝟙 _ := by
    rw [Category.comp_id, ← cancel_mono V.ι, Category.assoc, Category.assoc, he]
    exact pullback.condition
  have hsq : IsPullback (pullback.fst (l' ≫ a) V.ι) (pullback.snd (l' ≫ a) V.ι) (l' ≫ e.hom)
      (𝟙 _) := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
      (fun s => pullback.lift s.fst s.snd (by
        have := s.condition
        rw [Category.comp_id] at this
        rw [← he, ← this, Category.assoc, Category.assoc]))
      (fun s => pullback.lift_fst _ _ _) (fun s => pullback.lift_snd _ _ _) ?_)
    intro s μ h1 h2
    apply pullback.hom_ext
    · rw [h1, pullback.lift_fst]
    · rw [h2, pullback.lift_snd]
  exact MorphismProperty.of_isPullback hsq ((Q.cancel_right_of_respectsIso l' e.hom).mpr hl')

variable {T Y : Scheme.{u}} [IsLocallyNoetherian T] (g : Y ⟶ T) [IsProper g] [Flat g]
  [GeometricallyIntegral g] (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)

/-- **Local universal families over the affine opens of the base.** -/
theorem exists_local (V : T.affineOpens) :
    ∃ (P : Scheme.{u}) (l : P ⟶ T) (D : (pullback g l).IdealSheafData),
      IsLocallyNoetherian P ∧ IsProper (pullback.snd l V.1.ι) ∧
        IsUniversalOn g (icl M hM) V.1 l D := by
  have : IsNoetherianRing Γ(T, V.1) := IsLocallyNoetherian.component_noetherian V
  let a := affPt V
  let L : LineBundle (pullback g a) := pbLB (pullback.fst g a) (lineBundleOfIsInvertible M hM)
  obtain ⟨P, l', W', hP, hl', hU⟩ := exists_affine_universal (R := Γ(T, V.1))
    (pullback.snd g a) L
  have hL : L.classOf = Group.pullback (pullback.fst g a) (icl M hM) := classOf_pbLB _ _
  rw [hL] at hU
  have hV : a.opensRange = V.1 := TopologicalSpace.Opens.ext (by
    rw [Scheme.Hom.coe_opensRange]
    exact range_affPt V)
  have hT := hU.transport (a := a)
  rw [hV] at hT
  exact ⟨P, l' ≫ a, _, hP,
    prop_pullback_snd_comp @IsProper l' a V.1 (range_affPt V) hl', hT⟩

/-- The flatness clause, local on affine opens of the base: a universal family of the linear
system over an affine open is flat and locally of finite presentation when the fibres have no
`H¹`, and surjective when moreover they have nonzero `H⁰`. -/
def LocalFibreFlatness : Prop :=
  ∀ (T Y : Scheme.{u}) [IsLocallyNoetherian T] (g : Y ⟶ T) [IsProper g] [Flat g]
    [GeometricallyIntegral g] (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (V : T.affineOpens) (P : Scheme.{u}) [IsLocallyNoetherian P] (l : P ⟶ T)
    (W : (pullback g l).IdealSheafData),
    IsUniversalOn g (icl M hM) V.1 l W →
    (∀ t ∈ V.1, IsZero ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 1).obj
      ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
      Flat (pullback.snd l V.1.ι) ∧ LocallyOfFinitePresentation (pullback.snd l V.1.ι) ∧
        ((∀ t ∈ V.1, ¬ IsZero ((relativeCohomology (pullback.snd g (T.fromSpecResidueField t)) 0).obj
          ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
            Surjective (pullback.snd l V.1.ι))

/-- Isomorphism with a twist from a class equation. -/
lemma nonempty_iso_of_class {X Z : Scheme.{u}} (q₁ : X ⟶ Y) (q₂ : X ⟶ Z)
    (Ld : LineBundle X) (n : Group Z)
    (h : Ld.classOf = Group.pullback q₁ (icl M hM) + Group.pullback q₂ n) :
    Nonempty (Ld.obj ≅ (Scheme.Modules.pullback q₁).obj M ⊗
      (Scheme.Modules.pullback q₂).obj (Group.lineBundleRepresentative Z n).obj) := by
  let N := Group.lineBundleRepresentative Z n
  refine nonempty_iso_tensor_of_icl (isInvertible_lineBundle Ld) (isInvertible_pullback q₁ hM)
    (isInvertible_pullback q₂ (isInvertible_lineBundle N)) ?_
  rw [icl_lineBundle Ld, icl_pullback q₁ M hM, icl_pullback q₂ N.obj (isInvertible_lineBundle N),
    icl_lineBundle N, Group.classOf_lineBundleRepresentative]
  exact h

/-- A class equation from an isomorphism with a twist. -/
lemma class_of_nonempty_iso {X Z : Scheme.{u}} (q₁ : X ⟶ Y) (q₂ : X ⟶ Z)
    (Ld : LineBundle X) (N' : Z.Modules) (hN' : Scheme.Modules.IsInvertible N')
    (e : Ld.obj ≅ (Scheme.Modules.pullback q₁).obj M ⊗ (Scheme.Modules.pullback q₂).obj N') :
    Ld.classOf = Group.pullback q₁ (icl M hM) + Group.pullback q₂ (icl N' hN') := by
  have hT := isInvertible_tensor (isInvertible_pullback q₁ hM) (isInvertible_pullback q₂ hN')
  have h := (icl_eq_iff _ _ (isInvertible_lineBundle Ld) hT).2 ⟨e⟩
  rw [icl_lineBundle Ld, icl_tensor _ _ (isInvertible_pullback q₁ hM)
    (isInvertible_pullback q₂ hN'), icl_pullback q₁ M hM, icl_pullback q₂ N' hN'] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The linear system of an invertible module over a locally noetherian base**, with its
flatness clause reduced to affine opens. -/
theorem properFlatIntegralLinearSystem_of_localFibreFlatness (hH : LocalFibreFlatness.{u}) :
    ProperFlatIntegralLinearSystemStatement.{u} := by
  intro T _ Y g hprop hflat hgi M hM
  have := hprop
  have := hflat
  have := hgi
  have : LocallyOfFinitePresentation g := inferInstance
  choose P l D hPN hPprop hU using exists_local g M hM
  let A : LocalData g (icl M hM) (fun V : T.affineOpens => V.1) := ⟨P, l, D, hPN, hU⟩
  have hW : TopologicalSpace.IsOpenCover (fun V : T.affineOpens => V.1) :=
    T.isBasis_affineOpens.isOpenCover
  obtain ⟨Wd, hWd⟩ := A.exists_glued_divisor hW
  have hrel := LocalData.glued_isRelativeEffective hWd
  obtain ⟨n, hn⟩ := LocalData.glued_class hWd hrel
  let NL := Group.lineBundleRepresentative (A.glued hW) n
  refine ⟨A.glued hW, A.lG hW, ⟨Wd, hrel⟩, NL.obj, A.glued_prop hW @IsProper hPprop,
    isInvertible_lineBundle NL,
    nonempty_iso_of_class M hM _ _ (EffectiveCartierDivisor.lineBundle ⟨Wd, hrel.1⟩) n hn,
    fun T' _ t' E => ⟨?_, ?_⟩, fun T' _ t' k₁ k₂ hk₁ hk₂ h =>
      LocalData.glued_eq_of_comap_eq hWd T' t' k₁ k₂ hk₁ hk₂ h, fun h1 => ?_⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hE, n', hn'⟩ := LS.comap (g := g) (m := icl M hM) k hk ⟨hrel, n, hn⟩
    exact ⟨hE, _, isInvertible_lineBundle _,
      nonempty_iso_of_class M hM _ _ (EffectiveCartierDivisor.lineBundle ⟨_, hE.1⟩) n' hn'⟩
  · rintro ⟨hE, N', hN', ⟨e⟩⟩
    have hLS : LS g (icl M hM) t' E :=
      ⟨hE, icl N' hN', class_of_nonempty_iso M hM _ _ (EffectiveCartierDivisor.lineBundle ⟨E, hE.1⟩)
        N' hN' e⟩
    exact LocalData.glued_exists_point hWd T' t' E hLS
  · have hloc : ∀ V : T.affineOpens, Flat (pullback.snd (l V) V.1.ι) ∧
        LocallyOfFinitePresentation (pullback.snd (l V) V.1.ι) ∧
        ((∀ t ∈ V.1, ¬ IsZero ((relativeCohomology
          (pullback.snd g (T.fromSpecResidueField t)) 0).obj
            ((Scheme.Modules.pullback (pullback.fst g (T.fromSpecResidueField t))).obj M))) →
          Surjective (pullback.snd (l V) V.1.ι)) := fun V => by
      have := hPN V
      exact hH T Y g M hM V (P V) (l V) (D V) (hU V) (fun t _ => h1 t)
    exact ⟨A.glued_prop hW @Flat (fun V => (hloc V).1),
      A.glued_prop hW @LocallyOfFinitePresentation (fun V => (hloc V).2.1),
      fun h0 => A.glued_prop hW @Surjective (fun V => (hloc V).2.2 (fun t _ => h0 t))⟩

end Langlands.AlgebraicGeometry.Picard.LinearSystemGluing
