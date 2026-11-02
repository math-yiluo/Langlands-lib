import Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackStatement
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf
import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Langlands.CategoryTheory.Sites.StackComposite
import Langlands.AlgebraicGeometry.Picard.LineBundleStackBase
import Langlands.AlgebraicGeometry.Picard.RelativeStack

/-! # Full fpqc stack descent for actual line bundles: proof -/

universe w t u

open CategoryTheory Opposite Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.OverFppfSheaf

set_option backward.isDefEq.respectTransparency.types false in
/-- **Site reduction for the fpqc topology.** A presheaf of types on `Over S` is an fpqc sheaf
as soon as it is a Zariski sheaf and satisfies the singleton sheaf condition along every lift to
`Over S` of a flat surjective morphism of affine schemes. -/
theorem isSheaf_fpqcTopology_over {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ Type w)
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.over S) G)
    (haff : ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ s : Spec R ⟶ S, Presieve.IsSheafFor G
        (.singleton (Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s))) :
    Presieve.IsSheaf (Scheme.fpqcTopology.over S) G := by
  refine isSheaf_over_of_isSheaf_ext G _ ?_
  rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
  refine ⟨isSheaf_ext_of_isSheaf_over G _ hzar, fun {R R'} φ hf hs ↦ ?_⟩
  have : Flat (Spec.map φ) := hf
  have : Surjective (Spec.map φ) := hs
  have : IsRegularEpi (Spec.map φ) := isRegularEpi_of_flat_of_surjective_of_isAffine _
  exact isSheafFor_singleton_ext G _
    (.singleton_of_isRepresentable_of_effectiveEpi _ _) (haff φ hf hs)

namespace PicardGroupoid

/-- Morphism descent for the line-bundle pseudofunctor along open covers. -/
lemma isPrestackFor_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) :
    pseudofunctor.{u}.IsPrestackFor (Presieve.ofArrows 𝒰.X 𝒰.f) :=
  moduleRealization.isPrestackFor_openCover 𝒰

/-- Effective descent for the line-bundle pseudofunctor along open covers. -/
lemma essSurj_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) :
    (pseudofunctor.{u}.toDescentData 𝒰.f).EssSurj :=
  moduleRealization.essSurj_openCover 𝒰

/-- Morphism descent for the line-bundle pseudofunctor along a quasi-compact faithfully flat
morphism. -/
lemma isPrestackFor_singleton {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [Flat p]
    [Surjective p] : pseudofunctor.{u}.IsPrestackFor (Presieve.singleton p) :=
  moduleRealization.isPrestackFor_singleton p

/-- Effective descent for the line-bundle pseudofunctor along an affine faithfully flat
morphism with affine target. -/
lemma essSurj_singleton {X Y : Scheme.{u}} (p : X ⟶ Y) [IsAffineHom p] [Flat p]
    [Surjective p] [IsAffine Y] :
    (pseudofunctor.{u}.toDescentData (fun _ : Unit ↦ p)).EssSurj :=
  moduleRealization.essSurj_singleton p

/-- The line-bundle pseudofunctor is a prestack for the Zariski topology. -/
instance isPrestack_zariski : pseudofunctor.{u}.IsPrestack Scheme.zariskiTopology :=
  Langlands.StackComposite.isPrestack_of_small.{u} _ fun _ E ↦ isPrestackFor_openCover E

/-- The line-bundle pseudofunctor is a prestack for the fpqc topology. -/
instance isPrestack_fpqc : pseudofunctor.{u}.IsPrestack Scheme.fpqcTopology where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    refine isSheaf_fpqcTopology_over _ ?_ ?_
    · exact (isSheaf_iff_isSheaf_of_type _ _).1
        (Pseudofunctor.IsPrestack.isSheaf Scheme.zariskiTopology M N)
    · intro R R' φ hf hs s
      have : Flat (Spec.map φ) := hf
      have : Surjective (Spec.map φ) := hs
      rw [Presieve.isSheafFor_iff_generate]
      apply Pseudofunctor.IsPrestackFor.isSheafFor'
      rw [Sieve.overEquiv_generate, Pseudofunctor.IsPrestackFor_generate_iff,
        ← Sieve.arrows_generate_map_eq_functorPushforward,
        Pseudofunctor.IsPrestackFor_generate_iff, Presieve.map_singleton]
      exact isPrestackFor_singleton (Spec.map φ)

/-- Effective descent along a covering family whose descent functor is essentially
surjective. -/
lemma isStackFor_of_essSurj {S : Scheme.{u}} {ι : Type t} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows X f ∈ Scheme.fpqcTopology S)
    [(pseudofunctor.{u}.toDescentData f).EssSurj] :
    pseudofunctor.{u}.IsStackFor (Presieve.ofArrows X f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  have h := pseudofunctor.{u}.fullyFaithfulToDescentData (J := Scheme.fpqcTopology) f hf
  have := h.full
  have := h.faithful
  exact { }

/-- Over an affine open of the base, an fpqc covering family is refined by a family whose
descent functor is essentially surjective. -/
lemma exists_refinement_affine {S : Scheme.{u}} (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Flat) S)
    [QuasiCompactCover 𝒰.toPreZeroHypercover] {A : Scheme.{u}} [IsAffine A] (r : A ⟶ S) :
    ∃ (κ : Type u) (V : κ → Scheme.{u}) (c : ∀ k, V k ⟶ A),
      Sieve.ofArrows V c ∈ Scheme.fpqcTopology A ∧
      (pseudofunctor.{u}.toDescentData c).EssSurj ∧
      ∀ k, ∃ (i : 𝒰.I₀) (h : V k ⟶ 𝒰.X i), h ≫ 𝒰.f i = c k ≫ r := by
  let 𝒰a := 𝒰.pullback₂ r
  have : QuasiCompactCover 𝒰a.toPreZeroHypercover := by
    show QuasiCompactCover (𝒰.toPreZeroHypercover.pullback₂ r)
    infer_instance
  obtain ⟨𝒱, φ, hfin, -⟩ := QuasiCompactCover.exists_hom.{u} 𝒰a
  let g : 𝒱.I₀ → Scheme.{u} := fun j ↦ Spec (𝒱.X j)
  let w : ∐ g ⟶ A := Sigma.desc 𝒱.f
  have : Flat w := IsZariskiLocalAtSource.sigmaDesc 𝒱.map_prop
  have : Surjective w := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := 𝒱.covers x
    exact ⟨Sigma.ι g (𝒱.idx x) y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]; exact hy⟩⟩
  have : IsAffineHom w := inferInstance
  have hess := Langlands.StackComposite.essSurj_toDescentData_comp pseudofunctor.{u}
    Scheme.fpqcTopology (fun _ : Unit ↦ w) (fun _ ↦ (sigmaOpenCover g).f)
    (fun _ ↦ Scheme.zariskiTopology_le_fpqcTopology _
      (Scheme.Cover.mem_grothendieckTopology (sigmaOpenCover g)))
    (essSurj_singleton w) (fun _ ↦ essSurj_openCover _)
  have : Finite 𝒱.I₀ := hfin
  refine ⟨_, _, _, ?_, hess, ?_⟩
  · refine Scheme.fpqcTopology.superset_covering ?_ (Scheme.Cover.mem_propQCTopology 𝒱.cover)
    refine (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun j ↦ ?_)
    have : 𝒱.cover.f j = (sigmaOpenCover g).f j ≫ w := by simp [w]
    rw [this]
    exact Sieve.ofArrows_mk _ (fun x : Σ (_ : Unit), 𝒱.I₀ ↦ (sigmaOpenCover g).f x.2 ≫ w) ⟨(), j⟩
  · rintro ⟨⟨⟩, j⟩
    refine ⟨φ.s₀ j, φ.h₀ j ≫ pullback.fst _ _, ?_⟩
    have hw : φ.h₀ j ≫ pullback.snd (𝒰.f (φ.s₀ j)) r = 𝒱.f j := φ.w₀ j
    simp [w, pullback.condition, reassoc_of% hw]

/-- Effective descent for the line-bundle pseudofunctor along every fpqc covering presieve. -/
lemma isStackFor_fpqc {S : Scheme.{u}} {R : Presieve S} (hR : R ∈ Scheme.fpqcPrecoverage S) :
    pseudofunctor.{u}.IsStackFor R := by
  obtain ⟨𝒰, h𝒰, rfl⟩ := Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover.1 hR
  let 𝒰₀ := 𝒰.qculift
  choose κ V c hc hess hfac using fun a ↦ exists_refinement_affine 𝒰₀ (S.affineCover.f a)
  have hd := Langlands.StackComposite.essSurj_toDescentData_comp pseudofunctor.{u}
    Scheme.fpqcTopology S.affineCover.f c hc (essSurj_openCover _) hess
  have hmem : Sieve.ofArrows _ (fun x : Σ a, κ a ↦ c x.1 x.2 ≫ S.affineCover.f x.1) ∈
      Scheme.fpqcTopology S := by
    refine Scheme.fpqcTopology.transitive (Scheme.zariskiTopology_le_fpqcTopology _
      (Scheme.Cover.mem_grothendieckTopology S.affineCover)) _ ?_
    rintro Y f ⟨Z, g, _, ⟨a⟩, rfl⟩
    rw [Sieve.pullback_comp]
    refine Scheme.fpqcTopology.pullback_stable g
      (Scheme.fpqcTopology.superset_covering ?_ (hc a))
    refine (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun k ↦ ?_)
    exact Sieve.ofArrows_mk _ (fun x : Σ a, κ a ↦ c x.1 x.2 ≫ S.affineCover.f x.1) ⟨a, k⟩
  have hstack := isStackFor_of_essSurj _ hmem
  rw [← Pseudofunctor.IsStackFor_generate_iff] at hstack ⊢
  refine hstack.of_le' _ hmem ?_
  refine (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun x ↦ ?_)
  obtain ⟨i, h, hh⟩ := hfac x.1 x.2
  refine ⟨_, h, 𝒰₀.f i, ?_, hh⟩
  rcases i with i | i
  · exact Presieve.ofArrows.mk _
  · exact Presieve.ofArrows.mk _

/-- The line-bundle pseudofunctor is a stack for the fpqc topology. -/
instance isStack_fpqc : pseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
  Pseudofunctor.IsStack.of_precoverage fun _ _ hR ↦ isStackFor_fpqc hR

end PicardGroupoid

/-- **Full fpqc stack descent for actual line bundles.** The line-bundle pseudofunctor is a
stack for the fpqc topology, and so is every relative line-bundle pseudofunctor on the induced
topology of the slice category. -/
theorem lineBundleFpqcStack : LineBundleFpqcStackStatement.{u} :=
  ⟨PicardGroupoid.isStack_fpqc, fun _ _ f ↦ PicardGroupoid.relative_isStack_fpqc f⟩

end Langlands.AlgebraicGeometry.Picard
