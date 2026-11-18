import Langlands.GroupScheme.RelativeUnipotent.DisjointFreeBundle
import Langlands.AlgebraicGeometry.Modules.FlatSectionDescent

/-! # Sections on an actual disjoint scheme open cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.DisjointCoverSections

private lemma squarePullbackIso_of_eq {X Y Z : Scheme.{u}} (p : Z ⟶ X)
    (a b : Y ⟶ Z) (he : a = b) (hs : a ≫ p = b ≫ p) (M : X.Modules) :
    squarePullbackIso p a b p hs M =
      (Scheme.Modules.pullbackCongr he).app ((Scheme.Modules.pullback p).obj M) := by
  subst b
  ext1
  simp [squarePullbackIso, Scheme.Modules.pullbackCongr]

variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})
  (h : DisjointCoverGluing.IsDisjoint 𝒰)

include h

/-- On a disjoint cover, every family of module maps is compatible. -/
lemma homFamily_compatible (M N : X.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj M ⟶
      (Scheme.Modules.pullback (𝒰.f i)).obj N) (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).map (φ i) ≫
        (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition N).hom =
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom ≫
          (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).map (φ j) := by
  by_cases hij : i = j
  · subst j
    have he : pullback.fst (𝒰.f i) (𝒰.f i) =
        pullback.snd (𝒰.f i) (𝒰.f i) := fst_eq_snd_of_mono_eq (𝒰.f i)
    rw [squarePullbackIso_of_eq (𝒰.f i) _ _ he,
      squarePullbackIso_of_eq (𝒰.f i) _ _ he]
    exact (Scheme.Modules.pullbackCongr he).hom.naturality (φ i)
  · have := h i j hij
    exact DisjointCoverGluing.modules_hom_ext _ _

/-- Actual module maps glue uniquely with arbitrary prescribed component maps. -/
lemma existsUnique_hom (M N : X.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj M ⟶
      (Scheme.Modules.pullback (𝒰.f i)).obj N) :
    ∃! f : M ⟶ N, ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map f = φ i :=
  OpenCoverHomGluing.openCoverHomGluing X 𝒰 M N φ (homFamily_compatible 𝒰 h M N φ)

/-- Component pullbacks jointly detect equality of actual module maps. -/
lemma hom_ext {M N : X.Modules} (f g : M ⟶ N)
    (he : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map f =
      (Scheme.Modules.pullback (𝒰.f i)).map g) : f = g := by
  obtain ⟨a, -, ha⟩ := existsUnique_hom 𝒰 h M N
    (fun i => (Scheme.Modules.pullback (𝒰.f i)).map g)
  exact (ha f he).trans (ha g (fun _ => rfl)).symm

omit h in
/-- The actual pullback of sections, component by component. -/
def restriction (M : X.Modules) :
    GlobalSections M →+ ∀ i, GlobalSections ((Scheme.Modules.pullback (𝒰.f i)).obj M) where
  toFun s i := pullbackSection (𝒰.f i) M s
  map_zero' := by
    funext i
    simpa only [Pi.zero_apply,
      Langlands.AlgebraicGeometry.Modules.pullbackSectionAddHom_apply] using
      map_zero (Langlands.AlgebraicGeometry.Modules.pullbackSectionAddHom (𝒰.f i) M)
  map_add' s t := by
    funext i
    simpa only [Pi.add_apply,
      Langlands.AlgebraicGeometry.Modules.pullbackSectionAddHom_apply] using
      map_add (Langlands.AlgebraicGeometry.Modules.pullbackSectionAddHom (𝒰.f i) M) s t

/-- Component sections determine a global section, even for non-quasicoherent modules. -/
lemma restriction_injective (M : X.Modules) : Function.Injective (restriction 𝒰 M) := by
  intro s t he
  apply sectionHom_injective
  apply hom_ext 𝒰 h
  intro i
  have H := congrArg (sectionHom ((Scheme.Modules.pullback (𝒰.f i)).obj M))
    (congrFun he i)
  simpa only [restriction, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sectionHom_pullbackSection, pullbackSectionHom, cancel_epi] using H

/-- Arbitrary actual component sections glue to a global section. -/
lemma restriction_surjective (M : X.Modules) : Function.Surjective (restriction 𝒰 M) := by
  intro s
  obtain ⟨f, hf, -⟩ := existsUnique_hom 𝒰 h (structureModule X) M
    (fun i => (pullbackUnitIso (𝒰.f i)).hom ≫
      sectionHom ((Scheme.Modules.pullback (𝒰.f i)).obj M) (s i))
  let t := (sectionHomEquiv M).symm f
  have ht : sectionHom M t = f := (sectionHomEquiv M).apply_symm_apply f
  refine ⟨t, funext (fun i => ?_)⟩
  apply sectionHom_injective
  change sectionHom _ (pullbackSection (𝒰.f i) M t) = _
  rw [sectionHom_pullbackSection, pullbackSectionHom, ht, hf]
  simp

/-- Sections of a module on a disjoint cover are the product of its actual
component-pullback sections. -/
def equiv (M : X.Modules) :
    GlobalSections M ≃+ ∀ i, GlobalSections ((Scheme.Modules.pullback (𝒰.f i)).obj M) :=
  AddEquiv.ofBijective (restriction 𝒰 M)
    ⟨restriction_injective 𝒰 h M, restriction_surjective 𝒰 h M⟩

@[simp]
lemma equiv_apply (M : X.Modules) (s : GlobalSections M) (i : 𝒰.I₀) :
    equiv 𝒰 h M s i = pullbackSection (𝒰.f i) M s := rfl

end Langlands.GroupScheme.RelativeUnipotent.DisjointCoverSections
