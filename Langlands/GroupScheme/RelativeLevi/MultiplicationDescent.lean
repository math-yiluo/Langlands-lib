import Langlands.GroupScheme.RelativeLevi.Basic
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smoothness and multiplication descent for Levi subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- A target-local morphism property satisfying fppf descent can be checked on
an arbitrary étale covering family. -/
theorem property_of_etaleCover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {X S : Scheme.{u}} (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (f : X ⟶ S) (h : ∀ i, P (pullback.snd f (𝒰.f i))) : P f := by
  let p := Sigma.desc 𝒰.f
  let : Etale p := IsZariskiLocalAtSource.sigmaDesc 𝒰.map_prop
  let : Surjective p := ⟨fun s => by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq s
    refine ⟨Sigma.ι 𝒰.X i x, ?_⟩
    simp only [p, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := P) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (g := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover 𝒰.X)]
  intro i
  let e := pullbackLeftPullbackSndIso f p (Sigma.ι 𝒰.X i) ≪≫
    pullback.congrHom rfl (Sigma.ι_comp_desc 𝒰.f i)
  have he : e.hom ≫ pullback.snd f (𝒰.f i) =
      pullback.snd (pullback.snd f p) (Sigma.ι 𝒰.X i) := by
    simp [e]
    exact pullbackLeftPullbackSndIso_hom_snd f p (Sigma.ι 𝒰.X i)
  change P (pullback.snd (pullback.snd f p) (Sigma.ι 𝒰.X i))
  rw [← he, P.cancel_left_of_respectsIso]
  exact h i

/-- Smoothness of a group scheme descends along an étale covering family. -/
theorem smooth_of_etaleCover {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (G : GroupScheme S)
    (h : ∀ i, Smooth ((baseChange (𝒰.f i)).obj G).X.hom) : Smooth G.X.hom :=
  property_of_etaleCover @Smooth 𝒰 G.X.hom h

/-- The square comparing a morphism of relative schemes with its base change is
cartesian on the underlying schemes. -/
theorem isPullback_over_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback b).map f).left (pullback.fst X.hom b)
      (pullback.fst Y.hom b) f.left := by
  have houter : IsPullback
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (pullback.fst X.hom b) b (f.left ≫ Y.hom) := by
    simpa only [Over.w f, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback X.hom b).flip
  exact houter.of_right
    (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom b).flip

/-- A relative morphism which becomes an isomorphism over every member of an
étale covering family is already an isomorphism. -/
theorem isIso_of_etaleCover {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ i, IsIso ((Over.pullback (𝒰.f i)).map f)) : IsIso f := by
  have hf : IsIso f.left := by
    apply property_of_etaleCover (MorphismProperty.isomorphisms Scheme.{u})
      (𝒰.pullback₁ Y.hom) f.left
    intro i
    let := h i
    have hi : IsIso ((Over.pullback (𝒰.f i)).map f).left := inferInstance
    have hp := (isPullback_over_baseChange (𝒰.f i) f).flip
    rw [← hp.isoPullback_hom_snd] at hi
    exact (MorphismProperty.isomorphisms Scheme.{u}).cancel_left_of_respectsIso _ _ |>.mp hi
  let : IsIso ((Over.forget S).map f) := hf
  exact isIso_of_reflects_iso f (Over.forget S)

/-- Base change preserves the actual multiplication morphism, using the
canonical product comparison in the category of schemes over the base. -/
theorem subgroupMultiplication_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P) :
    Functor.LaxMonoidal.μ (Over.pullback b) L.X U.X ≫
        (Over.pullback b).map (subgroupMultiplication l r) =
      subgroupMultiplication ((baseChange b).map l) ((baseChange b).map r) := by
  simp only [subgroupMultiplication, Functor.map_mul, MonObj.comp_mul,
    Functor.map_comp, Functor.Monoidal.μ_fst_assoc, Functor.Monoidal.μ_snd_assoc]
  rfl

/-- Isomorphy of subgroup multiplication is preserved by arbitrary base change. -/
theorem subgroupMultiplication_isIso_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    [IsIso (subgroupMultiplication l r)] :
    IsIso (subgroupMultiplication ((baseChange b).map l) ((baseChange b).map r)) := by
  rw [← subgroupMultiplication_baseChange b l r]
  infer_instance

/-- Isomorphy of subgroup multiplication can be checked on an étale covering
family of the base. -/
theorem subgroupMultiplication_isIso_of_etaleCover {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    (h : ∀ i, IsIso
      (subgroupMultiplication ((baseChange (𝒰.f i)).map l)
        ((baseChange (𝒰.f i)).map r))) : IsIso (subgroupMultiplication l r) := by
  apply isIso_of_etaleCover 𝒰
  intro i
  have hi := h i
  rw [← subgroupMultiplication_baseChange (𝒰.f i) l r] at hi
  exact (MorphismProperty.isomorphisms (Over (𝒰.X i))).cancel_left_of_respectsIso _ _ |>.mp hi

/-- The actual Levi-times-radical multiplication isomorphism obtained from local
multiplication isomorphisms on an étale covering family. -/
def subgroupMultiplicationIsoOfEtaleCover {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    (h : ∀ i, IsIso
      (subgroupMultiplication ((baseChange (𝒰.f i)).map l)
        ((baseChange (𝒰.f i)).map r))) : L.X ⊗ U.X ≅ P.X := by
  letI := subgroupMultiplication_isIso_of_etaleCover 𝒰 l r h
  exact asIso (subgroupMultiplication l r)

@[simp]
theorem subgroupMultiplicationIsoOfEtaleCover_hom {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    (h : ∀ i, IsIso
      (subgroupMultiplication ((baseChange (𝒰.f i)).map l)
        ((baseChange (𝒰.f i)).map r))) :
    (subgroupMultiplicationIsoOfEtaleCover 𝒰 l r h).hom = subgroupMultiplication l r :=
  rfl

/-- Given a global relative unipotent radical, the smoothness and multiplication
conditions for a closed Levi inclusion can be checked on an étale cover. -/
theorem isRelativeLeviSubgroup_of_etaleCover {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    {L U P : GroupScheme S} (l : L ⟶ P) (r : U ⟶ P)
    (hl : IsClosedSubgroup l) (hr : IsRelativeUnipotentRadical r)
    (hSmooth : ∀ i, Smooth ((baseChange (𝒰.f i)).obj L).X.hom)
    (hMul : ∀ i, IsIso
      (subgroupMultiplication ((baseChange (𝒰.f i)).map l)
        ((baseChange (𝒰.f i)).map r))) : IsRelativeLeviSubgroup l where
  isClosedSubgroup := hl
  smooth := smooth_of_etaleCover 𝒰 L hSmooth
  exists_unipotentRadical :=
    ⟨U, r, hr, subgroupMultiplication_isIso_of_etaleCover 𝒰 l r hMul⟩

end Langlands.GroupScheme.RelativeLevi
