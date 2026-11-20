import Langlands.GroupScheme.ConjugationStabilizerBaseChange
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.GroupScheme.SubgroupFunctor.ClosedZariskiDescent

/-! # Conjugation stabilizers of finite locally free subschemes over any base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open SubgroupFunctor (coverObj coverMap)

variable {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S}

private theorem mem_schemePointRange_of_openCover (z : Z ⟶ G.X) [Mono z.left]
    {V : Over S} (𝒱 : V.left.OpenCover) (x : V ⟶ G.X)
    (h : ∀ k, coverMap 𝒱 k ≫ x ∈ schemePointRange z (coverObj 𝒱 k)) :
    x ∈ schemePointRange z V := by
  choose y hy using h
  have he (k : 𝒱.I₀) : (y k).left ≫ z.left = 𝒱.f k ≫ x.left :=
    congrArg (fun a : coverObj 𝒱 k ⟶ G.X => a.left) (hy k)
  have hc (k l : 𝒱.I₀) :
      pullback.fst (𝒱.f k) (𝒱.f l) ≫ (y k).left =
        pullback.snd (𝒱.f k) (𝒱.f l) ≫ (y l).left := by
    apply (cancel_mono z.left).mp
    simp only [Category.assoc, he, pullback.condition_assoc]
  let v := 𝒱.glueMorphisms (fun k => (y k).left) hc
  have hv (k : 𝒱.I₀) : 𝒱.f k ≫ v = (y k).left := 𝒱.ι_glueMorphisms _ hc k
  have hw : v ≫ Z.hom = V.hom := by
    apply 𝒱.hom_ext
    intro k
    rw [← Category.assoc, hv]
    exact Over.w (y k)
  refine ⟨Over.homMk v hw, Over.OverMorphism.ext ?_⟩
  change v ≫ z.left = x.left
  apply 𝒱.hom_ext
  intro k
  rw [← Category.assoc, hv, he]

/-- Conjugation stabilization of a subscheme can be checked on a cover of the test. -/
theorem conjugationStabilizer_isZariskiLocal (z : Z ⟶ G.X) [Mono z.left] :
    (conjugationStabilizer z).IsZariskiLocal := by
  intro T 𝒰 g
  constructor
  · intro hg k
    exact (conjugationStabilizer z).comp_mem (coverMap 𝒰 k) hg
  · intro hg V a x hx
    let 𝒱 := 𝒰.pullback₁ a.left
    let b (k : 𝒱.I₀) : coverObj 𝒱 k ⟶ coverObj 𝒰 k :=
      Over.homMk (pullback.snd a.left (𝒰.f k)) (by
        change pullback.snd a.left (𝒰.f k) ≫ 𝒰.f k ≫ T.hom =
          pullback.fst a.left (𝒰.f k) ≫ V.hom
        rw [← pullback.condition_assoc, Over.w a])
    have hba (k : 𝒱.I₀) : coverMap 𝒱 k ≫ a = b k ≫ coverMap 𝒰 k :=
      Over.OverMorphism.ext pullback.condition
    constructor <;> apply mem_schemePointRange_of_openCover z 𝒱 <;> intro k
    all_goals
      have hx' : coverMap 𝒱 k ≫ x ∈ schemePointRange z (coverObj 𝒱 k) := by
        obtain ⟨y, rfl⟩ := hx
        exact ⟨coverMap 𝒱 k ≫ y, Category.assoc _ _ _⟩
      have hk := hg k _ (b k) _ hx'
      rw [← Category.assoc (b k), ← hba k, Category.assoc] at hk
      simp only [MonObj.comp_mul, GrpObj.comp_inv]
    · exact hk.1
    · exact hk.2

/-- Closed conjugation stabilizers for finite flat finitely presented closed subschemes
of group schemes over arbitrary bases. -/
def FiniteSubschemeStabilizerDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (Z : Over S)
    [IsFinite Z.hom] [Flat Z.hom] [LocallyOfFinitePresentation Z.hom],
    ∀ z : Z ⟶ G.X, IsClosedImmersion z.left → (conjugationStabilizer z).IsClosedRepresentable

/-- The affine-base stabilizers glue using the local factorization condition. -/
theorem finiteSubschemeStabilizerDescent : FiniteSubschemeStabilizerDescentStatement.{u} := by
  intro S G Z hfin hflat hlfp z hz
  have : IsClosedImmersion z.left := hz
  apply (conjugationStabilizer z).isClosedRepresentable_of_openCover
    (conjugationStabilizer_isZariskiLocal z) S.affineCover
  intro k
  let b := S.affineCover.f k
  let z' := (Over.pullback b).map z
  have hz' : IsClosedImmersion z'.left := MorphismProperty.of_isPullback
    (RelativeIdentityComponent.overPullback_isPullback b z).flip hz
  have : IsFinite ((Over.pullback b).obj Z).hom :=
    MorphismProperty.baseChange_obj (P := @IsFinite) b Z hfin
  have : Flat ((Over.pullback b).obj Z).hom :=
    MorphismProperty.baseChange_obj (P := @Flat) b Z hflat
  have : LocallyOfFinitePresentation ((Over.pullback b).obj Z).hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFinitePresentation) b Z hlfp
  rw [conjugationStabilizerBaseChange b z z' (pullback.fst Z.hom b)
    (IsPullback.of_hasPullback Z.hom b) (RelativeIdentityComponent.overPullback_isPullback b z).w]
  exact closedFiniteSubschemeStabilizer _ ((baseChange b).obj G)
    ((Over.pullback b).obj Z) z' hz'

end Langlands.GroupScheme
