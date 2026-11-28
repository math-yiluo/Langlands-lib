import Langlands.Geometry.Analytic.SchemeAnalytificationEtaleSite
import Langlands.Geometry.Analytic.SchemeAnalytificationPullbacks
import Langlands.Sheaf.ImagePullbackContinuity
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Pullback

/-! # The morphism from the analytic étale site to the algebraic étale site -/

noncomputable section

universe u a b

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open SaturatedAtlasPresentation
open Langlands.Sheaf (HasImagePullbacks)

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : (separatedLocallyFiniteTypeOver K).FullSubcategory)

private abbrev algebraicEtaleUnderlyingScheme : X.obj.left.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X.obj.left ⋙ Over.forget X.obj.left

private abbrev analyticEtaleUnderlyingSpace :
    EtaleSite ((localizedAnalytification K).obj X) ⥤ LocalizedCategory.{u, u, u} (K := K) :=
  MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _

variable {X}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Every cospan in the separated algebraic étale category has an actual scheme
pullback still in the separated algebraic étale category. -/
theorem separatedAlgebraicEtale_exists_schemePullback
    {U V W : SeparatedAlgebraicEtale K X} (f : U ⟶ W) (g : V ⟶ W) :
    ∃ (P : SeparatedAlgebraicEtale K X) (p : P ⟶ U) (q : P ⟶ V),
      IsPullback p.left.hom.left q.left.hom.left f.left.hom.left g.left.hom.left := by
  let l : U.left.obj.left ⟶ W.left.obj.left := f.left.hom.left
  let r : V.left.obj.left ⟶ W.left.obj.left := g.left.hom.left
  let p := pullback.fst l r
  let q := pullback.snd l r
  let s := p ≫ U.left.obj.hom
  let : Etale r := inferInstanceAs (Etale ((separatedAlgebraicEtaleForget K X).map g).left)
  let : IsSeparated V.left.obj.hom := V.left.property.2
  let : IsSeparated (r ≫ W.left.obj.hom) := by rw [Over.w g.left.hom]; infer_instance
  let : IsSeparated r := IsSeparated.of_comp r W.left.obj.hom
  let : Etale p := Etale.etale_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback l r).flip (show Etale r from inferInstance)
  let : IsSeparated p := IsSeparated.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback l r).flip (show IsSeparated r from inferInstance)
  let : LocallyOfFiniteType U.left.obj.hom := U.left.property.1
  let : IsSeparated U.left.obj.hom := U.left.property.2
  let P₀ : (separatedLocallyFiniteTypeOver K).FullSubcategory :=
    ⟨Over.mk s, inferInstanceAs (LocallyOfFiniteType s), inferInstanceAs (IsSeparated s)⟩
  let p₀ : P₀ ⟶ U.left := ObjectProperty.homMk (Over.homMk p rfl)
  have hpq : p ≫ U.hom.hom.left = q ≫ V.hom.hom.left := by
    have h₁ : l ≫ W.hom.hom.left = U.hom.hom.left :=
      congrArg (fun k : U.left ⟶ X => k.hom.left) (MorphismProperty.Over.w f)
    have h₂ : r ≫ W.hom.hom.left = V.hom.hom.left :=
      congrArg (fun k : V.left ⟶ X => k.hom.left) (MorphismProperty.Over.w g)
    rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, pullback.condition]
  let q₀ : P₀ ⟶ V.left := ObjectProperty.homMk (Over.homMk q (by
    have hV : V.hom.hom.left ≫ X.obj.hom = V.left.obj.hom := Over.w V.hom.hom
    have hU : U.hom.hom.left ≫ X.obj.hom = U.left.obj.hom := Over.w U.hom.hom
    change q ≫ V.left.obj.hom = p ≫ U.left.obj.hom
    rw [← hV, ← hU, ← Category.assoc, ← Category.assoc, hpq]))
  let : Etale U.hom.hom.left := U.prop
  let P : SeparatedAlgebraicEtale K X := MorphismProperty.Over.mk ⊤ (p₀ ≫ U.hom)
    (inferInstanceAs (Etale (p ≫ U.hom.hom.left)))
  let fp : P ⟶ U := MorphismProperty.Over.homMk p₀ rfl
  let fq : P ⟶ V := MorphismProperty.Over.homMk q₀ (by
    apply (separatedLocallyFiniteTypeOver K).ι.map_injective
    exact Over.OverMorphism.ext hpq.symm)
  exact ⟨P, fp, fq, IsPullback.of_hasPullback l r⟩

variable (X)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem separatedAlgebraicEtaleForget_hasImagePullbacks :
    HasImagePullbacks (separatedAlgebraicEtaleForget K X) := by
  intro W U V f g
  obtain ⟨P, p, q, hpq⟩ := separatedAlgebraicEtale_exists_schemePullback K f g
  have hcomm : p ≫ f = q ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    apply (separatedLocallyFiniteTypeOver K).ι.map_injective
    exact Over.OverMorphism.ext hpq.w
  refine ⟨P, p, q, hcomm, ?_⟩
  apply IsPullback.of_map_of_faithful (F := algebraicEtaleUnderlyingScheme K X)
  exact hpq

variable (hSmall : StrongEtaleSmallIndexComparisonStatement.{u})

/-- The analytification of the actual algebraic pullback is a pullback in the
analytic étale category. -/
theorem separatedEtaleAnalytification_hasImagePullbacks :
    HasImagePullbacks (separatedEtaleAnalytification K X hSmall) := by
  intro W U V f g
  obtain ⟨P, p, q, hpq⟩ := separatedAlgebraicEtale_exists_schemePullback K f g
  have hcomm : p ≫ f = q ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    apply (separatedLocallyFiniteTypeOver K).ι.map_injective
    exact Over.OverMorphism.ext hpq.w
  refine ⟨P, p, q, hcomm, ?_⟩
  apply IsPullback.of_map_of_faithful (F := analyticEtaleUnderlyingSpace K X)
  exact localizedAnalytification_map_isPullback K hpq

/-- The topology on the separated algebraic étale category induced by covering
families on the scheme's small étale site. -/
def separatedAlgebraicEtaleTopology : GrothendieckTopology (SeparatedAlgebraicEtale K X) :=
  (separatedAlgebraicEtaleForget K X).restrictedTopology (Scheme.smallEtaleTopology X.obj.left)

private theorem topology_toPrecoverage_toGrothendieck {T : Type*} [Category T]
    (J : GrothendieckTopology T) : J.toPrecoverage.toGrothendieck = J := by
  refine le_antisymm J.toGrothendieck_toPrecoverage_le ?_
  intro U S hS
  rw [← Sieve.generate_sieve S]
  exact Precoverage.generate_mem_toGrothendieck ((J.arrows_mem_toPrecoverage_iff S).2 hS)

instance separatedAlgebraicEtaleForget_isContinuous :
    (separatedAlgebraicEtaleForget K X).IsContinuous (separatedAlgebraicEtaleTopology K X)
      (Scheme.smallEtaleTopology X.obj.left) := by
  let J := Scheme.smallEtaleTopology X.obj.left
  change (separatedAlgebraicEtaleForget K X).IsContinuous
    (J.toPrecoverage.comap (separatedAlgebraicEtaleForget K X)).toGrothendieck J
  simpa only [topology_toPrecoverage_toGrothendieck] using
    (separatedAlgebraicEtaleForget_hasImagePullbacks K X).isContinuous
      (J.toPrecoverage.comap (separatedAlgebraicEtaleForget K X)) J.toPrecoverage (fun _ _ h => h)

/-- Analytification is continuous for the separated algebraic étale topology and
the ordinary analytic étale topology. -/
instance separatedEtaleAnalytification_isContinuous :
    (separatedEtaleAnalytification K X hSmall).IsContinuous (separatedAlgebraicEtaleTopology K X)
      (etaleTopology ((localizedAnalytification K).obj X)) := by
  let J := Scheme.smallEtaleTopology X.obj.left
  let J' := etaleTopology ((localizedAnalytification K).obj X)
  have hmap : J.toPrecoverage.comap (separatedAlgebraicEtaleForget K X) ≤
      J'.toPrecoverage.comap (separatedEtaleAnalytification K X hSmall) := by
    intro U R hR
    obtain ⟨I, V, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR ⊢
    exact separatedEtaleAnalytification_cover K X hSmall V f hR
  change (separatedEtaleAnalytification K X hSmall).IsContinuous
    (J.toPrecoverage.comap (separatedAlgebraicEtaleForget K X)).toGrothendieck J'
  simpa only [topology_toPrecoverage_toGrothendieck] using
    (separatedEtaleAnalytification_hasImagePullbacks K X hSmall).isContinuous
      (J.toPrecoverage.comap (separatedAlgebraicEtaleForget K X)) J'.toPrecoverage hmap

open Opposite

variable (A : Type a) [Category.{b} A]

local notation "J" => separatedAlgebraicEtaleTopology K X
local notation "J_an" => etaleTopology (Functor.obj (localizedAnalytification K) X)
local notation "F_an" => separatedEtaleAnalytification K X hSmall

/-- Restriction of algebraic étale sheaves to the separated étale objects. -/
def restrictAlgebraicEtaleSheaf : Sheaf (Scheme.smallEtaleTopology X.obj.left) A ⥤ Sheaf J A :=
  (separatedAlgebraicEtaleForget K X).sheafPushforwardContinuous A J
    (Scheme.smallEtaleTopology X.obj.left)

/-- Direct image from the analytic étale site, given by evaluation on analytic
étale objects arising by analytification. -/
def separatedAnalyticEtaleDirectImage : Sheaf J_an A ⥤ Sheaf J A :=
  Functor.sheafPushforwardContinuous F_an A J J_an

section InverseImage

variable [HasWeakSheafify (etaleTopology ((localizedAnalytification K).obj X)) A]
  [∀ (P : (SeparatedAlgebraicEtale K X)ᵒᵖ ⥤ A),
    (separatedEtaleAnalytification K X hSmall).op.HasLeftKanExtension P]

/-- The sheaf inverse image is the left Kan extension along analytification
followed by analytic étale sheafification. -/
def separatedAnalyticEtaleInverseImage : Sheaf J A ⥤ Sheaf J_an A :=
  Functor.sheafPullbackConstruction.sheafPullback F_an A J J_an

/-- The constructed inverse image is left adjoint to analytic direct image. -/
def separatedAnalyticEtaleAdjunction :
    separatedAnalyticEtaleInverseImage K X hSmall A ⊣ separatedAnalyticEtaleDirectImage K X hSmall A :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F_an A J J_an

/-- Analytification of an algebraic étale sheaf via its separated étale objects. -/
def analyticEtaleSheaf : Sheaf (Scheme.smallEtaleTopology X.obj.left) A ⥤ Sheaf J_an A :=
  restrictAlgebraicEtaleSheaf K X A ⋙ separatedAnalyticEtaleInverseImage K X hSmall A

end InverseImage

end Langlands.Analytic.SchemeAnalytification
