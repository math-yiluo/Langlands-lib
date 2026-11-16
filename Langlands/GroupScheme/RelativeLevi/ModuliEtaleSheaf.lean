import Langlands.GroupScheme.RelativeLevi.ModuliCoverDescent
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # The etale sheaf of actual relative Levi images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P U : GroupScheme S}
    (i : P ⟶ G) (r : U ⟶ P) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i)
    (hU : ∀ {B : Scheme.{u}} (b : B ⟶ S),
      IsRelativeUnipotentRadical ((baseChange b).map r))
    (hstable : RestrictionStable P)

include i r hG hi hU

/-- Actual Levi images have unique gluing on every etale parameter cover. -/
theorem moduliFunctor_isSheafFor_etaleCover (T : Over S)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T.left) :
    Presieve.IsSheafFor (moduliFunctorOfStability hstable)
      (etaleCoverOver T 𝒰).presieve₀ := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  have hF : IsMatchingLevi 𝒰 q := by
    intro j k A a b hab
    exact congrArg Subtype.val (hq j k A a b hab)
  let H : LeviImage ((baseChange T.hom).obj P) :=
    ⟨matchingLeviSubgroup 𝒰 q,
      isLeviImage_matchingLeviSubgroup 𝒰 q i r hG hi hU hF⟩
  have hH : ∀ j, (moduliFunctorOfStability hstable).map
      ((etaleCoverOver T 𝒰).f j).op H = q j := by
    intro j
    change H.restrict hstable ((etaleCoverOver T 𝒰).f j) = q j
    apply LeviImage.ext
    change restrictImage ((etaleCoverOver T 𝒰).f j)
      (matchingLeviSubgroup 𝒰 q) = (q j).val
    exact restrictImage_matchingLeviSubgroup 𝒰 q hF j
  refine ⟨H, hH, fun H' hH' => ?_⟩
  apply LeviImage.eq_of_restrictImage_etaleCover 𝒰 H' H
  intro j
  exact (congrArg Subtype.val (hH' j)).trans (congrArg Subtype.val (hH j)).symm

/-- The presheaf of actual Levi images is a sheaf on the big etale slice. -/
theorem moduliFunctor_isSheaf_etale :
    Presieve.IsSheaf (Scheme.etaleTopology.over S)
      (moduliFunctorOfStability hstable) := by
  let F := moduliFunctorOfStability hstable
  have hF := moduliFunctor_isSheafFor_etaleCover i r hG hi hU hstable
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  have hle : (etaleCoverOver T 𝒰).presieve₀ ≤ R := by
    rintro _ _ ⟨j⟩
    exact (Sieve.overEquiv_iff R (𝒰.f j)).mp (h𝒰 _ _ ⟨j⟩)
  apply Presieve.isSheafFor_subsieve_aux F
    ((Sieve.generate_le_iff (etaleCoverOver T 𝒰).presieve₀ R).mpr hle)
    ((Presieve.isSheafFor_iff_generate (etaleCoverOver T 𝒰).presieve₀).mp (hF T 𝒰))
  intro V g _ x t₁ t₂ ht₁ ht₂
  apply (hF V (𝒰.pullback₁ g.left)).isSeparatedFor.ext
  rintro _ _ ⟨j⟩
  have hm : (Sieve.generate (etaleCoverOver T 𝒰).presieve₀).pullback g
      ((etaleCoverOver V (𝒰.pullback₁ g.left)).f j) := by
    let a : (etaleCoverOver V (𝒰.pullback₁ g.left)).X j ⟶
        (etaleCoverOver T 𝒰).X j :=
      Over.homMk (𝒰.pullbackHom g.left j) (by
        dsimp [etaleCoverOver]
        rw [← Category.assoc, 𝒰.pullbackHom_map, Category.assoc, Over.w g])
    refine ⟨_, a, (etaleCoverOver T 𝒰).f j, ⟨j⟩, ?_⟩
    ext
    exact 𝒰.pullbackHom_map g.left j
  exact (ht₁ _ hm).trans (ht₂ _ hm).symm

/-- The big etale sheaf of actual relative Levi images. -/
def moduliEtaleSheaf : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  ⟨moduliFunctorOfStability hstable,
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (moduliFunctor_isSheaf_etale i r hG hi hU hstable)⟩

/-- The actual-image presheaf satisfies descent along every surjective etale
parameter map, without an affine or quasi-compact restriction. -/
theorem moduliFunctor_isSheafFor_etale {M T : Over S} (a : M ⟶ T)
    [Etale a.left] [Surjective a.left] :
    Presieve.IsSheafFor (moduliFunctorOfStability hstable) (.singleton a) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply moduliFunctor_isSheaf_etale i r hG hi hU hstable
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  change Sieve.generate (Presieve.ofArrows
    (fun _ : PUnit.{1} => M.left) (fun _ => a.left)) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff @Etale a.left).mpr
      ⟨a.left.surjective, inferInstance⟩)

/-- The actual-image presheaf is also a sheaf on the big Zariski slice. -/
theorem moduliFunctor_isSheaf_zariski :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (moduliFunctorOfStability hstable) := by
  have hle : Scheme.zariskiTopology.over S ≤ Scheme.etaleTopology.over S := by
    intro T R hR
    exact Scheme.zariskiTopology_le_etaleTopology T.left hR
  exact Presheaf.IsSheaf.of_le hle
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (moduliFunctor_isSheaf_etale i r hG hi hU hstable))

end Langlands.GroupScheme.RelativeLevi
