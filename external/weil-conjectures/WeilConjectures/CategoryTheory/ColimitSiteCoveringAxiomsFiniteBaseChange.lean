/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ColimitSiteCoveringPullbackStagePresentation
import WeilConjectures.CategoryTheory.FilteredColimitPreservesPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
/-- Then for every finite indexed Q-cover and every arrow into its target, any family of pullback
squares has a covering family of first projections.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms-finitebasechange)

Proof: Fix a finite indexed Q-cover f, an arrow g into its target, and
an arbitrary pullback square for each f i and g. Represent the cover using hQ.
As in finite composition, choose stage representatives of every requested f i
and match every member of the finite representing presieve to an index. Move
them and a representative of g to a common stage and enforce endpoint and arrow
equalities by eventual equality. By hcover the resulting indexed stage family
is covering. Stage HasPullbacks supplies its pullbacks along g. By hpullback
and the limiting-cone argument of filteredColimit_preservesPullback, their
cocone images are pullbacks. Each prescribed pullback square is therefore
uniquely isomorphic, compatibly with both legs, to the corresponding image
square. Lift each such isomorphism and its inverse to a further common stage,
along with its endpoints, and enforce the inverse and leg equations by eventual
equality. Only finitely many squares are involved. At that stage use the lifted
isomorphisms to transport the stage pullbacks to the lifted prescribed vertices;
these are genuine pullback squares by invariance under isomorphism. Apply
(P j).IsStableUnderFiniteBaseChange to these squares. The image of the resulting
covering family is exactly the prescribed family of first projections, so hQ
makes it a Q-cover. This argument also covers an empty index: lift only g and
the covering target, then use the empty stage base-change family. -/
theorem colimit_site_covering_axioms_FiniteBaseChange
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        Q.IsStableUnderFiniteBaseChange := by
  constructor
  intro ι _inst S X f hR Y g P' p₁ p₂ h
  obtain ⟨j₀, T₀, R₀, e₀, hR₀, himage⟩ := (hQ S (Presieve.ofArrows X f)).mp hR
  obtain ⟨j, T, A, a, B, b, D, q₁, q₂, e, ha, hsquares, hlegs⟩ :=
    colimit_site_covering_pullback_stage_presentation J F P hfinite hcover hpullback V
      hobjects harrows j₀ T₀ R₀ hR₀ e₀ f himage g p₁ p₂ h
  have hbase : Presieve.ofArrows D q₁ ∈ P j B :=
    Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
      a ha b q₁ q₂ hsquares
  exact (hQ Y (Presieve.ofArrows P' p₁)).mpr
    ⟨j, B, Presieve.ofArrows D q₁, e, hbase, hlegs⟩

end CategoryTheory
