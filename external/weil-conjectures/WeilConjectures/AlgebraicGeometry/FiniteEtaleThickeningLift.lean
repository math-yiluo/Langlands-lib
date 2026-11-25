/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.FiniteThickeningCartesian
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A finite étale cover lifts across a finite order thickening which is a universal
homeomorphism, with a cartesian comparison map.
Source: Stacks Project, Tags 039R and 09ZW(8), as used in Tag 0GS2.
(blueprint: lem-weil-pbc-finite-etale-thickening-lift).

Proof: essential surjectivity of étale base change gives an étale cover upstairs and
an isomorphism of its pullback with the given cover. Use the inverse isomorphism followed
by the first projection for the comparison map. The square is a pullback because it is
isomorphic to the chosen pullback square. The second projection is finite, since its
composite with the isomorphism is the given finite morphism. Finiteness then lifts across
the finite order thickening by Tag 09ZW(8). -/
theorem exists_finiteEtale_thickening_lift {S T : Scheme.{u}} (i : S ⟶ T)
    (hi : IsFiniteOrderThickening i) [IsUniversalHomeomorphism i]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ S) :
    ∃ W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ T,
      ∃ g : V.left ⟶ W.left, IsPullback V.hom g i W.hom := by
  classical
  let V' : S.Etale := MorphismProperty.Over.mk ⊤ V.hom V.prop.2
  obtain ⟨W, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage i.Etale V'
  let e' := (MorphismProperty.Over.forget @Etale ⊤ S ⋙ Over.forget S).mapIso e
  have he : e'.hom ≫ V.hom = pullback.snd W.hom i := e.hom.w
  have hf : IsFinite (pullback.snd W.hom i) := by
    rw [← he]
    have : IsFinite V.hom := V.prop.1
    infer_instance
  have hW : IsFinite W.hom := (isFinite_iff_of_finiteOrderThickening i W.hom hi).mp hf
  refine ⟨MorphismProperty.Over.mk ⊤ W.hom ⟨hW, W.prop⟩,
    e'.inv ≫ pullback.fst W.hom i, ?_⟩
  have heinv : e'.inv ≫ pullback.snd W.hom i = V.hom := by
    rw [← he]
    simp
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback (i := e'.symm) (f := W.hom) (g := i)
  · constructor
    rw [Category.assoc, pullback.condition, ← Category.assoc, heinv]
  · rfl
  · exact heinv

end AlgebraicGeometry
