import Langlands.GroupScheme.RelativeLevi.AffineFaceRestriction
import Langlands.GroupScheme.RelativeLevi.FiniteFaceCoverGeometry
import Langlands.GroupScheme.RelativeLevi.ParabolicRadicalBaseChange
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # All-test matching of the original face terms on chart overlaps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Over an empty base every actual subgroup functor has the same all-test
membership condition. -/
theorem SubgroupFunctor.eq_of_isEmpty_base {S : Scheme.{u}} [IsEmpty S]
    {G : GroupScheme S} (F F' : SubgroupFunctor G) : F = F' := by
  ext T x
  let : IsEmpty T.left := Function.isEmpty T.hom
  have hx : x = 1 := by
    apply Over.OverMorphism.ext
    exact (isInitialOfIsEmpty (X := T.left)).hom_ext _ _
  rw [hx]
  exact ⟨fun _ => (F'.carrier T).one_mem, fun _ => (F.carrier T).one_mem⟩

namespace Descent

/-- Original-map range recovery is coherent under another actual pullback,
after comparing both targets to the direct original ambient pullback. -/
theorem range_pullbackComparison_tower
    {S T U V : Scheme.{u}} (p : T ⟶ S) (b : U ⟶ T) (a : U ⟶ S)
    (hb : b ≫ p = a) {G : GroupScheme S} {K : GroupScheme T}
    (i : K ⟶ (baseChange p).obj G) (c : V ⟶ U) :
    SubgroupFunctor.range
      ((baseChange c).map
          ((baseChange b).map i ≫ (pullbackComparison p b a hb G).hom) ≫
        (pullbackComparison a c (c ≫ a) rfl G).hom) =
    SubgroupFunctor.range
      ((baseChange (c ≫ b)).map i ≫
        (pullbackComparison p (c ≫ b) (c ≫ a)
          ((Category.assoc _ _ _).trans (congrArg (fun f => c ≫ f) hb)) G).hom) := by
  have he :
      (baseChange c).map
          ((baseChange b).map i ≫ (pullbackComparison p b a hb G).hom) ≫
        (pullbackComparison a c (c ≫ a) rfl G).hom =
      (pullbackComparison b c (c ≫ b) rfl K).hom ≫
        ((baseChange (c ≫ b)).map i ≫
          (pullbackComparison p (c ≫ b) (c ≫ a)
            ((Category.assoc _ _ _).trans (congrArg (fun f => c ≫ f) hb)) G).hom) := by
    rw [Functor.map_comp, Category.assoc,
      Dynamic.pullbackComparison_tower p b a hb c (c ≫ b) (c ≫ a) rfl
        ((Category.assoc _ _ _).trans (congrArg (fun f => c ≫ f) hb)) rfl,
      ← Category.assoc, pullbackComparison_naturality, Category.assoc]
  rw [he, SubgroupFunctor.range_iso_comp]

end Descent

namespace RelativeLevi

variable {S : Scheme.{u}} {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}

local instance overlapAmbientAffine {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace AffineParabolicFaceChart

variable {s t : S} (C : AffineParabolicFaceChart p s) (D : AffineParabolicFaceChart p t)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

include hG hp hr in
/-- On any common affine parameter scheme, the two original terms agree
in the actual direct pullback of the original ambient group. -/
theorem range_affineRestriction_eq (A : CommRingCat.{u})
    (b : Spec A ⟶ Spec C.ring) (c : Spec A ⟶ Spec D.ring) (a : Spec A ⟶ S)
    (hb : b ≫ C.projection = a) (hc : c ≫ D.projection = a) (d : ℕ) :
    SubgroupFunctor.range
      ((baseChange b).map (C.termInclusion d) ≫
        (Descent.pullbackComparison C.projection b a hb G).hom) =
    SubgroupFunctor.range
      ((baseChange c).map (D.termInclusion d) ≫
        (Descent.pullbackComparison D.projection c a hc G).hom) := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let : Subsingleton A := hA
    let : IsEmpty (Spec A) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    exact SubgroupFunctor.eq_of_isEmpty_base _ _
  | inr hA =>
    let : Nontrivial A := hA
    obtain ⟨M, hM⟩ := C.exists_restrictionModel hG A b a hb
    obtain ⟨N, hN⟩ := D.exists_restrictionModel hG A c a hc
    rw [hM d, hN d]
    exact M.terms_eq N ((baseChange a).map r) (hG.baseChange a)
      (hr.baseChange_parabolic hp hG a) d

include hG hp hr in
/-- The original unscaled terms match after arbitrary common base change,
on every scheme test, without an affine or nonempty overlap premise. -/
theorem range_restriction_eq {V : Scheme.{u}}
    (b : V ⟶ Spec C.ring) (c : V ⟶ Spec D.ring) (a : V ⟶ S)
    (hb : b ≫ C.projection = a) (hc : c ≫ D.projection = a) (d : ℕ) :
    SubgroupFunctor.range
      ((baseChange b).map (C.termInclusion d) ≫
        (Descent.pullbackComparison C.projection b a hb G).hom) =
    SubgroupFunctor.range
      ((baseChange c).map (D.termInclusion d) ≫
        (Descent.pullbackComparison D.projection c a hc G).hom) := by
  let i := (baseChange b).map (C.termInclusion d) ≫
    (Descent.pullbackComparison C.projection b a hb G).hom
  let j := (baseChange c).map (D.termInclusion d) ≫
    (Descent.pullbackComparison D.projection c a hc G).hom
  have hi : IsClosedImmersion i.hom.hom.left :=
    ((C.isClosedSubgroup_termInclusion d).baseChange b).comp_iso
      (Descent.pullbackComparison C.projection b a hb G)
  have hj : IsClosedImmersion j.hom.hom.left :=
    ((D.isClosedSubgroup_termInclusion d).baseChange c).comp_iso
      (Descent.pullbackComparison D.projection c a hc G)
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (SubgroupFunctor.range_eq_iff_baseChange_openCover V.affineBasisCover i j).mpr
  intro k
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  let q := V.affineBasisCover.f k
  apply (SubgroupFunctor.range_comp_iso_eq_iff _ _
    (Descent.pullbackComparison a q (q ≫ a) rfl G)).mp
  change SubgroupFunctor.range
      ((baseChange q).map
          ((baseChange b).map (C.termInclusion d) ≫
            (Descent.pullbackComparison C.projection b a hb G).hom) ≫ _) =
    SubgroupFunctor.range
      ((baseChange q).map
          ((baseChange c).map (D.termInclusion d) ≫
            (Descent.pullbackComparison D.projection c a hc G).hom) ≫ _)
  rw [Descent.range_pullbackComparison_tower, Descent.range_pullbackComparison_tower]
  exact C.range_affineRestriction_eq D r hG hp hr (V.affineBasisCoverRing k)
    (q ≫ b) (q ≫ c) (q ≫ a)
    ((Category.assoc _ _ _).trans (congrArg (fun f => q ≫ f) hb))
    ((Category.assoc _ _ _).trans (congrArg (fun f => q ≫ f) hc)) d

end AffineParabolicFaceChart
end RelativeLevi
end Langlands.GroupScheme
