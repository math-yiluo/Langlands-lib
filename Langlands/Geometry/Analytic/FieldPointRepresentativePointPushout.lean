import Langlands.Geometry.Analytic.FieldPointRepresentativeChartFactorization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout

/-! # Faithful quotient pushouts from equality of full point images -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint

open Set CategoryTheory PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {P A B C : SaturatedAtlasPresentation.{u, v, v} K}

private theorem boundedEval_congr {x y : FieldPoint L C.presentation}
    (h : x = y) (t : C.presentation.atlas.Index)
    (hx : x.point ∈ range (C.presentation.atlas.chart t))
    (hy : y.point ∈ range (C.presentation.atlas.chart t)) :
    x.boundedEval t hx = y.boundedEval t hy := by
  cases h
  rfl

variable (p : FieldPoint L P.presentation) (r : P ⟶ A) (s : P ⟶ B)
  (f : A ⟶ C) (g : B ⟶ C)
  (h : (p.map r P.hasAllLocalDomains).map f A.hasAllLocalDomains =
    (p.map s P.hasAllLocalDomains).map g B.hasAllLocalDomains)
  (k : P.presentation.atlas.Index) (hk : p.point ∈ range (P.presentation.atlas.chart k))
  (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
  (t : C.presentation.atlas.Index)
  (hr : r.baseMap '' range (P.presentation.atlas.chart k) ⊆
    range (A.presentation.atlas.chart i))
  (hs : s.baseMap '' range (P.presentation.atlas.chart k) ⊆
    range (B.presentation.atlas.chart j))
  (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
    range (C.presentation.atlas.chart t))
  (hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
    range (C.presentation.atlas.chart t))

include h in
/-- Equality of the two full point images already makes the actual
quotient-valued chart pullbacks agree over the common target chart. -/
theorem chartTestPullback_square_of_point_map_eq :
    (p.chartTestPullback r k hk i hr).comp (f.pullback i t hf) =
      (p.chartTestPullback s k hk j hs).comp (g.pullback j t hg) := by
  have hri := hr ⟨p.point, hk, rfl⟩
  have hsj := hs ⟨p.point, hk, rfl⟩
  have hrft := hf ⟨r.baseMap p.point, hri, rfl⟩
  have hsgt := hg ⟨s.baseMap p.point, hsj, rfl⟩
  have he := boundedEval_congr h t hrft hsgt
  apply BoundedAlgHom.ext
  intro a
  apply character_injective (p.boundedEval k hk)
  calc
    character (p.boundedEval k hk)
        ((p.chartTestPullback r k hk i hr) (f.pullback i t hf a)) =
        (p.map r P.hasAllLocalDomains).boundedEval i hri (f.pullback i t hf a) :=
      congrArg (fun ψ : BoundedAlgHom K (A.presentation.atlas.algebra i) L =>
        ψ (f.pullback i t hf a))
        (p.character_comp_chartTestPullback r k hk i hr)
    _ = ((p.map r P.hasAllLocalDomains).map f A.hasAllLocalDomains).boundedEval
        t hrft a :=
      (congrArg (fun ψ : BoundedAlgHom K (C.presentation.atlas.algebra t) L => ψ a)
        ((p.map r P.hasAllLocalDomains).map_boundedEval f A.hasAllLocalDomains
          t hrft i hri hf)).symm
    _ = ((p.map s P.hasAllLocalDomains).map g B.hasAllLocalDomains).boundedEval
        t hsgt a :=
      congrArg (fun ψ : BoundedAlgHom K (C.presentation.atlas.algebra t) L => ψ a) he
    _ = (p.map s P.hasAllLocalDomains).boundedEval j hsj (g.pullback j t hg a) :=
      congrArg (fun ψ : BoundedAlgHom K (C.presentation.atlas.algebra t) L => ψ a)
        ((p.map s P.hasAllLocalDomains).map_boundedEval g B.hasAllLocalDomains
          t hsgt j hsj hg)
    _ = character (p.boundedEval k hk)
        ((p.chartTestPullback s k hk j hs) (g.pullback j t hg a)) :=
      (congrArg (fun ψ : BoundedAlgHom K (B.presentation.atlas.algebra j) L =>
        ψ (g.pullback j t hg a))
        (p.character_comp_chartTestPullback s k hk j hs)).symm

/-- Equality of the full point images supplies a bounded map from the actual
affinoid pushout into the faithful local quotient algebra. -/
def chartTestPushoutPullbackOfPointMapEq :
    BoundedAlgHom K (AffinoidPushout.algebra (f.pullback i t hf) (g.pullback j t hg))
      (algebra (p.boundedEval k hk)) :=
  AffinoidPushout.lift (f.pullback i t hf) (g.pullback j t hg)
    (algebra (p.boundedEval k hk))
    (p.chartTestPullback r k hk i hr) (p.chartTestPullback s k hk j hs)
    (p.chartTestPullback_square_of_point_map_eq r s f g h k hk i j t hr hs hf hg)

/-- The pushout map recovers the first actual quotient-valued pullback. -/
theorem chartTestPushoutPullbackOfPointMapEq_comp_leftMap :
    (p.chartTestPushoutPullbackOfPointMapEq r s f g h k hk i j t hr hs hf hg).comp
      (AffinoidPushout.leftMap (f.pullback i t hf) (g.pullback j t hg)) =
        p.chartTestPullback r k hk i hr :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

/-- The pushout map recovers the second actual quotient-valued pullback. -/
theorem chartTestPushoutPullbackOfPointMapEq_comp_rightMap :
    (p.chartTestPushoutPullbackOfPointMapEq r s f g h k hk i j t hr hs hf hg).comp
      (AffinoidPushout.rightMap (f.pullback i t hf) (g.pullback j t hg)) =
        p.chartTestPullback s k hk j hs :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

/-- The two original quotient-valued chart pullbacks determine the map uniquely. -/
theorem chartTestPushoutPullbackOfPointMapEq_unique
    (ψ : BoundedAlgHom K
      (AffinoidPushout.algebra (f.pullback i t hf) (g.pullback j t hg))
      (algebra (p.boundedEval k hk)))
    (hl : ψ.comp (AffinoidPushout.leftMap (f.pullback i t hf) (g.pullback j t hg)) =
      p.chartTestPullback r k hk i hr)
    (hr' : ψ.comp (AffinoidPushout.rightMap (f.pullback i t hf) (g.pullback j t hg)) =
      p.chartTestPullback s k hk j hs) :
    ψ = p.chartTestPushoutPullbackOfPointMapEq r s f g h k hk i j t hr hs hf hg :=
  AffinoidPushout.hom_ext _ _ _
    ψ (p.chartTestPushoutPullbackOfPointMapEq r s f g h k hk i j t hr hs hf hg)
    (hl.trans (p.chartTestPushoutPullbackOfPointMapEq_comp_leftMap r s f g h
      k hk i j t hr hs hf hg).symm)
    (hr'.trans (p.chartTestPushoutPullbackOfPointMapEq_comp_rightMap r s f g h
      k hk i j t hr hs hf hg).symm)

end Langlands.Analytic.AffinoidAtlasPresentation.FieldPoint
