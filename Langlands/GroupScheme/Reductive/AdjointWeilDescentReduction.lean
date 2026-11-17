import Langlands.GroupScheme.Reductive.AdjointWeilPresentation
import Langlands.GroupScheme.Reductive.AdjointPinnedAtlas
import Langlands.GroupScheme.Reductive.AdjointWeilPairRecovery
import Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentStatement

/-! # Adjoint Weil existence reduced to local products and pair descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffineAdjointWeilPresentation

variable {A : Type u} [CommRing A]
  {G H : GroupScheme (Spec (CommRingCat.of A))}

/-- Precompose an actual presentation by an isomorphism of the original group. -/
def precompose (P : AffineAdjointWeilPresentation H) (e : G ≅ H) :
    AffineAdjointWeilPresentation G where
  ring := P.ring
  group := P.group
  surjective := P.surjective
  reductive := P.reductive
  fibres := P.fibres
  iso := e ≪≫ P.iso

/-- Generic almost-simple pair descent, if supplied, descends actual adjoint
presentations, with adjointness recovered from the original local comparisons. -/
def ofEtaleLocal (hD : AffineWeilPairEtaleDescentStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {J : Type u} (R : J → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.Etale A (R i)]
    (P : ∀ i, AffineAdjointWeilPresentation
      ((GroupScheme.baseChange (algebraBaseMap A (R i))).obj G))
    (hcover : ∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (algebraBaseMap A (R i))) :
    AffineAdjointWeilPresentation G := by
  apply Classical.choice
  obtain ⟨B, hB, hAB, hfin, hproj, het, G', haff, hlft,
      hsurj, hred, hAS, hiso, hrec⟩ :=
    hD A G J R (fun i => (P i).ring) (fun i => (P i).group) hcover
      (fun i => (P i).surjective) (fun i => (P i).reductive)
      (fun i s => ((P i).fibres s).2) (fun i => ⟨(P i).iso⟩)
  let : CommRing B := hB
  let : Algebra A B := hAB
  let : Module.Finite A B := hfin
  let : Module.Projective A B := hproj
  let : Algebra.Etale A B := het
  let : IsAffine G'.X.left := haff
  let : LocallyOfFiniteType G'.X.hom := hlft
  let E (i : J) : R i ⊗[A] B ≃ₐ[R i] (P i).ring := Classical.choose (hrec i)
  have hadj : IsFibrewiseAdjoint G' := by
    apply AffineWeilPairRecovery.isFibrewiseAdjoint A B R (fun i => (P i).ring)
      E G' (fun i => (P i).group) hcover
    · intro i
      rw [AffineWeilPairRecovery.map_eq]
      exact Classical.choose_spec (hrec i)
    · intro i s
      exact ((P i).fibres s).1
  exact ⟨
    { ring := B
      group := G'
      surjective := hsurj
      reductive := hred
      fibres := fun s => ⟨hadj s, hAS s⟩
      iso := Classical.choice hiso }⟩

/-- On an arbitrary affine base, local adjoint pinned presentations and
generic pair descent suffice for the global adjoint presentation. This is
a conditional construction, not an assertion that the two inputs hold. -/
def ofPinnedCharts
    (hD : AffineWeilPairEtaleDescentStatement.{u})
    (hlocal : ∀ M : AffineAdjointPinnedModel.{u}, IsFibrewiseNontrivial M.group →
      Nonempty (AffineAdjointWeilPresentation M.group))
    (G : GroupScheme (Spec (CommRingCat.of A))) (hG : IsReductive G)
    (hadj : IsFibrewiseAdjoint G) (hnt : IsFibrewiseNontrivial G) :
    AffineAdjointWeilPresentation G := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let D := AffineAdjointPinnedAtlas.ofReductive hG hadj hnt
  let R (s : Spec (CommRingCat.of A)) := (D.chart s).model.ring
  let : ∀ s, CommRing (R s) := fun s => (D.chart s).model.commRing
  let : ∀ s, Algebra A (R s) := D.chartAlgebra
  have hb (s : Spec (CommRingCat.of A)) :
      algebraBaseMap A (R s) = (D.chart s).map := D.algebraBaseMap_chart s
  let : ∀ s, Algebra.Etale A (R s) := fun s => by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    change Etale (algebraBaseMap A (R s))
    rw [hb s]
    exact (D.chart s).etale
  let modelPresentation (s : Spec (CommRingCat.of A)) :=
    Classical.choice (hlocal (D.chart s).model (D.chart s).nontrivial)
  let P (s : Spec (CommRingCat.of A)) :
      AffineAdjointWeilPresentation
        ((GroupScheme.baseChange (algebraBaseMap A (R s))).obj G) :=
    (modelPresentation s).precompose
      (eqToIso (congrArg (fun b => (GroupScheme.baseChange b).obj G) (hb s)) ≪≫
        (D.chart s).iso)
  apply ofEtaleLocal hD G R P
  intro s
  refine ⟨s, D.point s, ?_⟩
  rw [hb s]
  exact D.image_point s

end Langlands.GroupScheme.AffineAdjointWeilPresentation
