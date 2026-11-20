import Langlands.GroupScheme.HomScheme.AdicSplitTorusEffectivity
import Langlands.GroupScheme.HomScheme.AdicFiniteDescent
import Langlands.GroupScheme.HomScheme.AdicFiniteTest
import Langlands.GroupScheme.Torus.CompleteLocalSimultaneousSplitting
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialReduction
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.RelativeDiagonalizableSplit
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Adic Hom effectivity for tori with affine target fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal
  (isAdicComplete_map_of_finite)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

/-- Adic restriction from a torus to a smooth separated quasi-compact group
with affine residue-field fibres is bijective over a complete Noetherian local ring. -/
def AffineFiberTorusAdicHomStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (H G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    RelativeTorus.IsTorus H → HasAffineResidueFibers G →
    Function.Bijective (System.restrict (maximalIdeal A) H G)

private theorem affineAlgebraizationUnique_of_isSeparated
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {H G : GroupScheme (Spec (CommRingCat.of A))} [IsSeparated G.X.hom] :
    AffineAlgebraizationUnique I H G := by
  intro B _ φ hφ hH s f g hf hg
  let : Algebra A B := φ.toAlgebra
  let : Module.Finite A B := hφ
  let : IsAdicComplete (I.map φ) B := isAdicComplete_map_of_finite (S := B) I
  let p := Spec.map (CommRingCat.ofHom φ)
  have : IsSeparated ((baseChange p).obj G).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom p))
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  exact eq_of_isAlgebraization_of_injective φ s
    (diagonalizableAdicInjectivity_of_iso (I.map φ)
      (Diagonalizable.relativeModelIso (CommRingCat.of B) M ≪≫ e.symm)) f g hf hg

set_option maxHeartbeats 1200000 in
/-- Apply split-source effectivity on a finite étale local cover, then descend
using uniqueness on the finite double overlap. -/
theorem affineFiberTorusAdicHom : AffineFiberTorusAdicHomStatement.{u} := by
  intro A _ _ _ _ H G _ _ _ hH hG
  let : IsCommMonObj H.X := hH.isCommMonObj
  refine ⟨System.restrict_injective_of_torsion hH.isMultiplicativeType G, ?_⟩
  intro s
  let : HenselianLocalRing A := CompleteLocalDeformation.henselianLocalRing_of_complete A
  obtain ⟨𝒰, h𝒰⟩ := hH
  let d := CompleteLocalDeformation.localSplitting A H
    (MultiplicativeTypeQuasiIsotrivial.exists_finite_etale_of_etale_cover A H 𝒰
      (fun i => (h𝒰 i).isRelativeDiagonalizable))
  let B := d.Carrier
  let φ := algebraMap A B
  let p := Spec.algebraMap A B
  let H' := (baseChange p).obj H
  let G' := (baseChange p).obj G
  let : Nonempty (Spec (CommRingCat.of B)) := ⟨closedPoint B⟩
  let : IsFinite p := d.specFinite
  let : Etale p := d.specEtale
  let : Surjective p := d.specSurjective
  let : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom p))
  let : IsSeparated G'.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom p))
  let : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom p))
  have htor : RelativeTorus.IsTorus H := ⟨𝒰, h𝒰⟩
  have hspl : IsSplitTorus H' :=
    (htor.baseChange p).isSplitTorus_of_isDiagonalizable d.split
  have heff : Function.Bijective (System.restrict ((maximalIdeal A).map φ) H' G') := by
    rw [show (maximalIdeal A).map φ = maximalIdeal B from d.residueData.map_maximalIdeal]
    exact splitTorusAdicEffectivity B H' G' hspl (hG.baseChange p)
  obtain ⟨f, hf⟩ := heff.surjective (s.pull φ)
  have ha : s.IsAlgebraization (V := Over.mk p) f := isAlgebraization_of_restrict_pull φ s f hf
  let W := Over.mk (Descent.fst p ≫ p)
  have hW : RelativeMultiplicativeType.IsDiagonalizable ((baseChange W.hom).obj H) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (Descent.pullbackComparison p (Descent.fst p) (Descent.fst p ≫ p) rfl H).symm
      (d.split.baseChange (Descent.fst p))
  let : IsFinite W.hom := inferInstanceAs (IsFinite (Descent.fst p ≫ p))
  have hc : evaluate (overlapFst p) f = evaluate (overlapSnd p) f :=
    eq_of_isAlgebraization_of_isFinite (affineAlgebraizationUnique_of_isSeparated (maximalIdeal A))
      W hW (System.isAlgebraization_evaluate ha _) (System.isAlgebraization_evaluate ha _)
  have hcompat := compatible_of_evaluate_eq p f hc
  refine ⟨Descent.EtaleHomDescent.hom p f hcompat, ?_⟩
  apply System.pull_injective φ
  rw [System.pull_restrict]
  exact (congrArg (System.restrict ((maximalIdeal A).map φ) H' G')
    (Descent.EtaleHomDescent.baseChange_hom p f hcompat)).trans hf

end Langlands.GroupScheme.HomScheme.Adic
