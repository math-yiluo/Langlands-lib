import Langlands.GroupScheme.HomScheme.AdicTorsionRestriction
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Closedness of algebraized finite-source embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.AdicAffinePoints
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {H G : GroupScheme (Spec (CommRingCat.of A))} [IsSeparated G.X.hom]

set_option maxHeartbeats 1100000 in
/-- A finite-source group homomorphism into a separated target is closed
if all its adic reductions are closed. -/
theorem isClosedSubgroup_of_isFiniteSource [IsFinite H.X.hom] (f : H ⟶ G)
    (hf : ∀ n : ℕ, IsClosedSubgroup ((baseChange (quotientMap (maximalIdeal A) n)).map f)) :
    IsClosedSubgroup f := by
  have : IsFinite (f.hom.hom.left ≫ G.X.hom) := f.hom.hom.w.symm ▸ inferInstance
  have hfin : IsFinite f.hom.hom.left := IsFinite.of_comp _ G.X.hom
  let S := Spec (CommRingCat.of A)
  let P := pullback f f
  let l : P ⟶ H := pullback.fst f f
  let r : P ⟶ H := pullback.snd f f
  let U := Grp.forget (Over S) ⋙ Over.forget S
  have hU : IsPullback l.hom.hom.left r.hom.hom.left f.hom.hom.left f.hom.hom.left :=
    (IsPullback.of_hasPullback f f).map U
  have : IsFinite l.hom.hom.left := MorphismProperty.of_isPullback hU.flip hfin
  have : IsFinite P.X.hom := l.hom.hom.w ▸ (inferInstance : IsFinite (l.hom.hom.left ≫ H.X.hom))
  have hlr : l = r := by
    apply (finiteSourceAdicHom A P H).injective
    apply System.ext
    intro n
    let B := baseChange (quotientMap (maximalIdeal A) n)
    change B.map l = B.map r
    have : IsClosedImmersion (B.map f).hom.hom.left := hf n
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (B.map f).hom.hom.left).mp
    have h : B.map l ≫ B.map f = B.map r ≫ B.map f := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun m => B.map m) (pullback.condition (f := f) (g := f))
    exact congrArg (fun m => m.hom.hom.left) h
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨hfin, (mono_iff_fst_eq_snd hU.isLimit).mpr (congrArg (fun m => m.hom.hom.left) hlr)⟩

namespace System

variable [IsCommMonObj H.X]

/-- Algebraizing the finite torsion restrictions of a formal closed torus
system gives actual closed torsion embeddings. -/
theorem torsionRestriction_isClosedSubgroup (hH : RelativeTorus.IsTorus H)
    (s : System (maximalIdeal A) H G) (hs : ∀ n, IsClosedSubgroup (s.hom n))
    (k : ℕ) (hk : 0 < k) : IsClosedSubgroup (s.torsionRestriction hH.isMultiplicativeType k hk) := by
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have : IsFinite (torsion H (k : ℤ)).X.hom := (hH.isMultiplicativeType.torsion_geometry k hk).1
  have ht : IsClosedImmersion (torsionι H (k : ℤ)).hom.hom.left := inferInstance
  apply isClosedSubgroup_of_isFiniteSource
  intro n
  rw [torsionRestriction_reduce]
  exact (IsClosedSubgroup.baseChange _ (show IsClosedSubgroup (torsionι H (k : ℤ)) from ht)).comp (hs n)

end System

/-- Closedness of actual torsion maps obtained from formal closed torus maps. -/
def AdicTorsionClosedEmbeddingStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsCommMonObj H.X] [IsSeparated G.X.hom]
    (hH : RelativeTorus.IsTorus H) (s : System (maximalIdeal A) H G),
    (∀ n, IsClosedSubgroup (s.hom n)) →
    ∀ (k : ℕ) (hk : 0 < k), IsClosedSubgroup (s.torsionRestriction hH.isMultiplicativeType k hk)

theorem adicTorsionClosedEmbedding : AdicTorsionClosedEmbeddingStatement.{u} := by
  intro A _ _ _ _ H G _ _ hH s hs
  exact s.torsionRestriction_isClosedSubgroup hH hs

end Langlands.GroupScheme.HomScheme.Adic
