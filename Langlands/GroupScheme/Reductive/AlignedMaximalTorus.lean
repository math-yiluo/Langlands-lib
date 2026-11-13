import Langlands.GroupScheme.Reductive.TitsIndexCentralizerConjugacy
import Langlands.GroupScheme.Reductive.AbsoluteStarAction
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Descended maximal tori aligned with split coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of (SeparableClosure k)))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {D : CommGroupScheme (Spec (CommRingCat.of (SeparableClosure k)))}

/-- A maximal torus over the ground field containing `s`, identified after
scalar extension with `D`, with the prescribed factorization `ψ` retained. -/
def HasAlignedMaximalTorus (s : S.toGrp ⟶ G) (j : D.toGrp ⟶ H)
    (ψ : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj S ⟶ D) :
    Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (f : S ⟶ T),
    IsMaximalTorus i ∧ CommGroupScheme.groupHom f ≫ i = s ∧
      ∃ (e : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T ≅ D)
        (Φ : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅ H),
        (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map i ≫ Φ.hom =
          CommGroupScheme.groupHom e.hom ≫ j ∧
        (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map f ≫ e.hom = ψ

set_option maxHeartbeats 400000 in
/-- Centralizer conjugacy aligns a descended maximal torus without changing
the supplied split-subtorus map in split coordinates. -/
theorem hasAlignedMaximalTorus [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ G) (hs : IsClosedSubgroup s)
    (j : D.toGrp ⟶ H) (hj : IsMaximalTorus j) (hD : IsSplitTorus D.toGrp)
    (Φ : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅ H)
    (ψ : (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj S ⟶ D)
    (hψ : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map s ≫ Φ.hom =
      CommGroupScheme.groupHom ψ ≫ j) :
    HasAlignedMaximalTorus s j ψ := by
  let : Smooth G.X.hom := hG.smooth
  let b := algebraBaseMap k (SeparableClosure k)
  let F := GroupScheme.baseChange b
  let C := CommGroupScheme.baseChange b
  obtain ⟨T, i, f, hi, hf⟩ :=
    EnvelopeInfiniteReduction.exists_isMaximalTorus_factor G s hS.isTorus hs
  let f' : S ⟶ T := Additive.ofMul f
  have hsplit : IsSplitTorus (C.obj T).toGrp :=
    GaloisPinningData.isSplitTorus_separableClosure T hi.1
  have hiE : IsMaximalTorus (T := C.obj T) (F.map i) :=
    (maximalTorusBaseChange k (SeparableClosure k) G T i hi.1 hi.2.1).mp hi
  have h₁ : IsMaximalSplitTorus (T := C.obj T) (F.map i ≫ Φ.hom) :=
    (hiE.comp_iso Φ).isMaximalSplitTorus hsplit
  have h₂ : IsMaximalSplitTorus (T := D) j := hj.isMaximalSplitTorus hD
  have hfE : CommGroupScheme.groupHom (C.map f') ≫ (F.map i ≫ Φ.hom) =
      F.map s ≫ Φ.hom := by
    change F.map f ≫ (F.map i ≫ Φ.hom) = _
    rw [← Category.assoc, ← F.map_comp, hf]
  obtain ⟨z, e, he, hz⟩ := exists_centralizing_conj_of_isMaximalSplitTorus
    (A := C.obj S) (T₁ := C.obj T) (T₂ := D) hH
    (hS.baseChange b) (F.map s ≫ Φ.hom) h₁ h₂ (C.map f') ψ hfE hψ.symm
  refine ⟨T, i, f', hi, hf, e, Φ ≪≫ H.innerIso z, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc] using he
  · have hcomp :
        CommGroupScheme.groupHom (C.map f' ≫ e.hom) ≫ j =
          CommGroupScheme.groupHom ψ ≫ j := by
      change CommGroupScheme.groupHom (C.map f') ≫
        (CommGroupScheme.groupHom e.hom ≫ j) = _
      rw [← he, ← Category.assoc, hfE, hz, hψ]
    have : Mono j.hom.hom := hj.2.1.mono_overHom
    have hhom := (cancel_mono j.hom.hom).mp (congrArg (fun a => a.hom.hom) hcomp)
    change Additive.ofMul (CommGroupScheme.groupHom (C.map f' ≫ e.hom)) =
      Additive.ofMul (CommGroupScheme.groupHom ψ)
    congr 1
    exact Grp.hom_ext _ _ hhom

end Langlands.GroupScheme
