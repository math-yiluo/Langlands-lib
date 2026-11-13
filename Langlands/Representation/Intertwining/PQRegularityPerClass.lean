import Langlands.Representation.Intertwining.PQRegularityCriteria
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryProof

/-! # `PQ`-regularity, one strict predecessor at a time -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Cast

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance perClassAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)}

/-- Transporting an intersection datum along an equality of representatives does not change
its piece kernel. -/
theorem pieceSplitComponentKernel_cast {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ M) {z z' : rationalPoints G} (h : z = z')
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    (e : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z =
      GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z')
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    pieceSplitComponentKernel a (cast e D) σ = pieceSplitComponentKernel a D σ := by
  subst h
  rfl

end Cast

set_option maxHeartbeats 1000000 in
/-- `PQ`-regularity one strict predecessor at a time: `σ` is `PQ`-regular exactly when, for
every representative `z` of a strict Bruhat predecessor of the identity double coset and every
intersection datum `D` at `z`, the kernel `I_σ` and the piece kernel of `D` are comaximal. -/
theorem isPQRegular_iff_forall_piece
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
          IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ ↔
            ∀ z : rationalPoints G,
              Geometric.BruhatLT (pointImage p) (pointImage q)
                (DoubleCoset.mk (pointImage p) (pointImage q) z)
                (identityParabolicDoubleCoset p q) →
              ∀ D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
                  q lQ rQ hq hrQ hlQ hmulQ z,
                splitComponentKernel l hl a σ ⊔ pieceSplitComponentKernel a D σ = ⊤ := by
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro σ
  obtain ⟨m, c, zg, hzg, ⟨Dg⟩⟩ := representedGeometricLemmaGeometry k G hG
    P M N Q M U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hcrit := fun (zf : parabolicDoubleCosets p q → rationalPoints G)
      (hzf : ∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (zf w) = w) Df =>
    (pqRegularity_predecessorCriteria k G hG P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ
      hmulQ hsame A a ha σ zf hzf Df).1
  constructor
  · intro hreg z hz D
    classical
    let zf : parabolicDoubleCosets p q → rationalPoints G := fun w =>
      if w = DoubleCoset.mk (pointImage p) (pointImage q) z then z else zg (c.symm w)
    have hzf : ∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (zf w) = w := by
      intro w
      dsimp only [zf]
      split_ifs with hw
      · exact hw.symm
      · rw [hzg, Equiv.apply_symm_apply]
    have hzfz : ∀ w, w = DoubleCoset.mk (pointImage p) (pointImage q) z → z = zf w := by
      intro w hw
      dsimp only [zf]
      split_ifs with h
      · rfl
      · exact absurd hw h
    have hzfn : ∀ w, ¬ w = DoubleCoset.mk (pointImage p) (pointImage q) z →
        zf w = zg (c.symm w) := by
      intro w hw
      dsimp only [zf]
      split_ifs with h
      · exact absurd h hw
      · rfl
    let Df : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q) →
        GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ (zf w) :=
      fun w _ => if hw : w = DoubleCoset.mk (pointImage p) (pointImage q) z then
          cast (by rw [hzfz w hw]) D
        else cast (by rw [hzfn w hw]) (Dg (c.symm w))
    have hK : pieceSplitComponentKernel a
        (Df (DoubleCoset.mk (pointImage p) (pointImage q) z) hz) σ =
        pieceSplitComponentKernel a D σ := by
      simp only [Df, dite_true]
      exact pieceSplitComponentKernel_cast a (hzfz _ rfl) D _ σ
    have h := (hcrit zf hzf Df).mp hreg
    refine top_unique (h.symm.le.trans (sup_le_sup_left ?_ _))
    rw [← hK]
    exact iInf₂_le (DoubleCoset.mk (pointImage p) (pointImage q) z) hz
  · intro hall
    have hzf : ∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (zg (c.symm w)) = w := by
      intro w
      rw [hzg, Equiv.apply_symm_apply]
    refine (hcrit (fun w => zg (c.symm w)) hzf (fun w _ => Dg (c.symm w))).mpr ?_
    have : Fintype (parabolicDoubleCosets p q) := Fintype.ofEquiv _ c
    have hfin : (⨅ (w) (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q)), pieceSplitComponentKernel a (Dg (c.symm w)) σ) =
        ⨅ w ∈ (Finset.univ : Finset (parabolicDoubleCosets p q)),
          ⨅ (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
            (identityParabolicDoubleCoset p q)), pieceSplitComponentKernel a (Dg (c.symm w)) σ := by
      simp only [Finset.mem_univ, iInf_pos]
    rw [hfin]
    refine Ideal.sup_iInf_eq_top fun w _ => ?_
    by_cases hw : Geometric.BruhatLT (pointImage p) (pointImage q) w
        (identityParabolicDoubleCoset p q)
    · rw [iInf_pos hw]
      have hw' := hw
      rw [← hzf w] at hw'
      exact hall _ hw' (Dg (c.symm w))
    · rw [iInf_neg hw, sup_top_eq]

end Langlands.Aubert.General.RepresentedParabolic
