import Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeProof
import Langlands.GroupScheme.Absolute.CentralizerUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Connected reductivity of actual dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- The two structural statements imply radical vanishing for a smooth connected
centralizer, given a maximal torus containing the cocharacter and an ambient
trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_of_borel_envelope
    (hEnvelope : ChevalleyUnipotentEnvelopeStatement.{u})
    (hBorel : CentralizerUnipotentBorelContainmentStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasTrivialUnipotentRadical G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {M : GroupScheme (Spec (CommRingCat.of k))} (j : M ⟶ G)
    (hj : IsClosedSubgroup j) (hrep : (centralizer χ).IsRepresentedBy j)
    (hMsm : Smooth M.X.hom) (hMconn : ConnectedSpace M.X.left)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hT : IsMaximalTorus t) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range t) :
    HasTrivialUnipotentRadical M := by
  intro U i hi hUsm hUconn hU hUnormal
  have hicomp : IsClosedSubgroup (i ≫ j) := by
    let : IsClosedImmersion i.hom.hom.left := hi
    let : IsClosedImmersion j.hom.hom.left := hj
    change IsClosedImmersion (i.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  have hUB : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b → SubgroupFunctor.range t ≤ SubgroupFunctor.range b →
      SubgroupFunctor.range (i ≫ j) ≤ SubgroupFunctor.range b := by
    intro B b hB hTB
    exact hBorel k G χ M j hj hrep hMsm hMconn U i hi hUsm hUconn hU hUnormal
      B b hB (hχ.trans hTB)
  obtain ⟨N, n, hn, hNsm, hNconn, hN, hNnormal, hUn⟩ :=
    hEnvelope k G T t hT U (i ≫ j) hicomp hUsm hUconn hU hUB
  have hnzero := hG N n hn hNsm hNconn hN hNnormal
  have hcompzero : SubgroupFunctor.range (i ≫ j) = ⊥ := by
    apply SubgroupFunctor.ext
    intro V
    rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxN := hUn V hx
    rw [hnzero] at hxN
    exact Subgroup.mem_bot.mp hxN
  let : Mono j.hom.hom := hrep.1
  exact (SubgroupFunctor.range_comp_eq_bot_iff i j).mp hcompzero

/-- Scalar-extension assembly: the two structural inputs imply connected
reductivity when the scalar-extended cocharacter lies in a maximal torus.
Smoothness and connectedness use their published proofs. -/
theorem isConnectedReductive_of_borel_envelope
    (hEnvelope : ChevalleyUnipotentEnvelopeStatement.{u})
    (hBorel : CentralizerUnipotentBorelContainmentStatement.{u})
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {M : GroupScheme (Spec (CommRingCat.of k))} (j : M ⟶ G)
    (hj : IsClosedSubgroup j) (hrep : (centralizer χ).IsRepresentedBy j)
    (hT : ∃ (T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (t : T.toGrp ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G),
      IsMaximalTorus t ∧
        SubgroupFunctor.range (baseChangeCocharacter (toAlgebraicClosure k) χ) ≤
          SubgroupFunctor.range t) :
    IsConnectedReductive M := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hMsm : Smooth M.X.hom := (dynamicSmooth k G χ M j).2.1 hrep
  have hMconn : ConnectedSpace M.X.left :=
    ((dynamicConnected k G χ M j).2 hG.connectedSpace).2 hrep
  refine ⟨hMsm, hj.isAffineHom, hMconn, ?_⟩
  let b := toAlgebraicClosure k
  let Ga := (GroupScheme.baseChange b).obj G
  let Ma := (GroupScheme.baseChange b).obj M
  let ja := (GroupScheme.baseChange b).map j
  let χa := baseChangeCocharacter b χ
  have : Smooth Ga.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom Ga.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace Ga.X.left := hG.connectedSpace_toAlgebraicClosure
  have hrepa : (centralizer χa).IsRepresentedBy ja :=
    isRepresentedBy_centralizer_baseChange b χ hrep
  have hja : IsClosedSubgroup ja := hj.baseChange b
  have hMasm : Smooth Ma.X.hom := (dynamicSmooth (AlgebraicClosure k) Ga χa Ma ja).2.1 hrepa
  have hMaconn : ConnectedSpace Ma.X.left :=
    ((dynamicConnected (AlgebraicClosure k) Ga χa Ma ja).2 inferInstance).2 hrepa
  obtain ⟨T, t, hTmax, hχt⟩ := hT
  exact hasTrivialUnipotentRadical_of_borel_envelope hEnvelope hBorel
    hG.hasTrivialGeometricUnipotentRadical χa ja hja hrepa hMasm hMaconn T t hTmax hχt

/-- Over an algebraically closed field, finite Galois splitting upgrades a
maximal split torus to a maximal torus. -/
private theorem isMaximalTorus_of_finiteGaloisSplitting
    (hFinite : TorusFiniteGaloisSplittingStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G}
    (ht : IsMaximalSplitTorus t) : IsMaximalTorus t := by
  refine ⟨ht.1.1.isTorus, ht.1.2, ?_⟩
  intro T' t' f hT' ht' hf
  exact ht.2 T' t' ⟨IsTorus.isSplitTorus_of_finiteGaloisSplitting hFinite hT', ht'⟩ f hf

/-- The existing maximal split torus factorization yields the precise maximal
torus containment used by radical assembly, conditional on finite Galois splitting. -/
private theorem exists_maximalTorus_of_finiteGaloisSplitting
    (hFinite : TorusFiniteGaloisSplittingStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsMaximalTorus t ∧ SubgroupFunctor.range χ ≤ SubgroupFunctor.range t := by
  obtain ⟨T, t, ν, ht, hν⟩ := cocharacterMaximalSplitTorus k G χ
  exact ⟨T, t, isMaximalTorus_of_finiteGaloisSplitting hFinite ht,
    SubgroupFunctor.range_le_of_factor (CommGroupScheme.groupHom ν) hν⟩

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme

/-- Every supplied closed representative of a cocharacter centralizer in a
connected reductive group over an arbitrary field is connected reductive. -/
theorem dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u} := by
  intro k _ G hG χ M j hj hrep
  apply Dynamic.isConnectedReductive_of_borel_envelope chevalleyUnipotentEnvelope
    centralizerUnipotentBorelContainment hG χ j hj hrep
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  exact Dynamic.exists_maximalTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting _ _

end Langlands.GroupScheme
