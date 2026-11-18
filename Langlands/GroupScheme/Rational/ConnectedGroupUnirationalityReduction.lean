import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReductionStatement
import Langlands.AlgebraicGeometry.PointTopology.UnirationalProducts
import Langlands.GroupScheme.Torus.TorusUnirationalityStatement
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceStatement
import Langlands.GroupScheme.Reductive.TorusDominationProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.AlgebraicGeometry.PointTopology.UnirationalSpreading
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.GroupScheme.Torus.Geometry

/-! # Connected group unirationality: quotient reduction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.ConnectedUnirationality

section Section

variable {B : Scheme.{u}} {K H Q : GroupScheme B} (j : K ⟶ H) (q : H ⟶ Q)
    (σ : Q.X ⟶ H.X)

/-- Multiply a kernel element with a supplied ordinary scheme section. -/
def sectionMultiplication : K.X ⊗ Q.X ⟶ H.X :=
  (fst K.X Q.X ≫ j.hom.hom) * (snd K.X Q.X ≫ σ)

/-- An ordinary scheme section of a full-kernel quotient gives a surjective
kernel-times-quotient multiplication map. -/
theorem sectionMultiplication_surjective
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (hσ : σ ≫ q.hom.hom = 𝟙 Q.X) :
    Surjective (sectionMultiplication j σ).left := by
  have hx : ((𝟙 H.X) * (q.hom.hom ≫ σ)⁻¹) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp,
      Category.assoc, hσ, Category.comp_id, mul_inv_cancel]
  obtain ⟨a, ha⟩ := SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hk _ hx
  let r : H.X ⟶ K.X ⊗ Q.X := lift a q.hom.hom
  have hr : r ≫ sectionMultiplication j σ = 𝟙 H.X := by
    simp only [r, sectionMultiplication, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc, ha]
    exact inv_mul_cancel_right _ _
  refine ⟨fun y => ⟨r.left y, ?_⟩⟩
  have hr' : r.left ≫ (sectionMultiplication j σ).left = 𝟙 H.X.left :=
    congrArg (fun f => f.left) hr
  rw [← Scheme.Hom.comp_apply, hr']
  rfl

end Section

variable
    (hsplit : SplitUnipotentAffineSpaceStatement.{u})

include hsplit in
/-- The affine-space description gives unirationality of every affine split
unipotent group. -/
theorem splitUnipotent_isUnirational
    {k : Type u} [Field k] (U : GroupScheme (Spec (CommRingCat.of k)))
    (haff : IsAffineHom U.X.hom) (hU : RelativeRoot.IsSplitUnipotent U) :
    IsUnirational k U.X := by
  obtain ⟨n, hn⟩ := hU
  obtain ⟨e⟩ := hsplit k n U haff hn
  exact (isUnirational_affineSpace (k := k) (ULift.{u} (Fin n))).of_iso e.symm

section Perfect

include hsplit in
/-- A smooth connected affine group over a perfect field is unirational once
connected reductive groups over that field are. -/
theorem perfect_isUnirational_of_reductive
    {k : Type u} [Field k] [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hred : ∀ Q : GroupScheme (Spec (CommRingCat.of k)),
      IsConnectedReductive Q → IsUnirational k Q.X) :
    IsUnirational k G.X := by
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence k G
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  have : Smooth U.X.hom := hi.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hUaff : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hUsplit := perfectFieldUnipotentSplit k U hi.connectedSpace hi.isUnipotent
  have hUr := splitUnipotent_isUnirational hsplit U hUaff hUsplit
  have hQr := hred Q ((perfectFieldPseudoReductive k Q).mp hQ)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  obtain ⟨n, hn⟩ := hUsplit
  have hUv := SplitUnipotentAffineTorsor.cocyclesVanish_of_hasSplitSeries
    (fun V hV T _ W _ _ _ ξ =>
      Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV T W ξ)
    n U hn hUaff
  obtain ⟨σ, hσ⟩ := SplitUnipotentAffineTorsor.exists_section i q hq.2.2.2 hUv
  have hsurj := sectionMultiplication_surjective i q σ hq.2.2.2 hσ
  exact (hUr.tensor hQr).map (sectionMultiplication i σ)
    hsurj.surj.denseRange

end Perfect

/-- Over an infinite field, the published torus domination theorem reduces
reductive unirationality to unirationality of tori. -/
theorem infinite_reductive_isUnirational
    (htorus : TorusUnirationalityStatement.{u})
    {k : Type u} [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    IsUnirational k G.X := by
  obtain ⟨T, f, hT, hf⟩ := reductiveTorusDomination k G hG
  exact ((htorus k).2.1 T hT).map f hf

include hsplit in
/-- A quasi-split group is dominated by its three-factor open cell, whose
centralizer factor is a torus and whose other factors are split unipotent. -/
theorem quasiSplit_isUnirational
    (htorus : TorusUnirationalityStatement.{u})
    {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsQuasiSplit G) :
    IsUnirational k G.X := by
  have hred := hG.isConnectedReductive
  have : Smooth G.X.hom := hred.smooth
  have : IsAffineHom G.X.hom := hred.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : ConnectedSpace G.X.left := hred.connectedSpace
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  obtain ⟨A, a, C, c, ha, hc, _hcc, hC⟩ :=
    quasiSplitTorusCentralizerExistence k G hG
  obtain ⟨ν, hν⟩ := ha.1.1.exists_cocharacter_centralizer a
  let χ := CommGroupScheme.groupHom ν ≫ a
  have hZ : (Dynamic.centralizer χ).IsRepresentedBy c := by
    rw [hν]
    exact hc
  let χ' := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let M := Dynamic.Affine.unipotentScheme χ'
  let U := Dynamic.Affine.unipotentScheme χ
  let m : M ⟶ G := Dynamic.Affine.unipotentHom χ'
  let v : U ⟶ G := Dynamic.Affine.unipotentHom χ
  have hm : (Dynamic.unipotent χ').IsRepresentedBy m :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hv : (Dynamic.unipotent χ).IsRepresentedBy v :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hmc : IsClosedSubgroup m := Dynamic.Affine.isClosedSubgroup_unipotentHom χ'
  have hvc : IsClosedSubgroup v := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have hMr := splitUnipotent_isUnirational hsplit M hmc.isAffineHom
    (Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ' hm hmc)
  have hUr := splitUnipotent_isUnirational hsplit U hvc.isAffineHom
    (Dynamic.isSplitUnipotent_of_isRepresentedBy_unipotent χ hv hvc)
  have hCr := (htorus k).2.1 C hC
  have hCU := hCr.tensor hUr
  have hsrc := hMr.tensor hCU
  let f := Dynamic.tripleCellMultiplication m c v
  have : IsOpenImmersion f.left :=
    Dynamic.isOpenImmersion_tripleCellMultiplication χ hm hZ hv
  let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ M.X ⊗ (C.X ⊗ U.X) :=
    lift 1 (lift 1 1)
  have : Nonempty (M.X ⊗ (C.X ⊗ U.X)).left :=
    ⟨t.left (Classical.arbitrary (Spec (CommRingCat.of k)))⟩
  exact hsrc.map f f.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace

include hsplit in
/-- All field cases: infinite fields use torus domination; finite fields
use quasi-splitness and the open cell. -/
theorem reductive_isUnirational
    (htorus : TorusUnirationalityStatement.{u})
    {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    IsUnirational k G.X := by
  cases finite_or_infinite k with
  | inl hfin =>
    let : Finite k := hfin
    exact quasiSplit_isUnirational hsplit htorus G (finiteFieldQuasiSplit k G hG)
  | inr hinf =>
    let : Infinite k := hinf
    exact infinite_reductive_isUnirational htorus G hG

include hsplit in
/-- The complete connected-group result reduced to the torus and split-unipotent
affine-space statements. -/
theorem connectedGroupUnirationality_of_inputs
    (htorus : TorusUnirationalityStatement.{u}) :
    ConnectedGroupUnirationalityStatement.{u} := by
  intro k _ G
  refine ⟨?_, reductive_isUnirational hsplit htorus G⟩
  intro hperfect hs ha hc
  let : PerfectField k := hperfect
  let : Smooth G.X.hom := hs
  let : IsAffineHom G.X.hom := ha
  let : ConnectedSpace G.X.left := hc
  exact perfect_isUnirational_of_reductive hsplit G
    (fun Q hQ => reductive_isUnirational hsplit htorus Q hQ)

end Langlands.GroupScheme.ConnectedUnirationality

namespace Langlands.GroupScheme

/-- Exact proof of the two-premise reduction of connected-group unirationality. -/
theorem connectedGroupUnirationalityReduction :
    ConnectedGroupUnirationalityReductionStatement.{u} := by
  intro htorus hsplit
  exact ConnectedUnirationality.connectedGroupUnirationality_of_inputs hsplit htorus

end Langlands.GroupScheme
