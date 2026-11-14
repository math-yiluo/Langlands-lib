import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellProof
import Langlands.GroupScheme.Rational.DynamicRootProductsLargerSupport

/-! # Actual root and full-centralizer open charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.BruhatTits.IntegralModels.RootCentralizerOpenChart

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Ordered multiplication in a dynamic radical stays an isomorphism when
its full root representatives are replaced by other full representatives. -/
theorem isIso_rootProduct_of_representatives
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (D : RelativeRoot.DynamicRootProductData i ν a)
    (ha : ∀ r, 0 < latticePairing S (a r) ν)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (RelativeRoot.subgroup i (a r)).IsRepresentedBy (j r)) :
    ∃ h : ∀ r, SubgroupFunctor.range (j r) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i),
      IsIso (RelativeRoot.orderedMultiplication
        (fun r => D.unipotentRep.factorHom (j r) (h r))) := by
  have hle (r : Fin n) : RelativeRoot.subgroup i (a r) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) :=
    RelativeRoot.subgroup_le_dynamicUnipotent_of_isDomain i ν (ha r)
  have h (r : Fin n) : SubgroupFunctor.range (j r) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
    rw [(hj r).2]
    exact hle r
  have hD (r : Fin n) : SubgroupFunctor.range (D.factorInclusions r) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
    rw [(D.factorRep r).2]
    exact hle r
  refine ⟨h, ?_⟩
  exact RelativeRoot.isIso_orderedMultiplication_factorHom_of_isIso
    D.unipotentRep j hj h D.unipotentRep D.factorInclusions D.factorRep hD
    (RelativeRoot.isIso_orderedMultiplication_factorHom_of_iso
      D.unipotentRep D.factorInclusions hD D.productIso D.product_comp)

/-- The actual ordered-product isomorphism for any replacements of the
full root representatives in supplied dynamic product data. -/
def rootProductIsoOfRepresentatives
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (D : RelativeRoot.DynamicRootProductData i ν a)
    (ha : ∀ r, 0 < latticePairing S (a r) ν)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (RelativeRoot.subgroup i (a r)).IsRepresentedBy (j r)) :
    (∏ᶜ H).X ≅ D.unipotentGroup.X :=
  let h := isIso_rootProduct_of_representatives i ν a D ha j hj
  RelativeRoot.orderedProductIso D.unipotentRep j h.choose h.choose_spec

/-- The transported isomorphism composes to the specified ambient ordered
multiplication, rather than only agreeing on rational points. -/
theorem rootProductIsoOfRepresentatives_comp
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (D : RelativeRoot.DynamicRootProductData i ν a)
    (ha : ∀ r, 0 < latticePairing S (a r) ν)
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (RelativeRoot.subgroup i (a r)).IsRepresentedBy (j r)) :
    (rootProductIsoOfRepresentatives i ν a D ha j hj).hom ≫
      D.unipotentInclusion.hom.hom = RelativeRoot.orderedMultiplication j :=
  RelativeRoot.orderedProductIso_hom_comp D.unipotentRep j _ _

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- Any full root representatives in the two ordered dynamic products,
with the full whole-torus centralizer in the middle, give an actual open
ordered multiplication chart for a generic cocharacter. -/
theorem isOpenImmersion_orderedMultiplication
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {nN nP : ℕ} (aN : Fin nN → characterLattice S)
    (aP : Fin nP → characterLattice S)
    (DN : RelativeRoot.DynamicRootProductData i (-ν) aN)
    (DP : RelativeRoot.DynamicRootProductData i ν aP)
    (haN : ∀ r, 0 < latticePairing S (aN r) (-ν))
    (haP : ∀ r, 0 < latticePairing S (aP r) ν)
    {H : Fin (nN + (nP + 1)) → GroupScheme (Spec (CommRingCat.of k))}
    (j : ∀ r, H r ⟶ G)
    (hjN : ∀ r, (RelativeRoot.subgroup i (aN r)).IsRepresentedBy
      (j (Fin.castAdd (nP + 1) r)))
    (hjZ : (torusCentralizer i).IsRepresentedBy (j (Fin.natAdd nN 0)))
    (hjP : ∀ r, (RelativeRoot.subgroup i (aP r)).IsRepresentedBy
      (j (Fin.natAdd nN r.succ))) :
    IsOpenImmersion (RelativeRoot.orderedMultiplication j).left := by
  obtain ⟨hN, hNiso⟩ := isIso_rootProduct_of_representatives i (-ν) aN DN haN
    (fun r => j (Fin.castAdd (nP + 1) r)) hjN
  obtain ⟨hP, hPiso⟩ := isIso_rootProduct_of_representatives i ν aP DP haP
    (fun r => j (Fin.natAdd nN r.succ)) hjP
  let : IsIso (RelativeRoot.orderedMultiplication
      (fun r => DN.unipotentRep.factorHom _ (hN r))) := hNiso
  let : IsIso (RelativeRoot.orderedMultiplication
      (fun r => DP.unipotentRep.factorHom _ (hP r))) := hPiso
  have hNrep : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy DN.unipotentInclusion := by
    have h := DN.unipotentRep
    rw [groupHom_neg_comp_eq_oppositeCocharacter_overBase] at h
    exact h
  have hZrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (j (Fin.natAdd nN 0)) := by
    rw [hS.dynamicCentralizer_eq_torusCentralizer i ν hν]
    exact hjZ
  exact OrderedIntegralOpenCell.isOpenImmersion_orderedMultiplication_of_split j
    (CommGroupScheme.groupHom ν ≫ i) hNrep hZrep DP.unipotentRep
    (RelativeRoot.orderedMultiplication
      (fun r => DN.unipotentRep.factorHom _ (hN r)))
    (RelativeRoot.orderedMultiplication_factorHom DN.unipotentRep _ hN)
    (𝟙 _) (by simp)
    (RelativeRoot.orderedMultiplication
      (fun r => DP.unipotentRep.factorHom _ (hP r)))
    (RelativeRoot.orderedMultiplication_factorHom DP.unipotentRep _ hP)

end Langlands.BruhatTits.IntegralModels.RootCentralizerOpenChart
