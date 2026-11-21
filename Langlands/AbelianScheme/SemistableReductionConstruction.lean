import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Finite DVR extensions and geometric semiabelian presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace Langlands.AbelianScheme

/-- A finite field extension of a DVR's fraction field admits a dominating DVR
whose fraction field is the supplied extension field. -/
def FiniteDvrExtension.ofFiniteField
    (V K L : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field L] [Algebra K L] [Module.Finite K L] :
    FiniteDvrExtension V K := by
  let : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := Langlands.AlgebraicGeometry.NoetherianValuativeCriterion.exists_valuationSubring_dominates
    (A := V) (K := K) (L := L) (IsDiscreteValuationRing.ringKrullDim_eq_one V)
  let W := Classical.choose h
  have hW := Classical.choose_spec h
  let : IsDiscreteValuationRing ↥W := hW.1
  let j : V →+* W := (algebraMap V L).codRestrict W hW.2.1
  let : Algebra V W := j.toAlgebra
  have hloc : IsLocalHom (algebraMap V W) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem := (hW.2.2 a).mp ((mem_maximalIdeal a).mpr hna)
    change (j a : L) ∈ W.nonunits at hmem
    rw [ValuationSubring.coe_mem_nonunits_iff] at hmem
    exact ((mem_maximalIdeal (j a)).mp hmem) ha
  exact
    { ring := W
      localHom := hloc
      fractionField := L
      finite := inferInstance
      mapsCommute := rfl }

@[simp]
theorem FiniteDvrExtension.ofFiniteField_fractionField
    (V K L : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field L] [Algebra K L] [Module.Finite K L] :
    (ofFiniteField V K L).fractionField = L :=
  rfl

/-- Over an algebraically closed field, an abelian quotient with torus kernel
has a split semiabelian presentation. -/
def SplitSemiabelianPresentation.ofTorusKernel {k : Type u} [Field k] [IsAlgClosed k]
    {G : CommGroupScheme (Spec (CommRingCat.of k))} (A : AbelianScheme (Spec (CommRingCat.of k)))
    (q : G ⟶ A.toCommGroupScheme) (hsm : Smooth (CommGroupScheme.hom q))
    (hsurj : Surjective (CommGroupScheme.hom q)) (hT : IsTorus (CommGroupScheme.kernel q).toGrp) :
    SplitSemiabelianPresentation G := by
  let splitting : Σ n : ℕ,
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} (Fin n)) ≅
        CommGroupScheme.kernel q := Classical.choice (by
    classical
    obtain ⟨I, hI, ⟨e⟩⟩ :=
      toriAreSplit_of_isSepClosed k (CommGroupScheme.kernel q).toGrp hT
    let : Fintype I := Fintype.ofFinite I
    let n := Fintype.card I
    let σ : ULift.{u} (Fin n) ≃ I := Equiv.ulift.trans (Fintype.equivFin I).symm
    let t := piEquivIso σ (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp)
    exact ⟨⟨n, CommGroupScheme.isoOfGroupIso (t ≪≫ e.symm)⟩⟩)
  exact
    { torusRank := splitting.1
      quotient := A
      quotientMap := q
      smooth := hsm
      surjective := hsurj
      torusIso := splitting.2 }

@[simp]
theorem SplitSemiabelianPresentation.ofTorusKernel_quotient {k : Type u} [Field k] [IsAlgClosed k]
    {G : CommGroupScheme (Spec (CommRingCat.of k))} (A : AbelianScheme (Spec (CommRingCat.of k)))
    (q : G ⟶ A.toCommGroupScheme) (hsm : Smooth (CommGroupScheme.hom q))
    (hsurj : Surjective (CommGroupScheme.hom q)) (hT : IsTorus (CommGroupScheme.kernel q).toGrp) :
    (ofTorusKernel A q hsm hsurj hT).quotient = A :=
  rfl

@[simp]
theorem SplitSemiabelianPresentation.ofTorusKernel_quotientMap {k : Type u} [Field k] [IsAlgClosed k]
    {G : CommGroupScheme (Spec (CommRingCat.of k))} (A : AbelianScheme (Spec (CommRingCat.of k)))
    (q : G ⟶ A.toCommGroupScheme) (hsm : Smooth (CommGroupScheme.hom q))
    (hsurj : Surjective (CommGroupScheme.hom q)) (hT : IsTorus (CommGroupScheme.kernel q).toGrp) :
    (ofTorusKernel A q hsm hsurj hT).quotientMap = q :=
  rfl

end Langlands.AbelianScheme
