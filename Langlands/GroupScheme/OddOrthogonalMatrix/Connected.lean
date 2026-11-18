import Langlands.GroupScheme.OddOrthogonalMatrix.Automorphisms
import Langlands.GroupScheme.OddOrthogonalMatrix.IdentityCentralizer
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Connectedness of the full actual split odd norm-one group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {K : Type u} [Field K] {n : ℕ}

/-- Over an algebraically closed field every rational point of the full odd
group lies in its actual identity component. -/
theorem rationalPoint_mem_identityComponent [IsAlgClosed K] (hn : 2 ≤ n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme (Fin n) K).X) :
    g ∈ (SubgroupFunctor.range (identityComponentι (groupScheme (Fin n) K))).carrier _ := by
  let G := groupScheme (Fin n) K
  let H := identityComponent G
  let i := identityComponentι G
  let σ : H ≅ H := IdentityComponent.mapIso (G.innerIso g)
  obtain ⟨h, hh⟩ := TypeBNumbering.exists_innerIso_identityComponent hn σ
  let hG := h ≫ i.hom.hom
  have hg : i ≫ (G.innerIso g).hom = (H.innerIso h).hom ≫ i := by
    rw [hh]
    exact (IdentityComponent.mapIso_hom_identityComponentι (G.innerIso g)).symm
  have hhi : i ≫ (G.innerIso hG).hom = (H.innerIso h).hom ≫ i :=
    (innerIso_hom_comp i h).symm
  have hcentral : i ≫ (G.innerIso (g * hG⁻¹)).hom = i := by
    have hinv : i ≫ (G.innerIso hG⁻¹).hom = (H.innerIso h).inv ≫ i :=
      comp_innerIso_inv_hom (i := i) (n := hG) (σ := H.innerIso h) hhi
    rw [innerIso_mul_hom, reassoc_of% hinv, hg, Iso.inv_hom_id_assoc]
  have htriv : g * hG⁻¹ = 1 := by
    apply eq_one_of_centralizes_identityComponent K
    intro T z
    have he := congrArg (fun f : H ⟶ G => z ≫ f.hom.hom) hcentral
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at he
    change G.constantPoint (g * hG⁻¹) T * (z ≫ i.hom.hom) *
      (G.constantPoint (g * hG⁻¹) T)⁻¹ = z ≫ i.hom.hom at he
    change G.constantPoint (g * hG⁻¹) T * (z ≫ i.hom.hom) =
      (z ≫ i.hom.hom) * G.constantPoint (g * hG⁻¹) T
    have he' := congrArg (fun x => x * G.constantPoint (g * hG⁻¹) T) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  have heq : g = hG := mul_inv_eq_one.mp htriv
  rw [heq]
  exact SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩

/-- The full odd norm-one group is connected over an algebraically closed field. -/
theorem connectedSpace_groupScheme_of_isAlgClosed [IsAlgClosed K] (hn : 2 ≤ n) :
    ConnectedSpace (groupScheme (Fin n) K).X.left :=
  IdentityComponent.connectedSpace_of_forall_mem_range (rationalPoint_mem_identityComponent hn)

/-- The full odd norm-one group is connected over every field. -/
theorem connectedSpace_groupScheme (hn : 2 ≤ n) :
    ConnectedSpace (groupScheme (Fin n) K).X.left := by
  let b := toAlgebraicClosure K
  have : Surjective b := (fieldExtension_fpqc K (AlgebraicClosure K)).1
  refine connectedSpace_of_baseChange b _ ?_
  have : ConnectedSpace (groupScheme (Fin n) (AlgebraicClosure K)).X.left :=
    connectedSpace_groupScheme_of_isAlgClosed hn
  exact DynamicConnected.connectedSpace_of_iso (baseChangeModelIso (l := Fin n) b)

/-- The identity-component inclusion of the actual full odd group is an isomorphism. -/
def identityComponentIso (hn : 2 ≤ n) :
    identityComponent (groupScheme (Fin n) K) ≅ groupScheme (Fin n) K := by
  have : ConnectedSpace (groupScheme (Fin n) K).X.left := connectedSpace_groupScheme hn
  exact IdentityComponent.connectedIso _

@[simp] theorem identityComponentIso_hom (hn : 2 ≤ n) :
    (identityComponentIso (K := K) hn).hom = identityComponentι (groupScheme (Fin n) K) := rfl

set_option linter.defProp false in
/-- The full actual split odd norm-one group is connected reductive. -/
def reductive (hn : 2 ≤ n) : IsConnectedReductive (groupScheme (Fin n) K) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact (identityReductive (Fin n) K).of_iso (identityComponentIso hn).symm

end Langlands.GroupScheme.OddOrthogonalMatrix
