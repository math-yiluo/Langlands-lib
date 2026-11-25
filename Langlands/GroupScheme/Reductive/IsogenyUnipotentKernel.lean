import Langlands.GroupScheme.Reductive.SplitBigCellField
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Ordered root products and full unipotent kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LocalSplitCell

variable {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

private theorem list_prod_postcomp (q : G ⟶ H) (Z : Over (Spec (CommRingCat.of R)))
    (l : List (Z ⟶ G.X)) :
    l.prod ≫ q.hom.hom = (l.map (fun x => x ≫ q.hom.hom)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.prod_cons, List.map_cons, MonObj.mul_comp, ih]

/-- Ordered root products commute with postcomposition by any group homomorphism. -/
theorem orderedProduct_postcomp (u : J → (Ga R ⟶ G)) (q : G ⟶ H)
    {n : ℕ} (pos : Fin n → J) (Z : Over (Spec (CommRingCat.of R)))
    (w : Fin n → Γ(Z.left, ⊤)) :
    orderedProduct u pos Z w ≫ q.hom.hom =
      orderedProduct (fun r => u r ≫ q) pos Z w := by
  simp only [orderedProduct, list_prod_postcomp, List.map_ofFn, Function.comp_def,
    rootPoint_comp]

end LocalSplitCell

namespace IsRootDatumOf

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H}
    {J J' : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [Q.IsReduced]

/-- The actual relative roots of a supplied reduced root datum have reduced rays. -/
theorem reducedRays (hP : IsRootDatumOf i P) (hT : IsSplitTorus T.toGrp) :
    SplitBigCell.ReducedRays i := by
  let : HasUniqueDiv (ℚ ⊗[ℤ] characterLattice T) :=
    HasUniqueDiv.of_module_rat _
  let : HasUniqueDiv (characterLattice T) :=
    hT.character_toRat_injective.hasUniqueDiv toRat
  intro a ha b hb r t hr ht he
  rw [relativeRoots_eq_roots, ← hP.2.1] at ha hb
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  have hlin : ¬ LinearIndependent ℤ ![P.root s, P.root v] := by
    simp only [LinearIndependent.pair_iff, not_forall]
    refine ⟨(r : ℤ), -(t : ℤ), ?_, ?_⟩
    · simpa only [neg_smul, natCast_zsmul, add_neg_eq_zero] using he
    · simp only [Int.natCast_eq_zero, neg_eq_zero]
      omega
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) s v hlin with h | h
  · refine ⟨h, ?_⟩
    rw [h] at he
    apply Int.ofNat_inj.mp
    exact (smul_left_injective ℤ (P.ne_zero v))
      (by simpa only [natCast_zsmul] using he)
  · exfalso
    rw [h, smul_neg] at he
    have he' : (-(r : ℤ)) • P.root v = (t : ℤ) • P.root v := by
      simpa only [neg_smul, natCast_zsmul] using he
    have := (smul_left_injective ℤ (P.ne_zero v)) he'
    omega

/-- A finite ordering of exactly the roots positive on the supplied cocharacter. -/
def positiveRootEnumeration [Finite J] (P : RootDatum J (characterLattice T)
    (cocharacterLattice T)) (ν : cocharacterLattice T) :
    Σ n : ℕ, Fin n ≃ {r : J // 0 < latticePairing T (P.root r) ν} := by
  classical
  letI := Fintype.ofFinite {r : J // 0 < latticePairing T (P.root r) ν}
  exact ⟨Fintype.card _, (Fintype.equivFin _).symm⟩

open RelativeRoot LocalSplitCell

/-- If a homomorphism carries source root parametrizations onto corresponding target
root groups with exact character pullback, its full unipotent kernel is trivial. -/
theorem unipotent_kernel_trivial_of_root_correspondence [Finite J]
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (q : G ⟶ H) (t : T ⟶ T') (e : J ≃ J')
    (hroot : ∀ r, t ≫ Q.root (e r) = P.root r)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (subgroup i' (Q.root (e r))).IsRepresentedBy (u r ≫ q))
    (ν : cocharacterLattice T) (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X)
    (hx : x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z)
    (hq : x ≫ q.hom.hom = 1) : x = 1 := by
  classical
  obtain ⟨n, order⟩ := positiveRootEnumeration P ν
  let pos : Fin n → J := fun r => (order r).val
  let a : Fin n → characterLattice T := fun r => P.root (pos r)
  let b : Fin n → characterLattice T' := fun r => Q.root (e (pos r))
  have hposinj : Function.Injective pos :=
    Subtype.val_injective.comp order.injective
  have hainj : Function.Injective a := P.root.injective.comp hposinj
  have hbinj : Function.Injective b := Q.root.injective.comp (e.injective.comp hposinj)
  have hpair (r : J) :
      latticePairing T' (Q.root (e r)) (ν ≫ t) = latticePairing T (P.root r) ν := by
    rw [← hroot r]
    change gmEndEquiv k ((ν ≫ t) ≫ Q.root (e r)) =
      gmEndEquiv k (ν ≫ (t ≫ Q.root (e r)))
    rw [Category.assoc]
  have ha : Set.range a = {β | β ∈ relativeRoots i ∧ 0 < latticePairing T β ν} := by
    ext β
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self _,
        (order r).property⟩
    · rintro ⟨hβ, hβpos⟩
      rw [relativeRoots_eq_roots, ← hP.2.1] at hβ
      obtain ⟨r, rfl⟩ := hβ
      exact ⟨order.symm ⟨r, hβpos⟩, by simp [a, pos]⟩
  have hb : Set.range b = {β | β ∈ relativeRoots i' ∧
      0 < latticePairing T' β (ν ≫ t)} := by
    ext β
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨by rw [relativeRoots_eq_roots, ← hQ.2.1]; exact Set.mem_range_self _, ?_⟩
      rw [hpair]
      exact (order r).property
    · rintro ⟨hβ, hβpos⟩
      rw [relativeRoots_eq_roots, ← hQ.2.1] at hβ
      obtain ⟨r', rfl⟩ := hβ
      have hr : 0 < latticePairing T (P.root (e.symm r')) ν := by
        rw [← hpair, e.apply_symm_apply]
        exact hβpos
      exact ⟨order.symm ⟨e.symm r', hr⟩, by simp [b, pos]⟩
  obtain ⟨w, hw⟩ := (SplitBigCell.orderedProduct_points G hG T i
    (hi.isMaximalSplitTorus hT) ν (hP.reducedRays hT) u pos a hainj ha
    (fun r => hu (pos r)) Z).2 x |>.mp hx
  have hinj := (SplitBigCell.orderedProduct_points H hH T' i'
    (hi'.isMaximalSplitTorus hT') (ν ≫ t) (hQ.reducedRays hT')
    (fun r => u r ≫ q) pos b hbinj hb (fun r => hv (pos r)) Z).1
  have hwzero : w = 0 := by
    apply hinj
    rw [← orderedProduct_postcomp, hw, hq, orderedProduct_zero]
  rw [← hw, hwzero, orderedProduct_zero]

end IsRootDatumOf
end Langlands.GroupScheme
