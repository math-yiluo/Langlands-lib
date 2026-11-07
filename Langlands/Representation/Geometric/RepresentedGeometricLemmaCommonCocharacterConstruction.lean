import Langlands.GroupScheme.Rational.CommonCocharacterLeviIntersection
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryReduction

/-! # Actual geometric-lemma data from common-torus cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Construction

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  (z : rationalPoints G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
  (α β : cocharacterLattice T)

/-- Construct the actual two intersection triples, the conjugation isomorphism,
its original rational-point homeomorphism, and the common maximal split torus.
The supplied cocharacters realize the target triple and the source triple
conjugated by `z⁻¹` on all relative test schemes. -/
def geometricLemmaIntersectionDatumOfCommonCocharacters
    (hQ : SubgroupFunctor.range q =
      Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i))
    (hL : SubgroupFunctor.range (lQ ≫ q) =
      Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i))
    (hU : SubgroupFunctor.range (rQ ≫ q) =
      Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i))
    (hP : SubgroupFunctor.range (p ≫ (G.innerIso z⁻¹).hom) =
      Dynamic.parabolic (CommGroupScheme.groupHom β ≫ i))
    (hM : SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) =
      Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i))
    (hN : SubgroupFunctor.range (r ≫ p ≫ (G.innerIso z⁻¹).hom) =
      Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i)) :
    GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z := by
  have hzz' : (G.innerIso z⁻¹).hom ≫ (G.innerIso z).hom = 𝟙 G := by
    rw [innerIso_inv_hom, Iso.inv_hom_id]
  have hcM : IsClosedSubgroup (l ≫ p ≫ (G.innerIso z⁻¹).hom) :=
    hl.isClosedSubgroup.comp (hp.isClosedSubgroup.comp_iso _)
  have hcL : IsClosedSubgroup (lQ ≫ q) :=
    hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have hrepM : (Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i)).IsRepresentedBy
      (l ≫ p ≫ (G.innerIso z⁻¹).hom) :=
    ⟨hcM.mono_overHom, hM⟩
  have hrepL : (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).IsRepresentedBy
      (lQ ≫ q) :=
    ⟨hcL.mono_overHom, hL⟩
  let A := commonCocharacterLeviIntersection hl.isConnectedReductive i β α hcM hrepM
  let B := commonCocharacterLeviIntersection hlQ.isConnectedReductive i α β hcL hrepL
  have hparA : SubgroupFunctor.range (A.p' ≫ l ≫ p ≫ (G.innerIso z⁻¹).hom) =
      SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) ⊓
        SubgroupFunctor.range q := by
    simpa only [Category.assoc, hQ] using A.parabolic_eq
  have hleviA : SubgroupFunctor.range (A.l' ≫ A.p' ≫ l ≫ p ≫ (G.innerIso z⁻¹).hom) =
      SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) ⊓
        SubgroupFunctor.range (lQ ≫ q) := by
    simpa only [Category.assoc, hL] using A.levi_eq
  have hradA : SubgroupFunctor.range (A.r' ≫ A.p' ≫ l ≫ p ≫ (G.innerIso z⁻¹).hom) =
      SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) ⊓
        SubgroupFunctor.range (rQ ≫ q) := by
    simpa only [Category.assoc, hU] using A.radical_eq
  have hpar := range_comp_iso_eq_inf (G.innerIso z) hparA
  have hlevi := range_comp_iso_eq_inf (G.innerIso z) hleviA
  have hrad := range_comp_iso_eq_inf (G.innerIso z) hradA
  simp only [Category.assoc, hzz', Category.comp_id] at hpar hlevi hrad
  have hparB : SubgroupFunctor.range (B.p' ≫ lQ ≫ q) =
      SubgroupFunctor.range (lQ ≫ q) ⊓
        SubgroupFunctor.range (p ≫ (G.innerIso z⁻¹).hom) := by
    simpa only [Category.assoc, hP] using B.parabolic_eq
  have hleviB : SubgroupFunctor.range (B.l' ≫ B.p' ≫ lQ ≫ q) =
      SubgroupFunctor.range (lQ ≫ q) ⊓
        SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) := by
    simpa only [Category.assoc, hM] using B.levi_eq
  have hradB : SubgroupFunctor.range (B.r' ≫ B.p' ≫ lQ ≫ q) =
      SubgroupFunctor.range (lQ ≫ q) ⊓
        SubgroupFunctor.range (r ≫ p ≫ (G.innerIso z⁻¹).hom) := by
    simpa only [Category.assoc, hN] using B.radical_eq
  have hcommon : SubgroupFunctor.range (B.l' ≫ B.p' ≫ lQ ≫ q ≫ (G.innerIso z).hom) =
      SubgroupFunctor.range (A.l' ≫ A.p' ≫ l ≫ p) := by
    have h := range_comp_iso_eq_inf (G.innerIso z) hleviB
    simp only [Category.assoc, hzz', Category.comp_id] at h
    rw [h, hlevi, subgroupFunctor_inf_comm]
  have hcA : IsClosedSubgroup (A.l' ≫ A.p' ≫ l ≫ p) :=
    A.hl'.isClosedSubgroup.comp (A.hp'.isClosedSubgroup.comp
      (hl.isClosedSubgroup.comp hp.isClosedSubgroup))
  have hcB : IsClosedSubgroup (B.l' ≫ B.p' ≫ lQ ≫ q ≫ (G.innerIso z).hom) :=
    B.hl'.isClosedSubgroup.comp (B.hp'.isClosedSubgroup.comp
      (hlQ.isClosedSubgroup.comp (hq.isClosedSubgroup.comp_iso _)))
  have hrepA : (SubgroupFunctor.range (A.l' ≫ A.p' ≫ l ≫ p)).IsRepresentedBy
      (A.l' ≫ A.p' ≫ l ≫ p) := ⟨hcA.mono_overHom, rfl⟩
  have hrepB : (SubgroupFunctor.range (A.l' ≫ A.p' ≫ l ≫ p)).IsRepresentedBy
      (B.l' ≫ B.p' ≫ lQ ≫ q ≫ (G.innerIso z).hom) := ⟨hcB.mono_overHom, hcommon⟩
  let φ : B.M' ≅ A.M' :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hrepB hrepA
  have hφ : φ.hom ≫ A.l' ≫ A.p' ≫ l ≫ p =
      B.l' ≫ B.p' ≫ lQ ≫ q ≫ (G.innerIso z).hom :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hrepB hrepA
  have ht : A.torusMap ≫ A.l' ≫ A.p' ≫ l ≫ p = i ≫ (G.innerIso z).hom := by
    have h := congrArg (fun f : T.toGrp ⟶ G => f ≫ (G.innerIso z).hom) A.torusMap_comp
    simpa only [Category.assoc, hzz', Category.comp_id] using h
  have := B.hl'.isConnectedReductive.isAffineHom
  have := A.hl'.isConnectedReductive.isAffineHom
  have : IsAffine B.M'.X.left := isAffine_of_isAffineHom B.M'.X.hom
  have : IsAffine A.M'.X.left := isAffine_of_isAffineHom A.M'.X.hom
  let := leviPointTopology B.l' B.hl'
  let := leviPointTopology A.l' A.hl'
  let eφ : rationalPoints B.M' ≃* rationalPoints A.M' :=
    { toFun := rationalPoints.map φ.hom
      invFun := rationalPoints.map φ.inv
      left_inv := fun x => by
        simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
          Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
      right_inv := fun x => by
        simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
          Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      map_mul' := map_mul (rationalPoints.map φ.hom) }
  exact
    { P' := A.P', M' := A.M', N' := A.N', p' := A.p', l' := A.l', r' := A.r'
      hp' := A.hp', hr' := A.hr', hl' := A.hl', hmul' := A.hmul'
      Q' := B.P', L' := B.M', U' := B.N', q' := B.p', lQ' := B.l', rQ' := B.r'
      hq' := B.hp', hrQ' := B.hr', hlQ' := B.hl', hmulQ' := B.hmul'
      parabolic_eq := hpar, levi_eq := hlevi, radical_eq := hrad
      parabolic_eq' := hparB, levi_eq' := hleviB, radical_eq' := hradB
      φ := φ, φ_comp := hφ
      e :=
        { toMulEquiv := eφ
          continuous_toFun := continuous_rationalPoints_map φ.hom
          continuous_invFun := continuous_rationalPoints_map φ.inv }
      e_apply := fun _ => rfl
      torus := T, t := A.torusMap
      isMaximalSplitTorus := by rw [ht]; exact hi.comp_iso _ }

end Construction

end Langlands.Aubert.General.RepresentedParabolic
