import Langlands.GroupScheme.Reductive.RelativeIsogenyRootUnit
import Langlands.GroupScheme.Reductive.RelativeExponentCharacterLift

/-! # Fppf torus conjugation aligning actual root restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I K : Type u} [Fintype I] [Fintype K]

/-- The ratios of two families of root coefficients, as units on a test scheme. -/
def rootAlignmentUnits (V : Over (Spec (CommRingCat.of R))) (c c' : K → Rˣ) :
    K → (Γ(V.left, ⊤))ˣ :=
  fun a => Units.map (baseScalar V).toMonoidHom (c a * (c' a)⁻¹)

/-- The canonical fppf local torus point realizing the ratios of root coefficients. -/
def rootAlignmentLift (m : K → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec (CommRingCat.of R))) (c c' : K → Rˣ) :=
  splitTorus.exponentUnitsLift (CommRingCat.of R) m hm V (rootAlignmentUnits V c c')

/-- On every refinement, the chosen torus point has the prescribed root values. -/
theorem rootAlignmentLift_charValue (m : K → I → ℤ) (hm : LinearIndependent ℤ m)
    (V : Over (Spec (CommRingCat.of R))) (c c' : K → Rˣ)
    (Z : Over (Spec (CommRingCat.of R)))
    (d : Z ⟶ (rootAlignmentLift m hm V c c').cover) (a : K) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
      (splitTorus.exponentCharacter _ I (m a)) Z
        (d ≫ (rootAlignmentLift m hm V c c').lift) =
      baseScalar Z (c a * (c' a)⁻¹ : Rˣ) := by
  let L := rootAlignmentLift m hm V c c'
  have h := splitTorus.exponentUnitsLift_character_naturality (CommRingCat.of R)
    (splitTorus _ I) (Iso.refl _) m hm V (rootAlignmentUnits V c c') Z d a
  have hv := congrArg (fun z : (Γ(Z.left, ⊤))ˣ => (z : Γ(Z.left, ⊤))) h
  have hv' : VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
      (splitTorus.exponentCharacter _ I (m a)) Z (d ≫ L.lift) =
        (d ≫ L.projection).left.appTop (baseScalar V (c a * (c' a)⁻¹ : Rˣ)) := by
    simp only [splitTorus.exponentCharacterOnTorus, Iso.refl_hom, Iso.refl_inv,
      Grp.id_hom_hom, Category.id_comp, Category.comp_id,
      splitTorus.unitsRestrict, MonoidHom.compLeft_apply, Function.comp_apply,
      rootAlignmentUnits, Units.coe_map] at hv
    convert hv using 1 <;> rfl
  exact hv'.trans (appTop_baseScalar (d ≫ L.projection) _)

variable {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Matching character values align the two root power maps by target conjugation. -/
theorem rootPoint_eq_conjugate_of_charValue
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (m : I → ℤ) {v : Ga R ⟶ H} (hv : IsRootParametrization j m v)
    (u : Ga R ⟶ G) (phi Phi : G ⟶ H) (c c' : Rˣ) (q : ℕ)
    (hphi : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint u Z x ≫ phi.hom.hom = rootPoint v Z (baseScalar Z (c : R) * x ^ q))
    (hPhi : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint u Z x ≫ Phi.hom.hom = rootPoint v Z (baseScalar Z (c' : R) * x ^ q))
    (Z : Over (Spec (CommRingCat.of R))) (t : Z ⟶ (splitTorus _ I).X)
    (ht : VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
      (splitTorus.exponentCharacter _ I m) Z t = baseScalar Z (c * c'⁻¹ : Rˣ))
    (x : Γ(Z.left, ⊤)) :
    rootPoint u Z x ≫ phi.hom.hom =
      (t ≫ j.hom.hom) * (rootPoint u Z x ≫ Phi.hom.hom) * (t ≫ j.hom.hom)⁻¹ := by
  rw [hphi, hPhi, hv.equivariant, ht]
  apply congrArg (rootPoint v Z)
  rw [← mul_assoc, ← map_mul]
  have hc : (↑(c * c'⁻¹) : R) * ↑c' = ↑c := by
    simp only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [hc]

/-- The canonical lift aligns all selected root maps on every refined test scheme. -/
theorem rootAlignmentLift_rootPoint
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (m : K → I → ℤ) (hm : LinearIndependent ℤ m)
    (u : K → (Ga R ⟶ G)) (v : K → (Ga R ⟶ H))
    (hv : ∀ a, IsRootParametrization j (m a) (v a))
    (phi Phi : G ⟶ H) (c c' : K → Rˣ) (q : K → ℕ)
    (hphi : ∀ a (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (u a) Z x ≫ phi.hom.hom =
        rootPoint (v a) Z (baseScalar Z (c a : R) * x ^ q a))
    (hPhi : ∀ a (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (u a) Z x ≫ Phi.hom.hom =
        rootPoint (v a) Z (baseScalar Z (c' a : R) * x ^ q a))
    (V Z : Over (Spec (CommRingCat.of R)))
    (d : Z ⟶ (rootAlignmentLift m hm V c c').cover) (a : K) (x : Γ(Z.left, ⊤)) :
    rootPoint (u a) Z x ≫ phi.hom.hom =
      ((d ≫ (rootAlignmentLift m hm V c c').lift) ≫ j.hom.hom) *
        (rootPoint (u a) Z x ≫ Phi.hom.hom) *
        ((d ≫ (rootAlignmentLift m hm V c c').lift) ≫ j.hom.hom)⁻¹ :=
  rootPoint_eq_conjugate_of_charValue j (m a) (hv a) (u a) phi Phi (c a) (c' a)
    (q a) (hphi a) (hPhi a) Z _ (rootAlignmentLift_charValue m hm V c c' Z d a) x

/-- Independent target root characters allow simultaneous fppf local conjugation of
two families of actual root power restrictions with unit coefficients. -/
theorem exists_fppf_root_alignment
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (m : K → I → ℤ) (hm : LinearIndependent ℤ m)
    (u : K → (Ga R ⟶ G)) (v : K → (Ga R ⟶ H))
    (hv : ∀ a, IsRootParametrization j (m a) (v a))
    (phi Phi : G ⟶ H) (c c' : K → Rˣ) (q : K → ℕ)
    (hphi : ∀ a (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (u a) Z x ≫ phi.hom.hom =
        rootPoint (v a) Z (baseScalar Z (c a : R) * x ^ q a))
    (hPhi : ∀ a (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint (u a) Z x ≫ Phi.hom.hom =
        rootPoint (v a) Z (baseScalar Z (c' a : R) * x ^ q a))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ W) (a : K) (x : Γ(Z.left, ⊤)),
        rootPoint (u a) Z x ≫ phi.hom.hom =
          ((d ≫ t) ≫ j.hom.hom) * (rootPoint (u a) Z x ≫ Phi.hom.hom) *
            ((d ≫ t) ≫ j.hom.hom)⁻¹ := by
  let L := rootAlignmentLift m hm V c c'
  exact ⟨L.cover, L.projection, L.lift, L.flat, L.surjective, L.locallyOfFinitePresentation,
    rootAlignmentLift_rootPoint j m hm u v hv phi Phi c c' q hphi hPhi V⟩

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi Phi : G ⟶ H)
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  [IsFinite phi.hom.hom.left] [IsFinite Phi.hom.hom.left]

include hP hQ hweight hphi hPhi hH hmaxH

/-- Two finite homomorphisms with the same supplied root-datum isogeny and torus
map are fppf-locally conjugate on any family of independent target roots. -/
theorem exists_fppf_selected_root_alignment
    {K : Type u} [Fintype K] (beta : K → J')
    (hind : LinearIndependent ℤ (fun a => Q.root (beta a)))
    (u : K → (Ga R ⟶ G)) (v : K → (Ga R ⟶ H))
    (hu : ∀ a, IsRootParametrization i (P.root (r.indexEquiv (beta a))) (u a))
    (hv : ∀ a, IsRootParametrization j (Q.root (beta a)) (v a))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ W) (a : K) (x : Γ(Z.left, ⊤)),
        rootPoint (u a) Z x ≫ phi.hom.hom =
          ((d ≫ t) ≫ j.hom.hom) * (rootPoint (u a) Z x ≫ Phi.hom.hom) *
            ((d ≫ t) ≫ j.hom.hom)⁻¹ := by
  exact exists_fppf_root_alignment j (fun a => Q.root (beta a)) hind u v hv phi Phi
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => rootRestrictionUnit i j hP hQ r tau hweight Phi hPhi hH hmaxH
      (beta a) (hu a) (hv a))
    (fun a => r.rootFactor (beta a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight phi hphi
      hH hmaxH (beta a) (hu a) (hv a))
    (fun a => rootRestriction_unit_power_rootPoint i j hP hQ r tau hweight Phi hPhi
      hH hmaxH (beta a) (hu a) (hv a)) V

/-- In particular, target simple roots can be aligned simultaneously after an
fppf change of any test scheme. -/
theorem exists_fppf_simple_root_alignment (bQ : Q.Base)
    (u : bQ.support → (Ga R ⟶ G)) (v : bQ.support → (Ga R ⟶ H))
    (hu : ∀ a : bQ.support, IsRootParametrization i (P.root (r.indexEquiv a)) (u a))
    (hv : ∀ a : bQ.support, IsRootParametrization j (Q.root a) (v a))
    (V : Over (Spec (CommRingCat.of R))) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (b : W ⟶ V)
      (t : W ⟶ (splitTorus (Spec (CommRingCat.of R)) I').X),
      Flat b.left ∧ Surjective b.left ∧ LocallyOfFinitePresentation b.left ∧
      ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ W)
        (a : bQ.support) (x : Γ(Z.left, ⊤)),
        rootPoint (u a) Z x ≫ phi.hom.hom =
          ((d ≫ t) ≫ j.hom.hom) * (rootPoint (u a) Z x ≫ Phi.hom.hom) *
            ((d ≫ t) ≫ j.hom.hom)⁻¹ :=
  exists_fppf_selected_root_alignment i j hP hQ r tau hweight phi Phi hphi hPhi
    hH hmaxH Subtype.val bQ.linearIndepOn_root.linearIndependent u v hu hv V

end Langlands.GroupScheme.RelativeIsogeny
