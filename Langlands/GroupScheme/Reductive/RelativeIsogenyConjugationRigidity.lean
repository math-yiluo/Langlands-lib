import Langlands.GroupScheme.Reductive.RelativeIsogenySimpleRootPower
import Langlands.GroupScheme.Reductive.TorusConjugationGeneratorComparison

/-! # Whole-group conjugation from actual simple-root restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open LocalSplitCell

namespace splitTorus

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {I I' : Type u} [Fintype I] [Fintype I']

/-- Pull back a map of coordinate tori and restore the standard coordinates. -/
def coordinateBaseChangeHom
    (tau : commGroupScheme S I ⟶ commGroupScheme S I') :
    commGroupScheme S' I ⟶ commGroupScheme S' I' :=
  (commBaseChangeIso b I).inv ≫ (CommGroupScheme.baseChange b).map tau ≫
    (commBaseChangeIso b I').hom

/-- A specified integral character formula is preserved by scalar extension. -/
theorem coordinateBaseChangeHom_character
    (tau : commGroupScheme S I ⟶ commGroupScheme S I')
    (w : (I' → ℤ) →ₗ[ℤ] (I → ℤ))
    (h : ∀ m, tau ≫ exponentCharacter S I' m = exponentCharacter S I (w m))
    (m : I' → ℤ) :
    coordinateBaseChangeHom b tau ≫ exponentCharacter S' I' m =
      exponentCharacter S' I (w m) := by
  unfold coordinateBaseChangeHom
  rw [Category.assoc, Category.assoc, exponentCharacter_baseChange,
    characterLattice.baseChange_apply, ← Functor.map_comp_assoc, h,
    ← characterLattice.baseChange_apply, ← exponentCharacter_baseChange,
    Iso.inv_hom_id_assoc]

variable {R : Type u} [CommRing R]
  (A : Type u) [CommRing A] [Algebra R A]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The common torus square survives base change with standard torus coordinates. -/
theorem coordinateBaseChangeHom_square
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (tau : commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      commGroupScheme (Spec (CommRingCat.of R)) I')
    (f : G ⟶ H) (h : i ≫ f = CommGroupScheme.groupHom tau ≫ j) :
    baseChangeHom (K := A) G I i ≫ (baseChange (algebraBaseMap R A)).map f =
      CommGroupScheme.groupHom (coordinateBaseChangeHom (algebraBaseMap R A) tau) ≫
        baseChangeHom (K := A) H I' j := by
  change (baseChangeIso (algebraBaseMap R A) I).inv ≫
      (baseChange (algebraBaseMap R A)).map i ≫
      (baseChange (algebraBaseMap R A)).map f =
    ((baseChangeIso (algebraBaseMap R A) I).inv ≫
      (baseChange (algebraBaseMap R A)).map (CommGroupScheme.groupHom tau) ≫
      (baseChangeIso (algebraBaseMap R A) I').hom) ≫
      (baseChangeIso (algebraBaseMap R A) I').inv ≫
      (baseChange (algebraBaseMap R A)).map j
  rw [← Functor.map_comp, h, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end splitTorus

/-- Pullback followed by an inner automorphism preserves finiteness. -/
theorem isFinite_torusConjugateAlgebraHom
    {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {V : Over (Spec (CommRingCat.of R))}
    (A : Type u) [CommRing A] [Algebra R A]
    (j : T.toGrp ⟶ H) (F : G ⟶ H) [hFfinite : IsFinite F.hom.hom.left]
    (t : V ⟶ T.X) (a : fieldPoint R A ⟶ V) :
    IsFinite (torusConjugateAlgebraHom A j F t a).hom.hom.left := by
  let p := (baseChangePointsEquiv (algebraBaseMap R A) H (𝟙_ _)).symm
    (a ≫ t ≫ j.hom.hom)
  have : IsFinite ((baseChange (algebraBaseMap R A)).map F).hom.hom.left :=
    MorphismProperty.of_isPullback
      (baseChange_map_isPullback (algebraBaseMap R A) F).flip inferInstance
  have : IsIso ((((baseChange (algebraBaseMap R A)).obj H).innerIso p).hom).hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map
      (((baseChange (algebraBaseMap R A)).obj H).innerIso p).hom))
  change IsFinite (((baseChange (algebraBaseMap R A)).map F).hom.hom.left ≫
    ((((baseChange (algebraBaseMap R A)).obj H).innerIso p).hom).hom.hom.left)
  infer_instance

section SimpleRestrictions

attribute [local irreducible] torusConjugateAlgebraHom

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  [Finite J] [Finite J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]
  {p : ℕ} {V : Over (Spec (CommRingCat.of R))}

set_option maxHeartbeats 2000000 in
/-- Finite maps with supplied compatible root data are conjugate on the whole
source once their conjugated maps agree on the torus and positive simple roots
for every local coefficient algebra. -/
theorem TorusConjugates.of_simpleRootRestrictions
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m))
    (phi Phi : G ⟶ H) [hfinphi : IsFinite phi.hom.hom.left] [hfinPhi : IsFinite Phi.hom.hom.left]
    (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (b : P.Base) (u : J → (Ga R ⟶ G)) (v : J' → (Ga R ⟶ H))
    (hu : ∀ α ∈ b.support,
      IsRootParametrization i (P.root α) (u α) ∧
      IsRootParametrization i (P.root (P.reflectionPerm α α)) (u (P.reflectionPerm α α)))
    (hv : ∀ α ∈ b.support,
      IsRootParametrization j (Q.root (r.indexEquiv.symm α)) (v (r.indexEquiv.symm α)) ∧
      IsRootParametrization j
        (Q.root (Q.reflectionPerm (r.indexEquiv.symm α) (r.indexEquiv.symm α)))
        (v (Q.reflectionPerm (r.indexEquiv.symm α) (r.indexEquiv.symm α))))
    (hw : ∀ α ∈ b.support, IsWeylPoint i (rootWeylPoint P u α) (P.reflection α))
    (t : V ⟶ (splitTorus.commGroupScheme _ I').X)
    (he : ∀ α ∈ b.support, TorusConjugatesOnRoot j phi Phi t (u α)) :
    TorusConjugates j phi Phi t := by
  classical
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  apply TorusConjugates.of_localAlgebraHom j phi Phi t
  intro A _ _ _ a
  have heA (α : J) (hα : α ∈ b.support) :
      baseChangeRoot A (u α) ≫ (baseChange (algebraBaseMap R A)).map phi =
        baseChangeRoot A (u α) ≫ torusConjugateAlgebraHom A j Phi t a :=
    torusConjugateAlgebraHom_root (R := R) (G := G) (H := H)
      (T := splitTorus.commGroupScheme _ I') (V := V)
      j phi Phi t (u α) (he α hα) A a
  have hPA := hP.baseChange_implicit (A := A)
  have hQA := hQ.baseChange_implicit (A := A)
  have hGA := hG.baseChange (algebraBaseMap R A)
  have hHA := hH.baseChange (algebraBaseMap R A)
  have hmaxGA := splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmaxG (A := A)
  have hmaxHA := splitTorus.isFibrewiseMaximalTorus_baseChangeHom I' H j hmaxH (A := A)
  let hGAff : IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let hHAff : IsAffineHom ((baseChange (algebraBaseMap R A)).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  let hfinphiA : IsFinite ((baseChange (algebraBaseMap R A)).map phi).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (baseChange_map_isPullback (algebraBaseMap R A) phi).flip inferInstance
  let hfinconjA : IsFinite (torusConjugateAlgebraHom A j Phi t a).hom.hom.left :=
    isFinite_torusConjugateAlgebraHom (hFfinite := hfinPhi) A j Phi t a
  refine @RelativeIsogeny.hom_ext_of_simpleRootRestrictions
    A _ I I' J J' _ _ _ _
    ((baseChange (algebraBaseMap R A)).obj G) ((baseChange (algebraBaseMap R A)).obj H)
    P Q _ _ p _ _ _ hGAff hHAff
    (splitTorus.baseChangeHom (K := A) G I i)
    (splitTorus.baseChangeHom (K := A) H I' j)
    hPA hQA r (splitTorus.coordinateBaseChangeHom (algebraBaseMap R A) tau) ?_
    ((baseChange (algebraBaseMap R A)).map phi) ?_ hHA hmaxHA
    hfinphiA (torusConjugateAlgebraHom A j Phi t a) hfinconjA ?_ hGA ?_ ?_ hmaxGA
    b (fun α => baseChangeRoot A (u α)) (fun β => baseChangeRoot A (v β)) ?_ ?_ ?_ ?_
  · exact splitTorus.coordinateBaseChangeHom_character (algebraBaseMap R A) tau r.weightMap hweight
  · exact splitTorus.coordinateBaseChangeHom_square A i j tau phi hphi
  · exact (torusConjugateAlgebraHom_torus j Phi t i (CommGroupScheme.groupHom tau) hPhi A a).trans
      (splitTorus.coordinateBaseChangeHom_square A i j tau Phi hPhi)
  · exact (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm).comp
      (hi.baseChange (algebraBaseMap R A))
  · exact (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso (algebraBaseMap R A) I').symm).comp
      (hj.baseChange (algebraBaseMap R A))
  · exact fun α hα => ⟨isRootParametrization_baseChangeRoot A i _ _ (hu α hα).1,
      isRootParametrization_baseChangeRoot A i _ _ (hu α hα).2⟩
  · exact fun α hα => ⟨isRootParametrization_baseChangeRoot A j _ _ (hv α hα).1,
      isRootParametrization_baseChangeRoot A j _ _ (hv α hα).2⟩
  · exact fun α hα => isWeylPoint_baseChange A (hw α hα)
  · exact heA

end SimpleRestrictions

end Langlands.GroupScheme
