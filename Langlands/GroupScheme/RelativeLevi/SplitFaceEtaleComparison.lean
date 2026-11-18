import Langlands.GroupScheme.RelativeLevi.RootWeightBaseChange
import Langlands.GroupScheme.RelativeLevi.SplitFaceCoordinateConjugacy
import Langlands.GroupScheme.Torus.EtaleParabolicCoordinateConjugacy
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Torus.FibrewiseMaximalBaseChange
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality

/-! # Canonical face-term comparison across arbitrary maximal split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell LocalSplitRootBaseChange RelativeUnipotent

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  [DecidableEq I] [DecidableEq I']
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ G)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt) (D : SplitParabolicFaceChart j Q fam' wt')
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' G j Q)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter j wt'))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

section CoefficientConjugacy

variable (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A]

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

include hG hmax hmax' hP hQ hfam hfam' hU in
/-- After coefficient extension, an actual coordinate conjugator inside the
original parabolic identifies the pullbacks of all original terms. -/
theorem range_baseChange_eq_of_coordinateConjugacy
    (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X)
    (hg : g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange
      (algebraBaseMap R A)).carrier _)
    (hsquare : ((splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
        (GroupScheme.baseChange (algebraBaseMap R A)).map i) ≫
          (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).innerIso g).hom =
      CommGroupScheme.groupHom (splitTorus.exponentEquivIso (Spec (CommRingCat.of A)) E).hom ≫
        ((splitTorus.baseChangeIso (algebraBaseMap R A) I').inv ≫
          (GroupScheme.baseChange (algebraBaseMap R A)).map j)) (d : ℕ) :
    (SubgroupFunctor.range (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter))).baseChange (algebraBaseMap R A) =
    (SubgroupFunctor.range (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter j D.cocharacter))).baseChange (algebraBaseMap R A) := by
  classical
  let b := algebraBaseMap R A
  let GA := (GroupScheme.baseChange b).obj G
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let jA := splitTorus.baseChangeHom (K := A) G I' j
  have hGA : IsReductive GA := hG.baseChange b
  let : Smooth G.X.hom := hG.smooth
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I G i b hmax
  have hmaxA' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') jA :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I' G j b hmax'
  have hPA : IsFibrewiseRootDatumOf I GA iA P := hP.baseChange_implicit
  have hQA : IsFibrewiseRootDatumOf I' GA jA Q := hQ.baseChange_implicit
  have hfA (a : J) : IsRootParametrization iA (P.root a) (baseChangeRoot A (fam a)) :=
    isRootParametrization_baseChangeRoot A i (P.root a) (fam a) (hfam a)
  have hfA' (a : J') : IsRootParametrization jA (Q.root a) (baseChangeRoot A (fam' a)) :=
    isRootParametrization_baseChangeRoot A j (Q.root a) (fam' a) (hfam' a)
  let CA : SplitParabolicFaceChart iA P (fun a => baseChangeRoot A (fam a)) wt :=
    Classical.choice (nonempty_splitParabolicFaceChart hGA hmaxA hPA hfA)
  let DA : SplitParabolicFaceChart jA Q (fun a => baseChangeRoot A (fam' a)) wt' :=
    Classical.choice (nonempty_splitParabolicFaceChart hGA hmaxA' hQA hfA')
  have hc : Dynamic.baseChangeCocharacter b (AffineRegularBorel.cocharacter i wt) =
      AffineRegularBorel.cocharacter iA wt :=
    splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange I G i wt b
  have hc' : Dynamic.baseChangeCocharacter b (AffineRegularBorel.cocharacter j wt') =
      AffineRegularBorel.cocharacter jA wt' :=
    splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange I' G j wt' b
  have hUA : Dynamic.unipotent (AffineRegularBorel.cocharacter iA wt) =
      Dynamic.unipotent (AffineRegularBorel.cocharacter jA wt') := by
    rw [← hc, ← hc', Dynamic.unipotent_baseChange, Dynamic.unipotent_baseChange, hU]
  have hgA : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter iA wt)).carrier _ := by
    rw [← hc, Dynamic.parabolic_baseChange]
    exact hg
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    C.range_affineBaseChange_inclusion_eq A CA hG hmax hP,
    D.range_affineBaseChange_inclusion_eq A DA hG hmax' hQ]
  exact CA.range_inclusion_eq_of_coordinateConjugacy DA hGA hmaxA hmaxA' hPA hQA hfA hfA'
    hUA E g hgA hsquare d

end CoefficientConjugacy

include hG hmax hmax' hP hQ hfam hfam' hU in
/-- The same comparison for an arbitrary specified affine base map, using its
induced coefficient-algebra structure without changing the actual pullback. -/
theorem range_affineBaseChange_eq_of_coordinateConjugacy
    (A : CommRingCat.{u}) [Nontrivial A]
    (b : Spec A ⟶ Spec (CommRingCat.of R))
    (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (g : Over.mk (𝟙 (Spec A)) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg : g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange b).carrier _)
    (hsquare : ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom =
      CommGroupScheme.groupHom (splitTorus.exponentEquivIso (Spec A) E).hom ≫
        ((splitTorus.baseChangeIso b I').inv ≫ (GroupScheme.baseChange b).map j)) (d : ℕ) :
    (SubgroupFunctor.range (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter))).baseChange b =
    (SubgroupFunctor.range (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter j D.cocharacter))).baseChange b := by
  let : Algebra R A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R A = b := Spec.map_preimage b
  let F (a : Spec A ⟶ Spec (CommRingCat.of R)) : Prop :=
    ∀ (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
      (g : Over.mk (𝟙 (Spec A)) ⟶ ((GroupScheme.baseChange a).obj G).X),
      g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange a).carrier _ →
      ((splitTorus.baseChangeIso a I).inv ≫ (GroupScheme.baseChange a).map i) ≫
          (((GroupScheme.baseChange a).obj G).innerIso g).hom =
        CommGroupScheme.groupHom (splitTorus.exponentEquivIso (Spec A) E).hom ≫
          ((splitTorus.baseChangeIso a I').inv ≫ (GroupScheme.baseChange a).map j) →
      (SubgroupFunctor.range (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter))).baseChange a =
      (SubgroupFunctor.range (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter))).baseChange a
  have h : F (algebraBaseMap R A) := by
    intro E g hg hsquare
    exact C.range_baseChange_eq_of_coordinateConjugacy D hG hmax hmax' hP hQ hfam hfam' hU
      A E g hg hsquare d
  exact (Eq.mp (congrArg F hb) h) E g hg hsquare

variable (hPar : Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) =
  Dynamic.parabolic (AffineRegularBorel.cocharacter j wt'))

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Every original unscaled face term is independent of the maximal split
torus and all full root/chart choices, when the actual original parabolic
and contracting functors agree. Equality holds on every scheme test. -/
theorem range_inclusion_eq_of_sameParabolic (d : ℕ) :
    SubgroupFunctor.range (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)) =
    SubgroupFunctor.range (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter j D.cocharacter)) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let N (s : Spec (CommRingCat.of R)) :=
    splitTorus.etaleParabolicCoordinateConjugacyAt G i j wt wt' hmax hmax' hPar s
  let cover : (Spec (CommRingCat.of R)).Cover.{u} (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers (P := @Etale) (Spec (CommRingCat.of R))
      (fun s => Spec (N s).ring) (fun s => (N s).projection)
      (fun s => ⟨s, (N s).mem_range.choose, (N s).mem_range.choose_spec⟩)
      (fun s => (N s).etale)
  have hm : Mono (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom := by
    change Mono ((C.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hm' : Mono (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter j D.cocharacter)).hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  letI := hm
  letI := hm'
  apply (SubgroupFunctor.range_eq_iff_baseChange_etaleCover cover _ _).mpr
  intro s
  let : Nontrivial (N s).ring := (N s).mem_range.choose.nontrivial
  exact C.range_affineBaseChange_eq_of_coordinateConjugacy D hG hmax hmax' hP hQ hfam hfam' hU
    (N s).ring (N s).projection (N s).coordinateMap (N s).conjugator
    (N s).mem_parabolic (N s).square d

/-- The actual comparison of original terms for arbitrary maximal split
tori presenting the same parabolic and contracting subgroup. -/
def sameParabolicTermIso (d : ℕ) : C.weights.groupScheme d ≅ D.weights.groupScheme d := by
  let c := C.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let b := D.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono c.hom.hom := by
    change Mono ((C.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (C.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter)).1
  have hm' : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  have hc : (SubgroupFunctor.range c).IsRepresentedBy c := ⟨hm, rfl⟩
  exact hc.isoOfIsRepresentedBy ⟨hm',
    (C.range_inclusion_eq_of_sameParabolic D hG hmax hmax' hP hQ hfam hfam' hU hPar d).symm⟩

/-- The resulting isomorphism retains the original ambient inclusions. -/
theorem sameParabolicTermIso_hom_comp (d : ℕ) :
    (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom ≫
      (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)) =
      C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter i C.cocharacter) := by
  unfold sameParabolicTermIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.SplitParabolicFaceChart
