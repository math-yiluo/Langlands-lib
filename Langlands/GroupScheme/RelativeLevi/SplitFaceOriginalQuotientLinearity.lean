import Langlands.GroupScheme.RelativeLevi.SplitFaceParabolicLinearity
import Langlands.GroupScheme.RelativeLevi.SplitFaceRootTransportLinearity
import Langlands.GroupScheme.RelativeLevi.SplitRadicalFaceComparison

/-! # Linearity of the original canonical quotient comparison under coordinate conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H Q Q' : GroupScheme S}

/-- An equivariant source automorphism can be removed from an equivariant composite. -/
theorem isEquivariant_of_iso_comp
    (b : AutomorphicAction H Q) (b' : AutomorphicAction H Q')
    (J : Q ≅ Q) (A : Q ≅ Q') (E : Q ⟶ Q')
    (hJ : b.IsEquivariant b J.hom) (hA : b.IsEquivariant b' A.hom)
    (hfac : J.hom ≫ E = A.hom) : b.IsEquivariant b' E := by
  have hf : J.hom.hom.hom ≫ E.hom.hom = A.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) hfac
  intro T s x
  let y := x ≫ J.inv.hom.hom
  have hy : y ≫ J.hom.hom.hom = x := by
    simp only [y, Category.assoc, iso_inv_hom_hom, Category.comp_id]
  calc
    b.act s x ≫ E.hom.hom = (b.act s y ≫ J.hom.hom.hom) ≫ E.hom.hom := by
      rw [hJ, hy]
    _ = b'.act s (y ≫ A.hom.hom.hom) := by rw [Category.assoc, hf, hA]
    _ = b'.act s ((y ≫ J.hom.hom.hom) ≫ E.hom.hom) := by
      simp only [Category.assoc, hf]
    _ = b'.act s (x ≫ E.hom.hom) := by rw [hy]

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {S : Scheme.{u}} {G G' Q Q' : GroupScheme S}

/-- Compatible actual factorizations through a full quotient respect composition. -/
theorem comp_eq_of_fac {F : SubgroupFunctor G} {q : G ⟶ Q} {q' : G' ⟶ Q'}
    (hq : RelativeRoot.IsFppfQuotient F q)
    (j : G ⟶ G) (e a : G ⟶ G') (J : Q ⟶ Q) (E A : Q ⟶ Q')
    (hJ : q ≫ J = j ≫ q) (hE : q ≫ E = e ≫ q') (hA : q ≫ A = a ≫ q')
    (hcomp : j ≫ e = a) : J ≫ E = A := by
  apply hom_ext hq
  rw [← Category.assoc, hJ, Category.assoc, hE, ← Category.assoc, hcomp, hA]

end Langlands.GroupScheme.FppfQuotientComparison

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

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
  (hPar : Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) =
    Dynamic.parabolic (AffineRegularBorel.cocharacter j wt'))
  (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
  (u : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (AffineRegularBorel.borel i wt).X)
  (hsquare : i ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom =
    precompTorus E j)

local instance originalComparisonAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance originalComparisonQuotientCompact (d : ℕ) :
    QuasiCompact (C.weights.quotientMap d).hom.hom.left := by
  have hAffine (n : ℕ) : IsAffine (VectorGroup.groupScheme (CommRingCat.of R) n).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R)))
    infer_instance
  have := hAffine (Nat.card (C.weights.support d))
  have := hAffine (Nat.card (C.weights.exactSupport d))
  rw [C.weights.quotientMap_hom]
  infer_instance

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Actual original-parabolic term action followed by original comparison is transported root comparison. -/
theorem sameParabolicTermIso_parabolic_factorization
    (e : RootPairing.Equiv P Q)
    (hr : ∀ a : J, SubgroupFunctor.range
      (fam a ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom) =
        SubgroupFunctor.range (fam' (e.indexEquiv a)))
    (hh : ∀ a : J,
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))
    (d : ℕ) :
    (C.originalParabolicTermIso hG hmax hP hfam d u).hom ≫
        (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      (C.rootTransportTermIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d).hom := by
  let g := u ≫ (AffineRegularBorel.inclusion i wt).hom.hom
  let f := G.innerIso g
  let c := C.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let b := D.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hj : (C.originalParabolicTermIso hG hmax hP hfam d u).hom ≫ c =
      c ≫ f.hom := by
    apply Grp.hom_ext
    change (C.originalParabolicTermIso hG hmax hP hfam d u).hom.hom.hom ≫
        c.hom.hom = c.hom.hom ≫ f.hom.hom.hom
    have ha := C.originalParabolicTermIso_comp hG hmax hP hfam d u
      (C.weights.groupScheme d).X (𝟙 _)
    have hb := G.comp_innerIso_hom g (C.weights.groupScheme d).X c.hom.hom
    simp only [Category.id_comp] at ha
    exact ha.trans hb.symm
  have hm : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  have hE : (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom.hom.hom ≫
      b.hom.hom = c.hom.hom :=
    congrArg (fun v => v.hom.hom)
      (C.sameParabolicTermIso_hom_comp D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
  have hA : (C.rootTransportTermIso D e f hr hh d).hom.hom.hom ≫ b.hom.hom =
      c.hom.hom ≫ f.hom.hom.hom :=
    congrArg (fun v => v.hom.hom) (C.rootTransportTermIso_hom_comp D e f hr hh d)
  apply Grp.hom_ext
  apply (cancel_mono b.hom.hom).mp
  change ((C.originalParabolicTermIso hG hmax hP hfam d u).hom.hom.hom ≫
      (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom.hom.hom) ≫
        b.hom.hom = (C.rootTransportTermIso D e f hr hh d).hom.hom.hom ≫ b.hom.hom
  rw [Category.assoc, hE, hA]
  exact congrArg (fun v => v.hom.hom) hj

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Full fppf quotient uniqueness preserves the actual parabolic factorization. -/
theorem sameParabolicQuotientIso_parabolic_factorization
    (e : RootPairing.Equiv P Q)
    (hr : ∀ a : J, SubgroupFunctor.range
      (fam a ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom) =
        SubgroupFunctor.range (fam' (e.indexEquiv a)))
    (hh : ∀ a : J,
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))
    (d : ℕ) :
    (C.originalParabolicQuotientIso hG hmax hP hfam d u).hom ≫
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      (C.rootTransportQuotientIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d).hom := by
  exact FppfQuotientComparison.comp_eq_of_fac (C.weights.isFppfQuotient_quotientMap d)
    _ _ _ _ _ _
    (C.originalParabolicQuotientIso_fac hG hmax hP hfam d u)
    (C.quotientMap_comp_sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
    (C.quotientMap_comp_rootTransportQuotientIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d)
    (C.sameParabolicTermIso_parabolic_factorization D hG hmax hmax' hP hQ hfam hfam'
      hU hPar u e hr hh d)

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- The original quotient comparison is inverse parabolic action followed by transported comparison. -/
theorem sameParabolicQuotientIso_eq_parabolic_inv_comp_rootTransport
    (e : RootPairing.Equiv P Q)
    (hr : ∀ a : J, SubgroupFunctor.range
      (fam a ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom) =
        SubgroupFunctor.range (fam' (e.indexEquiv a)))
    (hh : ∀ a : J,
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))
    (d : ℕ) :
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      (C.originalParabolicQuotientIso hG hmax hP hfam d u).inv ≫
        (C.rootTransportQuotientIso D e
          (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d).hom := by
  rw [← C.sameParabolicQuotientIso_parabolic_factorization D hG hmax hmax' hP hQ
    hfam hfam' hU hPar u e hr hh d, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit [Nontrivial R] in
include hfam hfam' in
/-- The transported root quotient has the actual common scalar action. -/
theorem rootTransportQuotientIso_isEquivariant_of_parabolicRootTransport
    (e : RootPairing.Equiv P Q)
    (hr : ∀ a : J, SubgroupFunctor.range
      (fam a ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom) =
        SubgroupFunctor.range (fam' (e.indexEquiv a)))
    (hh : ∀ a : J,
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))
    (hs : i ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom =
      precompTorus e.weightEquiv j) (d : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
      (C.faceMultiplier * (d + 1))).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1)))
      (C.rootTransportQuotientIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d).hom := by
  intro T s x
  exact FppfQuotientComparison.isEquivariant_of_fac
    (C.weights.isFppfQuotient_quotientMap d)
    (C.restrictedAction hfam C.realizingTorusCocharacter d)
    (D.restrictedAction hfam' (C.transportedRealizingCocharacter e) d)
    _ _ (C.realizingAction_quotient_equivariant hfam d)
    (C.transportedAction_quotient_equivariant D e hh hfam' d)
    (C.rootTransportTermIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d).hom
    (C.rootTransportTermIso_isEquivariant D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh hfam hfam' hs d)
    _ (C.quotientMap_comp_rootTransportQuotientIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d) s x

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Remove actual parabolic conjugation from an equivariant full-root transport. -/
theorem sameParabolicQuotientIso_isEquivariant_of_parabolicRootTransport
    (e : RootPairing.Equiv P Q)
    (hr : ∀ a : J, SubgroupFunctor.range
      (fam a ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom) =
        SubgroupFunctor.range (fam' (e.indexEquiv a)))
    (hh : ∀ a : J,
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))
    (hs : i ≫ (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)).hom =
      precompTorus e.weightEquiv j) (d : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
      (C.faceMultiplier * (d + 1))).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1)))
      (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom := by
  intro T s x
  exact AutomorphicAction.isEquivariant_of_iso_comp _ _
    (C.originalParabolicQuotientIso hG hmax hP hfam d u)
    (C.rootTransportQuotientIso D e (G.innerIso (u ≫ (AffineRegularBorel.inclusion i wt).hom.hom)) hr hh d)
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom
    (C.originalParabolicQuotientIso_isEquivariant hG hmax hP hfam d u)
    (C.rootTransportQuotientIso_isEquivariant_of_parabolicRootTransport D hfam hfam' u e hr hh hs d)
    (C.sameParabolicQuotientIso_parabolic_factorization D hG hmax hmax' hP hQ hfam hfam'
      hU hPar u e hr hh d) s x

include hG hmax hmax' hP hQ hfam hfam' hU hPar hsquare in
/-- An actual coordinate conjugator in the original parabolic makes the ORIGINAL
canonical quotient comparison scalar-equivariant. No linearity premise is supplied. -/
theorem sameParabolicQuotientIso_isEquivariant_of_coordinateConjugacy (d : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
      (C.faceMultiplier * (d + 1))).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1)))
      (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom := by
  let g := u ≫ (AffineRegularBorel.inclusion i wt).hom.hom
  let f := G.innerIso g
  let e : RootPairing.Equiv P Q :=
    rootDatumEquivOfCoordinateTorusIso E f hsquare hG hG hmax hmax' hP hQ
  have hr (a : J) : SubgroupFunctor.range (fam a ≫ f.hom) =
      SubgroupFunctor.range (fam' (e.indexEquiv a)) :=
    range_root_comp_coordinateTorusIso E f hsquare hG hG hmax hmax' hP hQ hfam hfam' a
  have hg : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).carrier
      (Over.mk (𝟙 _)) := by
    rw [← (Dynamic.Affine.isRepresentedBy_parabolicHom
      (AffineRegularBorel.cocharacter i wt)).2]
    exact SubgroupFunctor.mem_range.mpr ⟨u, rfl⟩
  have hnU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i wt)).IsNormalizedBy
      (Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)) := by
    rw [← C.represented.2]
    exact C.range_inclusion_isNormalizedBy_originalParabolic hG hmax hP hfam 0
  have hUf : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
      (Dynamic.unipotent (AffineRegularBorel.cocharacter j wt')).comap f.hom := by
    rw [← hU]
    exact (SubgroupFunctor.comap_innerIso_eq_of_isNormalizedBy hnU hg).symm
  have hh (a : J) :
      faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
        faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)) :=
    C.faceHeight_root_eq_of_rootSigns D e hG hmax' hQ
      (coPairing_pos_iff_of_rootTransport e f hr hfam hfam' hUf)
      (coPairing_zero_iff_of_rootTransport e f hr hfam hfam' hUf) a
  have he : e.weightEquiv = E := by
    apply LinearEquiv.ext
    intro m
    rw [RootPairing.Equiv.weightEquiv_apply]
    exact LinearMap.congr_fun
      (rootDatumEquivOfCoordinateTorusIso_weightMap E f hsquare hG hG hmax hmax' hP hQ) m
  have hs : i ≫ f.hom = precompTorus e.weightEquiv j := by
    rw [he]
    exact hsquare
  intro T s x
  exact C.sameParabolicQuotientIso_isEquivariant_of_parabolicRootTransport D
    hG hmax hmax' hP hQ hfam hfam' hU hPar u e hr hh hs d s x

include hG hmax hmax' hP hQ hfam hfam' hU hPar hsquare in
/-- The actual ORIGINAL canonical quotient comparison has its common scalar weight. -/
theorem sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy (d : ℕ) :
    VectorGroup.HasScalarWeight
      (VectorGroup.pointTransformation
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)
      (C.faceMultiplier * (d + 1)) :=
  VectorGroup.hasScalarWeight_of_equivariant _ _
    (C.sameParabolicQuotientIso_isEquivariant_of_coordinateConjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar E u hsquare d)

/-- The original ambient-compatible quotient comparison is linear over every coefficient algebra. -/
def sameParabolicLayerLinearEquivOfCoordinateConjugacy (d : ℕ)
    (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (Fin (Nat.card (C.weights.exactSupport d)) → A) ≃ₗ[A]
      (Fin (Nat.card (D.weights.exactSupport d)) → A) :=
  VectorGroup.linearEquivOfWeight
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar E u hsquare d) A

include hG hmax hmax' hP hQ hfam hfam' hU hPar hsquare in
/-- One base-ring matrix represents the ORIGINAL actual canonical quotient comparison. -/
theorem sameParabolicQuotientIso_eq_matrixHom_of_coordinateConjugacy (d : ℕ) :
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar E u hsquare d)

include hG hmax hmax' hP hQ hfam hfam' hU hPar hsquare in
/-- The original comparison has the same matrix formula on every scheme test. -/
theorem coordinates_sameParabolicQuotientIso_of_coordinateConjugacy (d : ℕ)
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of R)
      (Nat.card (C.weights.exactSupport d))).X) :
    (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (D.weights.exactSupport d)) T
      (x ≫ (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom.hom.hom)).toAdd =
      (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)).map
          (scalarMap T) *ᵥ
      (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) T x).toAdd :=
  VectorGroup.coordinates_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar E u hsquare d) T x

end Langlands.GroupScheme.SplitParabolicFaceChart
