import Langlands.GroupScheme.VectorCoefficientChange
import Langlands.GroupScheme.RelativeLevi.SplitFaceParabolicLinearity
import Langlands.GroupScheme.RelativeLevi.RootWeightBaseChange
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange

/-! # Linear comparison with the actual coefficient-changed face quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AutomorphicAction

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {U G : GroupScheme S} {V : GroupScheme S'}
  (c : U ⟶ G) (k : V ⟶ (GroupScheme.baseChange b).obj G) [Mono k.hom.hom]
  (e : (GroupScheme.baseChange b).obj U ≅ V)
  (he : e.hom ≫ k = (GroupScheme.baseChange b).map c)
  (χ : (Gm S).toGrp ⟶ G)
  (a : AutomorphicAction (Gm S).toGrp U)
  (ha : ∀ (T : Over S) (s : T ⟶ (Gm S).X) (x : T ⟶ U.X),
    a.act s x ≫ c.hom.hom =
      (s ≫ χ.hom.hom) * (x ≫ c.hom.hom) * (s ≫ χ.hom.hom)⁻¹)
  (a' : AutomorphicAction (Gm S').toGrp V)
  (ha' : ∀ (T : Over S') (s : T ⟶ (Gm S').X) (x : T ⟶ V.X),
    a'.act s x ≫ k.hom.hom =
      (s ≫ (Dynamic.baseChangeCocharacter b χ).hom.hom) * (x ≫ k.hom.hom) *
        (s ≫ (Dynamic.baseChangeCocharacter b χ).hom.hom)⁻¹)

include he ha ha'

/-- An actual inclusion-compatible comparison intertwines coefficient-changed conjugation. -/
theorem coefficientChange_isEquivariant_of_conjugation :
    (a.coefficientChange b).IsEquivariant a' e.hom := by
  have hf : e.hom.hom.hom ≫ k.hom.hom =
      ((GroupScheme.baseChange b).map c).hom.hom :=
    congrArg (fun f => f.hom.hom) he
  intro T s x
  apply (cancel_mono k.hom.hom).mp
  rw [Category.assoc, hf, ha', Category.assoc, hf]
  apply (baseChangePointsEquiv b G T).injective
  rw [baseChangePointsEquiv_comp, coefficientChange_act, ha,
    map_mul, map_mul, map_inv, Dynamic.baseChangePointsEquiv_baseChangeCocharacter,
    baseChangePointsEquiv_comp]

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell LocalSplitRootBaseChange RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (A : Type u) [CommRing A] [Algebra R A]

local instance quotientChangeAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance quotientChangeAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

variable
  (D : SplitParabolicFaceChart (splitTorus.baseChangeHom (K := A) G I i)
    P (fun a => baseChangeRoot A (fam a)) wt)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)

include hG hmax hP in
/-- The actual coefficient-comparison term isomorphisms preserve consecutive steps. -/
theorem step_comp_affineBaseChangeTermIso (d : ℕ) :
    (GroupScheme.baseChange (algebraBaseMap R A)).map (C.weights.step d) ≫
        (C.affineBaseChangeTermIso A D hG hmax hP d).hom =
      (C.affineBaseChangeTermIso A D hG hmax hP (d + 1)).hom ≫ D.weights.step d := by
  let b := D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) D.cocharacter)
  have hm : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨hm, rfl⟩
  apply hb.hom_ext
  rw [Category.assoc, C.affineBaseChangeTermIso_hom_comp A D hG hmax hP d,
    ← Functor.map_comp, ← Category.assoc, C.weights.step_comp_inclusion]
  rw [Category.assoc, ← Category.assoc (D.weights.step d), D.weights.step_comp_inclusion,
    C.affineBaseChangeTermIso_hom_comp A D hG hmax hP (d + 1)]

/-- The actual original quotient after coefficient change, with standard target coordinates. -/
abbrev affineBaseChangeQuotientMap (d : ℕ) :
    (GroupScheme.baseChange (algebraBaseMap R A)).obj (C.weights.groupScheme d) ⟶
      VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (C.weights.exactSupport d)) :=
  FppfQuotientComparison.coefficientQuotient
    (CommRingCat.ofHom (algebraMap R A)) (C.weights.quotientMap d)

omit D hG hmax hP [Nontrivial R] [Fintype J] in
/-- The pulled-back actual quotient has precisely the pulled-back next-term kernel. -/
theorem isFppfQuotient_affineBaseChangeQuotientMap (d : ℕ) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap R A)).map (C.weights.step d)))
      (C.affineBaseChangeQuotientMap A d) := by
  rw [SubgroupFunctor.range_baseChangeHom]
  exact FppfQuotientComparison.isFppfQuotient_coefficientQuotient _
    (C.weights.isFppfQuotient_quotientMap d)

/-- The full quotient of the pulled-back original term equals the fresh chart quotient. -/
def affineBaseChangeQuotientIso (d : ℕ) :
    VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (C.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (D.weights.exactSupport d)) :=
  FppfQuotientComparison.isoOfCompatibleTerms
    ((GroupScheme.baseChange (algebraBaseMap R A)).map (C.weights.step d)) (D.weights.step d)
    (C.isFppfQuotient_affineBaseChangeQuotientMap A d) (D.weights.isFppfQuotient_quotientMap d)
    (C.affineBaseChangeTermIso A D hG hmax hP d)
    (C.affineBaseChangeTermIso A D hG hmax hP (d + 1))
    (C.step_comp_affineBaseChangeTermIso A D hG hmax hP d)

include hG hmax hP in
/-- The actual fresh quotient isomorphism retains the actual quotient factorization. -/
theorem affineBaseChangeQuotientIso_fac (d : ℕ) :
    C.affineBaseChangeQuotientMap A d ≫
        (C.affineBaseChangeQuotientIso A D hG hmax hP d).hom =
      (C.affineBaseChangeTermIso A D hG hmax hP d).hom ≫ D.weights.quotientMap d :=
  FppfQuotientComparison.isoOfCompatibleTerms_fac _ _ _ _ _ _ _

variable (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

/-- Use the original face cocharacter on the fresh chart without changing its original weights. -/
def affineBaseChangeTargetAction (d : ℕ) :
    AutomorphicAction (Gm (Spec (CommRingCat.of A))).toGrp (D.weights.groupScheme d) := by
  let j := Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) D.cocharacter)
  let : Mono j.hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  exact D.weights.cocharacterAction
    (fam := fun a => baseChangeRoot A (fam a)) (index := fun k => (D.index k : J))
    (ch := fun a => P.root a) j D.root_comp
    (fun a T s x => (isRootParametrization_baseChangeRoot A i _ _ (hfam a)).equivariant T s x)
    C.faceCocharacter d

include hG hmax hP hfam in
/-- Actual target quotient equivariance uses the ORIGINAL multiplier and exact unscaled face height. -/
theorem affineBaseChangeTargetAction_quotient (d : ℕ) :
    (C.affineBaseChangeTargetAction A D hfam d).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1))) (D.weights.quotientMap d) := by
  let j := Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) D.cocharacter)
  let : Mono j.hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  have hheight := C.faceHeight_eq_of_affineBaseChange A D hG hmax hP
  have hw (k : Fin D.chart.dimension) :
      coPairing (P.root (D.index k)) C.faceCocharacter =
        (C.faceMultiplier : ℤ) * D.weights.weight k := by
    rw [C.facePairing, LinearMap.congr_fun hheight (P.rootSpanMem ℤ (D.index k)),
      ← D.weight_eq k]
  intro T s x
  exact D.weights.quotientMap_isEquivariant_of_realization
    (fam := fun a => baseChangeRoot A (fam a)) (index := fun k => (D.index k : J))
    (ch := fun a => P.root a) j D.root_comp
    (fun a T s x => (isRootParametrization_baseChangeRoot A i _ _ (hfam a)).equivariant T s x)
    C.faceCocharacter C.faceMultiplier hw d s x

omit [Nontrivial R] [Fintype J] in
include hfam in
/-- The fresh target action has the actual base-changed original ambient conjugation equation. -/
theorem affineBaseChangeTargetAction_ambient (d : ℕ) (T : Over (Spec (CommRingCat.of A)))
    (s : T ⟶ (Gm (Spec (CommRingCat.of A))).X) (x : T ⟶ (D.weights.groupScheme d).X) :
    (C.affineBaseChangeTargetAction A D hfam d).act s x ≫
        (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i)
            D.cocharacter)).hom.hom =
      (s ≫ (Dynamic.baseChangeCocharacter (algebraBaseMap R A)
        (AffineRegularBorel.cocharacter i C.faceCocharacter)).hom.hom) *
      (x ≫ (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i)
            D.cocharacter)).hom.hom) *
      (s ≫ (Dynamic.baseChangeCocharacter (algebraBaseMap R A)
        (AffineRegularBorel.cocharacter i C.faceCocharacter)).hom.hom)⁻¹ := by
  let j := Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) D.cocharacter)
  let : Mono j.hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  let hu : TorusEquivariant (splitTorus.baseChangeHom (K := A) G I i) (fun a => P.root a)
      (fun a => baseChangeRoot A (fam a)) :=
    fun a T s x => (isRootParametrization_baseChangeRoot A i _ _ (hfam a)).equivariant T s x
  let v := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I C.faceCocharacter)
  have h₁ := D.weights.torusAction_inclusion
    (fam := fun a => baseChangeRoot A (fam a)) (index := fun k => (D.index k : J))
    (ch := fun a => P.root a) j D.root_comp hu d (s ≫ v.hom.hom) x
  have h₂ := D.chart.torusAction_comp
    (fam := fun a => baseChangeRoot A (fam a)) (index := fun k => (D.index k : J))
    (ch := fun a => P.root a) j D.root_comp hu (s ≫ v.hom.hom)
    (x ≫ (D.weights.inclusion d).hom.hom)
  have hc := splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange
    I G i C.faceCocharacter (algebraBaseMap R A)
  change Dynamic.baseChangeCocharacter (algebraBaseMap R A)
    (AffineRegularBorel.cocharacter i C.faceCocharacter) =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I C.faceCocharacter) ≫
        splitTorus.baseChangeHom (K := A) G I i at hc
  rw [hc]
  simpa only [affineBaseChangeTargetAction, RootWeightData.cocharacterAction,
    AutomorphicAction.restrict_act, Grp.comp_hom_hom, Category.assoc, j, hu, v,
    splitTorus.RelativeCocharacterCentralizer.baseChangedTorusHom, splitTorus.baseChangeHom] using
    (congrArg (fun y => y ≫ j.hom.hom) h₁).trans h₂

include hG hmax hP hfam in
/-- The original pulled-back and fresh term actions agree through the actual term comparison. -/
theorem affineBaseChangeTermIso_isEquivariant (d : ℕ) :
    ((C.faceScalarAction hfam d).coefficientChange (algebraBaseMap R A)).IsEquivariant
      (C.affineBaseChangeTargetAction A D hfam d)
      (C.affineBaseChangeTermIso A D hG hmax hP d).hom := by
  let j := D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) D.cocharacter)
  have : Mono j.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  intro T s x
  exact AutomorphicAction.coefficientChange_isEquivariant_of_conjugation
    (algebraBaseMap R A)
    (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)) j
    (C.affineBaseChangeTermIso A D hG hmax hP d)
    (C.affineBaseChangeTermIso_hom_comp A D hG hmax hP d)
    (AffineRegularBorel.cocharacter i C.faceCocharacter)
    (C.faceScalarAction hfam d) (C.faceScalarAction_comp hfam d)
    (C.affineBaseChangeTargetAction A D hfam d)
    (C.affineBaseChangeTargetAction_ambient A D hfam d) s x

local instance affineQuotientCompact (d : ℕ) :
    QuasiCompact (C.affineBaseChangeQuotientMap A d).hom.hom.left := by
  have hAffine (n : ℕ) : IsAffine (VectorGroup.groupScheme (CommRingCat.of R) n).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R)))
    infer_instance
  have := hAffine (Nat.card (C.weights.support d))
  have := hAffine (Nat.card (C.weights.exactSupport d))
  have : QuasiCompact (C.weights.quotientMap d).hom.hom.left := by
    rw [C.weights.quotientMap_hom]
    infer_instance
  change QuasiCompact (((GroupScheme.baseChange (algebraBaseMap R A)).map
    (C.weights.quotientMap d)).hom.hom.left ≫ (VectorGroup.baseChangeIso _).hom.hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

include hG hmax hP hfam in
/-- The actual coefficient/fresh quotient comparison has a derived common positive scalar action. -/
theorem affineBaseChangeQuotientIso_isEquivariant (d : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
      (C.faceMultiplier * (d + 1))).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1)))
      (C.affineBaseChangeQuotientIso A D hG hmax hP d).hom := by
  intro T s x
  exact FppfQuotientComparison.isEquivariant_of_fac
    (C.isFppfQuotient_affineBaseChangeQuotientMap A d)
    ((C.faceScalarAction hfam d).coefficientChange (algebraBaseMap R A))
    (C.affineBaseChangeTargetAction A D hfam d) _ _
    (FppfQuotientComparison.coefficientQuotient_isEquivariant
      (CommRingCat.ofHom (algebraMap R A)) (C.faceScalarAction hfam d)
      (C.faceMultiplier * (d + 1)) (C.weights.quotientMap d) (C.quotientMap_faceScalarAction hfam d))
    (C.affineBaseChangeTargetAction_quotient A D hG hmax hP hfam d)
    (C.affineBaseChangeTermIso A D hG hmax hP d).hom
    (C.affineBaseChangeTermIso_isEquivariant A D hG hmax hP hfam d)
    _ (C.affineBaseChangeQuotientIso_fac A D hG hmax hP d) s x

include hG hmax hP hfam in
/-- Each natural scalar power is preserved by the actual fresh quotient comparison. -/
theorem affineBaseChangeQuotientIso_isEquivariant_power (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (C.affineBaseChangeQuotientIso A D hG hmax hP d).hom := by
  apply VectorGroup.isEquivariant_power_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
  exact VectorGroup.hasScalarWeight_of_equivariant _ _
    (C.affineBaseChangeQuotientIso_isEquivariant A D hG hmax hP hfam d)

/-- The actual original-to-fresh coefficient quotient comparison is linear on all coefficient algebras. -/
def affineBaseChangeLayerLinearEquiv (d : ℕ) (B : CommAlgCat.{u} (CommRingCat.of A)) :
    (Fin (Nat.card (C.weights.exactSupport d)) → B) ≃ₗ[B]
      (Fin (Nat.card (D.weights.exactSupport d)) → B) :=
  VectorGroup.linearEquivOfWeight (C.affineBaseChangeQuotientIso A D hG hmax hP d)
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (VectorGroup.hasScalarWeight_of_equivariant _ _
      (C.affineBaseChangeQuotientIso_isEquivariant A D hG hmax hP hfam d)) B

end Langlands.GroupScheme.SplitParabolicFaceChart
