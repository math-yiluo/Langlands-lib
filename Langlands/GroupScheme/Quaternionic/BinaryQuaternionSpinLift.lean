import Langlands.GroupScheme.Quaternionic.AmbientBinaryQuaternion
import Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedStatement
import Langlands.GroupScheme.CentralSimpleSplitNormOne
import Langlands.GroupScheme.SimplyConnected.HomLift
import Langlands.GroupScheme.Quaternionic.HyperbolicNormSquareTorus
import Langlands.GroupScheme.SpecialLinearBinaryDynamicRoots

/-! # Separate binary quaternionic homomorphisms into a supplied spin cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S C : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- A homomorphism from a simply connected group has a unique lift through a supplied spin cover. -/
theorem existsUnique_liftHom (hπ : σ.IsSpinCover q π) (hC : IsSimplyConnected C)
    (f : C ⟶ σ.isometryGroup q) : ∃! a : C ⟶ S, a ≫ π = f := by
  let := hπ.smooth
  let := hC.isSemisimple.isConnectedReductive.connectedSpace
  obtain ⟨p, hp, hpp⟩ := hπ.exists_centralIsogeny
  let a := SimplyConnectedHomLift.liftHom
    (IdentityComponent.factor (σ.isometryGroup q) f) p hp hC
    hπ.isSimplyConnected.isSemisimple.isConnectedReductive (by infer_instance)
  have ha : a ≫ p = IdentityComponent.factor (σ.isometryGroup q) f :=
    SimplyConnectedHomLift.liftHom_comp _ _ _ _ _ _
  have haf : a ≫ π = f := by
    rw [← hpp, ← Category.assoc, ha, IdentityComponent.factor_identityComponentι]
  refine ⟨a, haf, ?_⟩
  intro b hb
  apply hp.cancel_of_connectedReductive hC.isSemisimple.isConnectedReductive
  apply (cancel_mono (identityComponentι (σ.isometryGroup q))).mp
  rw [Category.assoc, Category.assoc, hpp, hb, haf]

/-- The lift into the actual supplied spin group, without choosing a new covering group. -/
def liftHom (hπ : σ.IsSpinCover q π) (hC : IsSimplyConnected C)
    (f : C ⟶ σ.isometryGroup q) : C ⟶ S :=
  (hπ.existsUnique_liftHom hC f).choose

/-- The lift has exactly the prescribed isometry composite. -/
@[reassoc] theorem liftHom_comp (hπ : σ.IsSpinCover q π) (hC : IsSimplyConnected C)
    (f : C ⟶ σ.isometryGroup q) : hπ.liftHom hC f ≫ π = f :=
  (hπ.existsUnique_liftHom hC f).choose_spec.1

/-- Compatibility with the isometry map uniquely determines this lift. -/
theorem liftHom_unique (hπ : σ.IsSpinCover q π) (hC : IsSimplyConnected C)
    (f : C ⟶ σ.isometryGroup q) (a : C ⟶ S) (ha : a ≫ π = f) :
    a = hπ.liftHom hC f :=
  (hπ.existsUnique_liftHom hC f).choose_spec.2 a ha

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

/-- The degree-two norm-one premise also supplies simple connectedness of actual split SL₂. -/
theorem specialLinear_simplyConnected
    (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
    (K : Type u) [Field K] :
    IsSimplyConnected (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)) :=
  IsSimplyConnected.of_iso (CentralSimpleUnits.binaryMatrixNormOneIso K).symm
    (hsc K (Matrix (Fin 2) (Fin 2) K) (CentralSimpleUnits.binaryMatrix_finrank K))

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- Inclusion of the first factor of the actual binary product. -/
def firstFactor : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K) ⟶
    BinaryScheme.groupScheme (K := K) (D := D) :=
  Grp.homMk (lift (𝟙 _) (toUnit _ ≫ η[(CentralSimpleUnits.normOne K D).X]))

/-- Inclusion of the norm-one factor of the actual binary product. -/
def secondFactor : CentralSimpleUnits.normOne K D ⟶
    BinaryScheme.groupScheme (K := K) (D := D) :=
  Grp.homMk
    (lift (toUnit _ ≫ η[(SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X]) (𝟙 _))

/-- The first inclusion has coordinates `(g,1)` on every relative test. -/
theorem firstFactor_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X) :
    BinaryScheme.pointsEquiv T (x ≫ (firstFactor (K := K) (D := D)).hom.hom) =
      (SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T x, 1) := by
  apply Prod.ext
  · change SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T
      ((x ≫ lift (𝟙 _) (1 : _ ⟶ (CentralSimpleUnits.normOne K D).X)) ≫ fst _ _) = _
    rw [Category.assoc, lift_fst, Category.comp_id]
  · change CentralSimpleUnits.normOnePointsEquiv K D T
      ((x ≫ lift (𝟙 _) (1 : _ ⟶ (CentralSimpleUnits.normOne K D).X)) ≫ snd _ _) = 1
    rw [Category.assoc, lift_snd, MonObj.comp_one, map_one]

/-- The second inclusion has coordinates `(1,b)` on every relative test. -/
theorem secondFactor_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (CentralSimpleUnits.normOne K D).X) :
    BinaryScheme.pointsEquiv T (x ≫ (secondFactor (K := K) (D := D)).hom.hom) =
      (1, CentralSimpleUnits.normOnePointsEquiv K D T x) := by
  apply Prod.ext
  · change SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T
      ((x ≫ lift (1 : _ ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X)
        (𝟙 _)) ≫ fst _ _) = 1
    rw [Category.assoc, lift_fst, MonObj.comp_one, map_one]
  · change CentralSimpleUnits.normOnePointsEquiv K D T
      ((x ≫ lift (1 : _ ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X)
        (𝟙 _)) ≫ snd _ _) = _
    rw [Category.assoc, lift_snd, Category.comp_id]

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- The actual SL₂ action lifted separately into the supplied spin group. -/
def specialLinear : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K) ⟶ S :=
  hπ.liftHom (specialLinear_simplyConnected hsc K)
    (firstFactor ≫ AmbientBinaryScheme.isometryHom σ hdim hsym h)

/-- The actual norm-one action lifted separately into the supplied spin group. -/
def normOne : CentralSimpleUnits.normOne K D ⟶ S :=
  hπ.liftHom (hsc K D hdim)
    (secondFactor ≫ AmbientBinaryScheme.isometryHom σ hdim hsym h)

/-- The SL₂ lift has the prescribed ambient action as its composite. -/
@[reassoc] theorem specialLinear_comp :
    specialLinear σ hdim hsym h hπ hsc ≫ π =
      firstFactor ≫ AmbientBinaryScheme.isometryHom σ hdim hsym h :=
  hπ.liftHom_comp _ _

/-- The norm-one lift has the prescribed ambient action as its composite. -/
@[reassoc] theorem normOne_comp :
    normOne σ hdim hsym h hπ hsc ≫ π =
      secondFactor ≫ AmbientBinaryScheme.isometryHom σ hdim hsym h :=
  hπ.liftHom_comp _ _

/-- The scalar cocharacter in the supplied spin group is the diagonal of its SL₂ lift. -/
def scalar : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S :=
  SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
    specialLinear σ hdim hsym h hπ hsc

/-- The scalar lift has the actual diagonal binary action as its isometry composite. -/
@[reassoc] theorem scalar_comp :
    scalar σ hdim hsym h hπ hsc ≫ π =
      SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
        firstFactor ≫ AmbientBinaryScheme.isometryHom σ hdim hsym h := by
  rw [scalar, Category.assoc, specialLinear_comp]

/-- The SL₂ lift recovers its entire ambient matrix on every relative test scheme. -/
theorem specialLinear_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      (((x ≫ (specialLinear σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryAction.normOneAction σ hdim hsym (BinaryScheme.coefficients T)
          (SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T x, 1)) := by
  have hc : (x ≫ (specialLinear σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom =
      (x ≫ firstFactor.hom.hom) ≫
        (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, specialLinear_comp,
      Grp.comp_hom_hom, ← Category.assoc]
  rw [hc, AmbientBinaryScheme.isometryHom_points]
  change HyperbolicScheme.extendUnits h _ (BinaryAction.normOneAction σ hdim hsym _
    (BinaryScheme.pointsEquiv T (x ≫ firstFactor.hom.hom))) = _
  rw [firstFactor_points]

/-- The norm-one lift recovers its prescribed product action on every relative test scheme. -/
theorem normOne_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (CentralSimpleUnits.normOne K D).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      (((x ≫ (normOne σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryAction.normOneAction σ hdim hsym (BinaryScheme.coefficients T)
          (1, CentralSimpleUnits.normOnePointsEquiv K D T x)) := by
  have hc : (x ≫ (normOne σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom =
      (x ≫ secondFactor.hom.hom) ≫
        (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, normOne_comp,
      Grp.comp_hom_hom, ← Category.assoc]
  rw [hc, AmbientBinaryScheme.isometryHom_points]
  change HyperbolicScheme.extendUnits h _ (BinaryAction.normOneAction σ hdim hsym _
    (BinaryScheme.pointsEquiv T (x ≫ secondFactor.hom.hom))) = _
  rw [secondFactor_points]

/-- The diagonal restriction of the binary action is the actual hyperbolic Levi matrix. -/
theorem diagonal_normOne_action (R : Type u) [CommRing R] [Algebra K R]
    (t : Rˣ) (b : Langlands.CentralSimple.reducedNormOne K D R) :
    BinaryAction.normOneAction σ hdim hsym R (BinaryAction.diagonalSL t, b) =
      BinaryAction.hyperbolicLevi (σ.baseChange R)
        (Langlands.CentralSimple.normCoverScalarUnits K D R t * b.val) :=
  BinaryAction.diagonal_action_eq_levi (σ.baseChange R) _ b.val
    (BinaryAction.normOne_conjugate_inv σ hdim hsym R b) t

/-- The scalar lift acts by the scalar hyperbolic Levi matrix over every test scheme. -/
theorem scalar_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      (((x ≫ (scalar σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryAction.hyperbolicLevi (σ.baseChange (BinaryScheme.coefficients T))
          (Langlands.CentralSimple.normCoverScalarUnits K D (BinaryScheme.coefficients T)
            (Gm.pointsEquiv (Spec (CommRingCat.of K)) T x))) := by
  change HyperbolicScheme.matrixPointsEquiv n T
    ((((x ≫ (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K)).hom.hom) ≫
      (specialLinear σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
      (σ.isometryGroupι q).hom.hom) = _
  rw [specialLinear_points, SpecialLinear.BinaryRoot.pointsEquiv_upperCocharacter]
  change HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
    (BinaryAction.normOneAction σ hdim hsym (BinaryScheme.coefficients T)
      (BinaryAction.diagonalSL (R := BinaryScheme.coefficients T)
        (Gm.pointsEquiv (Spec (CommRingCat.of K)) T x), 1)) = _
  rw [diagonal_normOne_action]
  simp only [OneMemClass.coe_one, mul_one]

/-- The norm-one lift acts by its actual hyperbolic Levi matrix over every test scheme. -/
theorem normOne_levi_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (CentralSimpleUnits.normOne K D).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      (((x ≫ (normOne σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryAction.hyperbolicLevi (σ.baseChange (BinaryScheme.coefficients T))
          (CentralSimpleUnits.normOnePointsEquiv K D T x).val) := by
  rw [normOne_points]
  have he := diagonal_normOne_action σ hdim hsym (BinaryScheme.coefficients T)
    1 (CentralSimpleUnits.normOnePointsEquiv K D T x)
  simpa only [map_one, one_mul] using congrArg
    (HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)) he

end Langlands.GroupScheme.Quaternionic.BinarySpinLift
