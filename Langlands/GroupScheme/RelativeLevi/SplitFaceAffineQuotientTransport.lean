import Langlands.GroupScheme.RelativeLevi.SplitFaceAffineTransport
import Langlands.GroupScheme.RelativeLevi.SplitFaceGlobalQuotientLinearity
import Langlands.GroupScheme.Torus.FibrewiseMaximalBaseChange
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange

/-! # Original coefficient quotients under actual ambient transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell LocalSplitRootBaseChange
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R A : Type u} [CommRing R] [CommRing A] [Nontrivial R] [Algebra R A]
  {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of A))} [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  (C : SplitParabolicFaceChart i P fam wt)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))

local instance affineQuotientTransport_sourceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance affineQuotientTransport_targetAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance affineQuotientTransport_pullbackAffine :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

/-- An actual face chart on the coefficient-changed original root maps. -/
def coefficientFreshChart :
    SplitParabolicFaceChart (splitTorus.baseChangeHom (K := A) G I i)
      P (fun a => baseChangeRoot A (fam a)) wt := by
  let _ := C
  let : Smooth G.X.hom := hG.smooth
  exact Classical.choice (nonempty_splitParabolicFaceChart (hG.baseChange _)
    (splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I G i
      (algebraBaseMap R A) hmax) hP.baseChange_implicit
    (fun a => isRootParametrization_baseChangeRoot A i _ _ (hfam a)))

variable (f : (baseChange (algebraBaseMap R A)).obj G ≅ H)
  (D : SplitParabolicFaceChart (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom)
    P (fun a => baseChangeRoot A (fam a) ≫ f.hom) wt)

/-- Both independently chosen charts retain the original unscaled face height. -/
theorem coefficientFreshChart_transport_height (a : J) :
    faceHeight (C.coefficientFreshChart (A := A) hG hmax hP hfam).base
        (C.coefficientFreshChart (A := A) hG hmax hP hfam).faceCoweight (P.rootSpanMem ℤ a) =
      faceHeight D.base D.faceCoweight (P.rootSpanMem ℤ a) := by
  have h₁ := C.faceHeight_eq_of_affineBaseChange A
    (C.coefficientFreshChart (A := A) hG hmax hP hfam) hG hmax hP
  have h₂ := C.faceHeight_eq_of_sameCoordinateData D hG hmax hP
  exact LinearMap.congr_fun (h₁.symm.trans h₂) _

/-- The original coefficient term is transported through the actual ambient isomorphism. -/
def affineTransportTermIso (d : ℕ) :
    (baseChange (algebraBaseMap R A)).obj (C.weights.groupScheme d) ≅
      D.weights.groupScheme d := by
  classical
  let E := C.coefficientFreshChart (A := A) hG hmax hP hfam
  exact (C.affineBaseChangeTermIso A E hG hmax hP d) ≪≫
    E.rootTransportTermIso D (1 : RootPairing.Equiv P P) f
      (fun _ => rfl) (C.coefficientFreshChart_transport_height hG hmax hP hfam f D) d

/-- The term comparison preserves the original ambient maps exactly. -/
theorem affineTransportTermIso_hom_comp (d : ℕ) :
    (C.affineTransportTermIso hG hmax hP hfam f D d).hom ≫
        (D.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter
            (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom) D.cocharacter)) =
      (baseChange (algebraBaseMap R A)).map
        (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter i C.cocharacter)) ≫ f.hom := by
  classical
  unfold affineTransportTermIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [rootTransportTermIso_hom_comp, ← Category.assoc,
    C.affineBaseChangeTermIso_hom_comp A _ hG hmax hP d]

/-- Consecutive original terms retain their actual step map after transport. -/
theorem step_comp_affineTransportTermIso (d : ℕ) :
    (baseChange (algebraBaseMap R A)).map (C.weights.step d) ≫
        (C.affineTransportTermIso hG hmax hP hfam f D d).hom =
      (C.affineTransportTermIso hG hmax hP hfam f D (d + 1)).hom ≫ D.weights.step d := by
  classical
  unfold affineTransportTermIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc, C.step_comp_affineBaseChangeTermIso A _ hG hmax hP d,
    Category.assoc, step_comp_rootTransportTermIso]
  simp only [Category.assoc]

/-- The quotient of the ORIGINAL coefficient term, followed by actual ambient transport. -/
def affineTransportQuotientIso (d : ℕ) :
    VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (C.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of A) (Nat.card (D.weights.exactSupport d)) := by
  classical
  let E := C.coefficientFreshChart (A := A) hG hmax hP hfam
  exact (C.affineBaseChangeQuotientIso A E hG hmax hP d) ≪≫
    E.rootTransportQuotientIso D (1 : RootPairing.Equiv P P) f
      (fun _ => rfl) (C.coefficientFreshChart_transport_height hG hmax hP hfam f D) d

/-- The transported quotient retains the actual original coefficient quotient square. -/
theorem affineTransportQuotientIso_fac (d : ℕ) :
    C.affineBaseChangeQuotientMap A d ≫
        (C.affineTransportQuotientIso hG hmax hP hfam f D d).hom =
      (C.affineTransportTermIso hG hmax hP hfam f D d).hom ≫ D.weights.quotientMap d := by
  classical
  unfold affineTransportQuotientIso affineTransportTermIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc, C.affineBaseChangeQuotientIso_fac A _ hG hmax hP d,
    Category.assoc, quotientMap_comp_rootTransportQuotientIso]
  simp only [Category.assoc]

omit [Nontrivial R] [Fintype J] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem identity_transport_torus_square [DecidableEq I] :
    splitTorus.baseChangeHom (K := A) G I i ≫ f.hom =
      precompTorus (1 : RootPairing.Equiv P P).weightEquiv
        (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom) := by
  have he : (1 : RootPairing.Equiv P P).weightEquiv = LinearEquiv.refl ℤ (I → ℤ) := by
    ext x k
    rfl
  rw [he]
  change _ = CommGroupScheme.groupHom
    (splitTorus.exponentHom _ I I LinearMap.id) ≫ _
  rw [splitTorus.exponentHom_id]
  rfl

/-- The actual transported coefficient quotient commutes with every scalar power,
even over the zero coefficient ring. -/
theorem affineTransportQuotientIso_isEquivariant_power (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (C.affineTransportQuotientIso hG hmax hP hfam f D d).hom := by
  classical
  let E := C.coefficientFreshChart (A := A) hG hmax hP hfam
  have hF : ∀ a, IsRootParametrization
      (splitTorus.baseChangeHom (K := A) G I i) (P.root a) (baseChangeRoot A (fam a)) :=
    fun a => isRootParametrization_baseChangeRoot A i _ _ (hfam a)
  have hD : ∀ a, IsRootParametrization
      (splitTorus.baseChangeHom (K := A) G I i ≫ f.hom) (P.root a)
      (baseChangeRoot A (fam a) ≫ f.hom) :=
    fun a => (hF a).comp_iso f rfl
  have hq : VectorGroup.HasScalarWeight
      (VectorGroup.pointTransformation
        (E.rootTransportQuotientIso D (1 : RootPairing.Equiv P P) f (fun _ => rfl)
          (C.coefficientFreshChart_transport_height hG hmax hP hfam f D) d).hom)
      (E.faceMultiplier * (d + 1)) :=
    E.rootTransportQuotientIso_hasScalarWeight D (1 : RootPairing.Equiv P P) f
      (fun _ => rfl) (C.coefficientFreshChart_transport_height hG hmax hP hfam f D)
      hF hD (identity_transport_torus_square (P := P) f) d
  intro T s x
  change ((VectorGroup.powerWeightAction _ N).act s x ≫
      (C.affineBaseChangeQuotientIso A E hG hmax hP d).hom.hom.hom) ≫ _ = _
  rw [C.affineBaseChangeQuotientIso_isEquivariant_power A E hG hmax hP hfam d N]
  exact VectorGroup.isEquivariant_power_of_hasScalarWeight _
    (Nat.mul_pos E.faceMultiplier_pos (Nat.succ_pos d)) hq N s _

/-- The actual transported original quotient has scalar weight one. -/
theorem affineTransportQuotientIso_hasScalarWeight (d : ℕ) :
    VectorGroup.HasScalarWeight (VectorGroup.pointTransformation
      (C.affineTransportQuotientIso hG hmax hP hfam f D d).hom) 1 :=
  VectorGroup.hasScalarWeight_of_equivariant _ 1
    (C.affineTransportQuotientIso_isEquivariant_power hG hmax hP hfam f D d 1)

end Langlands.GroupScheme.SplitParabolicFaceChart
