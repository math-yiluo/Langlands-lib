import Langlands.AlgebraicGeometry.Picard.FiniteWeilCartierPerfectness
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHom
import Langlands.AbelianScheme.TorsionFunctor

/-! # Cartier perfectness along an actual principal polarization -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-- An actual group-scheme isomorphism induces an isomorphism of additive point functors. -/
def additivePointsIso (e : G ≅ H) :
    additivePoints G.toGrp ≅ additivePoints H.toGrp :=
  NatIso.ofComponents
    (fun T => ({
      toFun x := Additive.ofMul (x.toMul ≫ (CommGroupScheme.groupHom e.hom).hom.hom)
      invFun y := Additive.ofMul (y.toMul ≫ (CommGroupScheme.groupHom e.inv).hom.hom)
      left_inv x := by
        change (x.toMul ≫ _) ≫ _ = x.toMul
        have he := congrArg
          (fun f : G ⟶ G => (CommGroupScheme.groupHom f).hom.hom) e.hom_inv_id
        change (CommGroupScheme.groupHom e.hom).hom.hom ≫
          (CommGroupScheme.groupHom e.inv).hom.hom = 𝟙 G.X at he
        rw [Category.assoc, he, Category.comp_id]
      right_inv y := by
        change (y.toMul ≫ _) ≫ _ = y.toMul
        have he := congrArg
          (fun f : H ⟶ H => (CommGroupScheme.groupHom f).hom.hom) e.inv_hom_id
        change (CommGroupScheme.groupHom e.inv).hom.hom ≫
          (CommGroupScheme.groupHom e.hom).hom.hom = 𝟙 H.X at he
        rw [Category.assoc, he, Category.comp_id]
      map_add' x y := MonObj.mul_comp x.toMul y.toMul
        (CommGroupScheme.groupHom e.hom).hom.hom
    } : Additive (T.unop ⟶ G.X) ≃+ Additive (T.unop ⟶ H.X)).toAddCommGrpIso)
    (by
      intro T U b
      ext x
      exact Category.assoc b.unop x.toMul (CommGroupScheme.groupHom e.hom).hom.hom)

@[simp] lemma additivePointsIso_hom_app (e : G ≅ H) (T : Over S)
    (x : Additive (T ⟶ G.X)) :
    (additivePointsIso e).hom.app (op T) x =
      Additive.ofMul (x.toMul ≫ (CommGroupScheme.groupHom e.hom).hom.hom) := rfl

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (duality : RelativeDualKernelCharacterBijectiveStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "torsionMap" => finiteWeilAlongHomTorsionMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
local notation "chi" => dualTorsionCharacter preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "value" => finiteWeilAlongHomValue preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA

omit [QuasiSeparatedSpace S] in
/-- The pairing's existing torsion restriction is the actual torsion functor's map. -/
lemma finiteWeilAlongHomTorsionMap_eq_torsionMap (lam : A ⟶ DA) (n : ℕ) :
    torsionMap lam n = (GroupScheme.torsionMap (groupHom lam) (n : ℤ)).hom.hom := by
  apply (cancel_mono (torsionι (DA).toGrp (n : ℤ)).hom.hom).mp
  rw [finiteWeilAlongHom_torsion_inclusion]
  exact (congrArg (fun f => f.hom.hom)
    (GroupScheme.torsionMap_ι (groupHom lam) (n : ℤ))).symm

/-- Pulling the intrinsic pairing along an actual isomorphism to the dual is Cartier perfect. -/
def finiteWeilAlongIsoCartierIso (lam : A ⟶ DA) [IsIso lam]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    additivePoints (primal n).toGrp ≅ Cartier.characters (primal n) :=
  let e : A.toCommGroupScheme ≅ (DA).toCommGroupScheme :=
    { hom := commHom lam
      inv := commHom (inv lam)
      hom_inv_id := (asIso lam).hom_inv_id
      inv_hom_id := (asIso lam).inv_hom_id }
  additivePointsIso ((CommGroupScheme.torsionFunctor (n : ℤ)).mapIso e) ≪≫
    finiteWeilCartierIso preservation composition unitCoherence associativity comparison
      symmetry stability duality hA MA evaluationA n hn

/-- The second variable is sent to precisely the character of its actual image under `lam[n]`. -/
@[simp] lemma finiteWeilAlongIsoCartierIso_hom_app (lam : A ⟶ DA) [IsIso lam]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (y : Additive (T ⟶ (primal n).X)) :
    (finiteWeilAlongIsoCartierIso preservation composition unitCoherence associativity comparison
      symmetry stability duality hA geometryA MA evaluationA lam n hn).hom.app (op T) y =
        chi n (y.toMul ≫ torsionMap lam n) := by
  change chi n (y.toMul ≫
    (GroupScheme.torsionMap (groupHom lam) (n : ℤ)).hom.hom) = _
  rw [finiteWeilAlongHomTorsionMap_eq_torsionMap]

/-- Its root-valued evaluation is exactly the published pairing pulled back along `lam`. -/
lemma finiteWeilAlongIsoCartierIso_muEvaluation (lam : A ⟶ DA) [IsIso lam]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (x y : T ⟶ (primal n).X) :
    Cartier.muEvaluation n (torsion_multiplication_eq_one A.toGrp (n : ℤ))
      ((finiteWeilAlongIsoCartierIso preservation composition unitCoherence associativity comparison
        symmetry stability duality hA geometryA MA evaluationA lam n hn).hom.app (op T)
          (Additive.ofMul y)) x = value lam n x y := by
  rw [finiteWeilAlongIsoCartierIso_hom_app]
  rfl

/-- The same perfectness with the actual `Hom_T(A[n]_T,Gm_T)` presentation. -/
def finiteWeilAlongIsoCharacterHomIso (lam : A ⟶ DA) [IsIso lam]
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    additivePoints (primal n).toGrp ≅ Cartier.characterHomFunctor (primal n) :=
  finiteWeilAlongIsoCartierIso preservation composition unitCoherence associativity comparison
    symmetry stability duality hA geometryA MA evaluationA lam n hn ≪≫
      Cartier.characterHomNatIso (primal n)

variable (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})

/-- Cartier perfectness for the actual pairing of a principal relative polarization. -/
def finiteWeilPrincipalCartierIso (lam : A ⟶ DA)
    (hlam : IsPrincipalPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) :
    additivePoints (primal n).toGrp ≅ Cartier.characters (primal n) := by
  letI : IsIso lam := hlam.2
  exact finiteWeilAlongIsoCartierIso preservation composition unitCoherence associativity comparison
    symmetry stability duality hA geometryA MA evaluationA lam n hn

/-- The principal-polarization specialization retains the original root-valued evaluation. -/
lemma finiteWeilPrincipalCartierIso_muEvaluation (lam : A ⟶ DA)
    (hlam : IsPrincipalPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (x y : T ⟶ (primal n).X) :
    Cartier.muEvaluation n (torsion_multiplication_eq_one A.toGrp (n : ℤ))
      ((finiteWeilPrincipalCartierIso preservation composition unitCoherence associativity comparison
        symmetry stability duality hA geometryA MA evaluationA square universality lam hlam n hn).hom.app
          (op T) (Additive.ofMul y)) x = value lam n x y := by
  let : IsIso lam := hlam.2
  exact finiteWeilAlongIsoCartierIso_muEvaluation preservation composition unitCoherence
    associativity comparison symmetry stability duality hA geometryA MA evaluationA lam n hn T x y

end Langlands.AbelianScheme
