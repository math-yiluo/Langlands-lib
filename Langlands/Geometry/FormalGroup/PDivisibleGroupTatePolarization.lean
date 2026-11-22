import Langlands.AbelianScheme.Tate.Twist
import Langlands.Geometry.FormalGroup.PDivisibleGroupTateReduction
import Langlands.Geometry.FormalGroup.PDivisibleSplitOrderAction

/-! # The Weil pairing on schematic Tate points -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] {G : PDivisibleGroup R p}

private abbrev pointEval (T : Over (Spec R)) :
    CommGroupScheme (Spec R) ⥤ AddCommGrpCat.{u} :=
  additivePointFunctor (Spec R) ⋙ (CategoryTheory.evaluation _ _).obj (op T)

private abbrev levelPoints (G : PDivisibleGroup R p) (T : Over (Spec R)) (n : ℕ) :=
  Additive (T ⟶ (G.inclusions.obj n).X)

private abbrev tatePoints (G : PDivisibleGroup R p) (T : Over (Spec R)) :=
  ((schematicTatePointFunctor R p).obj G).obj (op T)

private abbrev project (G : PDivisibleGroup R p) (T : Over (Spec R)) (n : ℕ) :=
  (G.schematicTatePointProjection n).app (op T)

/-- The actual finite group at level `n` is killed by `p ^ n` on every scheme test. -/
theorem schematicTateLevel_nsmul (T : Over (Spec R)) (n : ℕ) (x : levelPoints G T n) :
    (p ^ n : ℕ) • x = 0 := by
  let H := G.inclusions.obj n
  have : IsFinite H.X.hom := (G.finiteLocallyFree n).1
  have : IsAffine H.X.left := GroupScheme.Cartier.FiniteDual.isAffine_of_isFinite H.toGrp
  obtain ⟨C, _, _, ⟨e⟩⟩ := GroupScheme.Cartier.FiniteDual.exists_iso_algSpec H.X
  let y : levelPoints G (affineTest (CommAlgCat.of R C)) n := Additive.ofMul e.inv
  let b : T ⟶ affineTest (CommAlgCat.of R C) := x.toMul ≫ e.hom
  let r := ((additivePoints H.toGrp).map b.op).hom
  have hr : r y = x := by
    change Additive.ofMul ((x.toMul ≫ e.hom) ≫ e.inv) = x
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    rfl
  have hy : (p ^ n : ℕ) • (r y) = 0 := by
    rw [← map_nsmul, G.schematicTateFiniteLevel_nsmul (CommAlgCat.of R C) n y, map_zero]
  rwa [hr] at hy

namespace PrincipalPolarization

variable (pol : PrincipalPolarization G) (T : Over (Spec R))

private abbrev globalSections (T : Over (Spec R)) := Γ(T.left, ⊤)

local notation "ΓT" => globalSections T

/-- The actual finite pairing evaluated as global units on the test scheme. -/
def levelWeilUnits (n : ℕ) :
    levelPoints G T n →+ levelPoints G T n →+ Additive ΓTˣ where
  toFun x := (Gm.pointsEquiv (Spec R) T).toAdditive.toAddMonoidHom.comp
    (MonoidHom.toAdditive (pol.evaluate n T x.toMul))
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change Additive.ofMul (Gm.pointsEquiv (Spec R) T
      (characterEvaluation ((pol.perfect n).hom.app (op T) 0) y.toMul)) = 0
    rw [map_zero, characterEvaluation_zero, map_one]
    rfl
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    change Additive.ofMul (Gm.pointsEquiv (Spec R) T
      (characterEvaluation ((pol.perfect n).hom.app (op T) (x + x')) y.toMul)) =
      Additive.ofMul (Gm.pointsEquiv (Spec R) T
        (characterEvaluation ((pol.perfect n).hom.app (op T) x) y.toMul)) +
      Additive.ofMul (Gm.pointsEquiv (Spec R) T
        (characterEvaluation ((pol.perfect n).hom.app (op T) x') y.toMul))
    rw [map_add, characterEvaluation_add, map_mul]
    rfl

theorem levelWeilUnits_restrict {U : Over (Spec R)} (b : U ⟶ T) (n : ℕ)
    (x y : T ⟶ (G.inclusions.obj n).X) :
    pol.levelWeilUnits U n (Additive.ofMul (b ≫ x)) (Additive.ofMul (b ≫ y)) =
      Additive.ofMul (Units.map b.left.appTop.hom.toMonoidHom
        (pol.levelWeilUnits T n (Additive.ofMul x) (Additive.ofMul y)).toMul) := by
  let χ := (pol.perfect n).hom.app (op T) (Additive.ofMul x)
  have h := ConcreteCategory.congr_hom ((pol.perfect n).hom.naturality b.op) (Additive.ofMul x)
  change (pol.perfect n).hom.app (op U) (Additive.ofMul (b ≫ x)) =
    (characters (G.inclusions.obj n)).map b.op χ at h
  change Additive.ofMul (Gm.pointsEquiv (Spec R) U
      (characterEvaluation ((pol.perfect n).hom.app (op U) (Additive.ofMul (b ≫ x))) (b ≫ y))) =
    Additive.ofMul (Units.map b.left.appTop.hom.toMonoidHom
      (Gm.pointsEquiv (Spec R) T (characterEvaluation χ y)))
  rw [h, characterEvaluation_restrict, Gm.pointsEquiv_naturality]

private def levelWeilValue (n : ℕ) (x y : levelPoints G T n) : TateTwist.Level ΓT (p ^ n) :=
  Additive.ofMul ⟨(pol.levelWeilUnits T n x y).toMul, by
    rw [mem_rootsOfUnity]
    let f := pol.levelWeilUnits T n x
    have h : (p ^ n : ℕ) • f y = 0 := by
      rw [← map_nsmul, schematicTateLevel_nsmul, map_zero]
    exact congrArg Additive.toMul h⟩

@[simp] theorem toUnit_levelWeilValue (n : ℕ) (x y : levelPoints G T n) :
    TateTwist.toUnit ΓT (p ^ n) (pol.levelWeilValue T n x y) = pol.levelWeilUnits T n x y := rfl

private theorem point_factorization {m n : ℕ} (i : m ⟶ n)
    (x : (pointEval T).obj (G.inclusions.obj n)) :
    (pointEval T).map (G.inclusions.map i) ((pointEval T).map (G.transfer i) x) =
      (p ^ (n - m) : ℕ) • x := by
  have h : (pointEval T).map (G.transfer i) ≫ (pointEval T).map (G.inclusions.map i) =
      p ^ (n - m) • 𝟙 ((pointEval T).obj (G.inclusions.obj n)) := by
    rw [← Functor.map_comp, G.multiplication, Functor.map_nsmul, (pointEval T).map_id]
  exact congrArg (fun f : (pointEval T).obj (G.inclusions.obj n) ⟶ _ => f x) h

private theorem levelWeilValue_transition (n : ℕ) (x y : tatePoints G T) :
    TateTwist.transition ΓT (pow_dvd_pow p (Nat.le_succ n))
        (pol.levelWeilValue T (n + 1) (project G T (n + 1) x) (project G T (n + 1) y)) =
      pol.levelWeilValue T n (project G T n x) (project G T n y) := by
  let i : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
  let E := pointEval T
  have h (z : tatePoints G T) :
      E.map (G.transfer i) (project G T (n + 1) z) = project G T n z :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (G.schematicTatePointProjection_transfer i) (op T)) z
  have hx := point_factorization T i (project G T (n + 1) x)
  change E.map (G.inclusions.map i) (E.map (G.transfer i) (project G T (n + 1) x)) =
      p ^ (n + 1 - n) • project G T (n + 1) x at hx
  rw [Nat.add_sub_cancel_left, pow_one, h x] at hx
  apply TateTwist.toUnit_injective ΓT (p ^ n)
  rw [TateTwist.toUnit_transition_succ, toUnit_levelWeilValue, toUnit_levelWeilValue]
  calc
    p • pol.levelWeilUnits T (n + 1) (project G T (n + 1) x) (project G T (n + 1) y) =
        pol.levelWeilUnits T (n + 1) (p • project G T (n + 1) x) (project G T (n + 1) y) := by
      rw [map_nsmul]
      rfl
    _ = _ := by
      rw [← hx, ← h y]
      exact congrArg (fun z => Additive.ofMul (Gm.pointsEquiv (Spec R) T z))
        (pol.adjoint i T (project G T n x).toMul (project G T (n + 1) y).toMul)

private def schematicTateWeilValue (x y : tatePoints G T) : TateTwist.Integral ΓT p :=
  ⟨fun n => pol.levelWeilValue T n (project G T n x) (project G T n y),
    fun n => pol.levelWeilValue_transition T n x y⟩

/-- The finite principal polarization induces a biadditive pairing of actual
schematic Tate sections with values in the actual integral Tate twist. -/
def schematicTateWeilPairing :
    tatePoints G T →+ tatePoints G T →+ TateTwist.Integral ΓT p where
  toFun x :=
    { toFun := pol.schematicTateWeilValue T x
      map_zero' := by
        apply Subtype.ext
        funext n
        apply TateTwist.toUnit_injective ΓT (p ^ n)
        change pol.levelWeilUnits T n (project G T n x) ((project G T n).hom 0) = 0
        rw [map_zero, map_zero]
      map_add' y y' := by
        apply Subtype.ext
        funext n
        apply TateTwist.toUnit_injective ΓT (p ^ n)
        change pol.levelWeilUnits T n (project G T n x) ((project G T n).hom (y + y')) =
          pol.levelWeilUnits T n (project G T n x) (project G T n y) +
          pol.levelWeilUnits T n (project G T n x) (project G T n y')
        rw [map_add, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    funext n
    apply TateTwist.toUnit_injective ΓT (p ^ n)
    change pol.levelWeilUnits T n ((project G T n).hom 0) (project G T n y) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    apply Subtype.ext
    funext n
    apply TateTwist.toUnit_injective ΓT (p ^ n)
    change pol.levelWeilUnits T n ((project G T n).hom (x + x')) (project G T n y) =
      pol.levelWeilUnits T n (project G T n x) (project G T n y) +
      pol.levelWeilUnits T n (project G T n x') (project G T n y)
    rw [map_add, map_add]
    rfl

@[simp] theorem toUnit_schematicTateWeilPairing (n : ℕ) (x y : tatePoints G T) :
    TateTwist.toUnit ΓT (p ^ n)
        (TateTwist.evaluation ΓT p n (pol.schematicTateWeilPairing T x y)) =
      pol.levelWeilUnits T n (project G T n x) (project G T n y) := rfl

/-- The pairing on compatible sections is alternating at every test. -/
@[simp] theorem schematicTateWeilPairing_self (x : tatePoints G T) :
    pol.schematicTateWeilPairing T x x = 0 := by
  apply Subtype.ext
  funext n
  apply TateTwist.toUnit_injective ΓT (p ^ n)
  let z : T ⟶ (G.inclusions.obj n).X := (project G T n x).toMul
  exact (congrArg (fun w => Additive.ofMul (Gm.pointsEquiv (Spec R) T w))
    (pol.alternating n T z)).trans (congrArg Additive.ofMul (map_one (Gm.pointsEquiv (Spec R) T)))

/-- Restriction of tests commutes with the pairing and the induced map of Tate twists. -/
theorem schematicTateWeilPairing_restrict {U : Over (Spec R)} (b : U ⟶ T)
    (x y : tatePoints G T) :
    pol.schematicTateWeilPairing U (((schematicTatePointFunctor R p).obj G).map b.op x)
        (((schematicTatePointFunctor R p).obj G).map b.op y) =
      TateTwist.map p b.left.appTop.hom (pol.schematicTateWeilPairing T x y) := by
  apply Subtype.ext
  funext n
  apply TateTwist.toUnit_injective Γ(U.left, ⊤) (p ^ n)
  change pol.levelWeilUnits U n
      (project G U n (((schematicTatePointFunctor R p).obj G).map b.op x))
      (project G U n (((schematicTatePointFunctor R p).obj G).map b.op y)) =
    Additive.ofMul (Units.map b.left.appTop.hom.toMonoidHom
      (pol.levelWeilUnits T n (project G T n x) (project G T n y)).toMul)
  exact (congrArg₂ (fun a c => pol.levelWeilUnits U n a c)
    (G.schematicTatePointProjection_restrict b x n)
    (G.schematicTatePointProjection_restrict b y n)).trans
    (pol.levelWeilUnits_restrict T b n (project G T n x).toMul (project G T n y).toMul)

end PrincipalPolarization
end Langlands.PDivisibleGroup
