import Langlands.GroupScheme.Cartier.FiniteSchemeDualCharacters
import Langlands.GroupScheme.Cartier.CharacterBaseChangeNaturality
import Langlands.GroupScheme.HomScheme.MultiplicativeTargetEtale

/-! # Pullback of the actual finite dual spectrum -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

open GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local notation "b" => specBase R S
local notation "BC" => CommGroupScheme.baseChange b

local instance baseChangedFinite (G : CommGroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom] :
    IsFinite ((BC).obj G).X.hom := by
  change IsFinite (Limits.pullback.snd G.X.hom b)
  infer_instance
local instance baseChangedFlat (G : CommGroupScheme (Spec (CommRingCat.of R))) [Flat G.X.hom] :
    Flat ((BC).obj G).X.hom := by
  change Flat (Limits.pullback.snd G.X.hom b)
  infer_instance
local instance baseChangedFinitePresentation (G : CommGroupScheme (Spec (CommRingCat.of R))) [LocallyOfFinitePresentation G.X.hom] :
    LocallyOfFinitePresentation ((BC).obj G).X.hom := by
  change LocallyOfFinitePresentation (Limits.pullback.snd G.X.hom b)
  infer_instance

variable (G : CommGroupScheme (Spec (CommRingCat.of R))) [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- The points of the pulled-back original dual are the points of the dual over
the new base, via actual base change of relative characters. -/
def schemeDualBaseChangePoints (T : Over (Spec (CommRingCat.of S))) :
    (T ⟶ ((BC).obj (schemeDual G)).X) ≃* (T ⟶ (schemeDual ((BC).obj G)).X) := by
  let U : Over (Spec (CommRingCat.of R)) := (Over.map b).obj T
  let A := (characters G).obj (op U)
  let B := (characters ((BC).obj G)).obj (op T)
  let pull : Additive (T ⟶ ((BC).obj (schemeDual G)).X) ≃+ Additive (U ⟶ (schemeDual G).X) :=
    (baseChangePointsEquiv b (schemeDual G).toGrp T).toAdditive
  let old : Additive (U ⟶ (schemeDual G).X) ≃+ A :=
    ((schemeDualCharacters G).app (op U)).addCommGroupIsoToAddEquiv
  let chars : A ≃+ B := ((charactersBaseChangeIso G b).app (op T)).addCommGroupIsoToAddEquiv
  let new : Additive (T ⟶ (schemeDual ((BC).obj G)).X) ≃+ B :=
    ((schemeDualCharacters ((BC).obj G)).app (op T)).addCommGroupIsoToAddEquiv
  exact (pull.trans (old.trans (chars.trans new.symm))).toMultiplicative

/-- On characters the point equivalence is the actual relative character base-change map. -/
theorem schemeDualBaseChangePoints_character (T : Over (Spec (CommRingCat.of S))) (y : T ⟶ ((BC).obj (schemeDual G)).X) :
    (schemeDualCharacters ((BC).obj G)).hom.app (op T) (Additive.ofMul (schemeDualBaseChangePoints G T y)) =
      (charactersBaseChangeIso G b).hom.app (op T) ((schemeDualCharacters G).hom.app
        (op ((Over.map b).obj T)) (Additive.ofMul (baseChangePointsEquiv b (schemeDual G).toGrp T y))) := by
  let e := ((schemeDualCharacters ((BC).obj G)).app (op T)).addCommGroupIsoToAddEquiv
  exact e.apply_symm_apply _

private theorem schemeDualBaseChangePoints_restrict {T U : Over (Spec (CommRingCat.of S))} (a : U ⟶ T)
    (y : T ⟶ ((BC).obj (schemeDual G)).X) :
    schemeDualBaseChangePoints G U (a ≫ y) = a ≫ schemeDualBaseChangePoints G T y := by
  apply Additive.ofMul.injective
  apply ((schemeDualCharacters ((BC).obj G)).app (op U)).addCommGroupIsoToAddEquiv.injective
  change (schemeDualCharacters ((BC).obj G)).hom.app (op U)
    (Additive.ofMul (schemeDualBaseChangePoints G U (a ≫ y))) =
    (schemeDualCharacters ((BC).obj G)).hom.app (op U) (Additive.ofMul (a ≫ schemeDualBaseChangePoints G T y))
  rw [schemeDualBaseChangePoints_character, ← schemeDualCharacters_restrict,
    schemeDualBaseChangePoints_character, baseChangePointsEquiv_naturality, ← schemeDualCharacters_restrict]
  let χ : (characters G).obj (op ((Over.map b).obj T)) := (schemeDualCharacters G).hom.app
    (op ((Over.map b).obj T)) (Additive.ofMul (baseChangePointsEquiv b (schemeDual G).toGrp T y))
  exact ConcreteCategory.congr_hom ((charactersBaseChangeIso G b).hom.naturality a.op) χ

/-- The actual Cartier dual of a finite locally free group scheme commutes with pullback. -/
def schemeDualBaseChangeIso : (BC).obj (schemeDual G) ≅ schemeDual ((BC).obj G) :=
  CommGroupScheme.isoOfGroupIso (GroupScheme.isoOfPoints (schemeDualBaseChangePoints G)
    (fun a y => schemeDualBaseChangePoints_restrict G a y))

/-- The actual comparison induces the character comparison on every test. -/
theorem schemeDualBaseChangeIso_hom_points (T : Over (Spec (CommRingCat.of S))) (y : T ⟶ ((BC).obj (schemeDual G)).X) :
    y ≫ (schemeDualBaseChangeIso G).hom.toMul.hom.hom = schemeDualBaseChangePoints G T y :=
  GroupScheme.comp_isoOfPoints_hom (schemeDualBaseChangePoints (S := S) G)
    (fun a z => schemeDualBaseChangePoints_restrict G a z) T y

/-- Evaluation of the actual dual comparison gives the same global unit after pullback. -/
theorem schemeDualBaseChangeIso_evaluation (T : Over (Spec (CommRingCat.of S)))
    (y : T ⟶ ((BC).obj (schemeDual G)).X) (x : T ⟶ ((BC).obj G).X) :
    Gm.pointsEquiv _ T (finiteSchemePairing ((BC).obj G) T
      (y ≫ (schemeDualBaseChangeIso G).hom.toMul.hom.hom) x) =
      Gm.pointsEquiv _ ((Over.map b).obj T) (finiteSchemePairing G ((Over.map b).obj T)
        (baseChangePointsEquiv b (schemeDual G).toGrp T y) (baseChangePointsEquiv b G.toGrp T x)) := by
  rw [schemeDualBaseChangeIso_hom_points]
  have h := schemeDualCharacters_evaluation ((BC).obj G) T (schemeDualBaseChangePoints G T y) x
  rw [← h, schemeDualBaseChangePoints_character, charactersBaseChangeIso_evaluation,
    schemeDualCharacters_evaluation]

variable {G} {H : CommGroupScheme (Spec (CommRingCat.of R))} [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]

/-- The comparison intertwines the actual contravariant dual maps. -/
theorem schemeDualBaseChangeIso_naturality (f : G ⟶ H) :
    (BC).map (schemeDualMap f) ≫ (schemeDualBaseChangeIso G).hom =
      (schemeDualBaseChangeIso H).hom ≫ schemeDualMap ((BC).map f) := by
  apply GroupScheme.CommGroupScheme.hom_ext_points
  intro T y
  let t := (BC).map (schemeDualMap f)
  let e := (schemeDualBaseChangeIso (S := S) H).hom
  change y ≫ t.toMul.hom.hom ≫ (schemeDualBaseChangeIso G).hom.toMul.hom.hom =
    y ≫ e.toMul.hom.hom ≫ (schemeDualMap ((BC).map f)).toMul.hom.hom
  rw [← Category.assoc, ← Category.assoc y e.toMul.hom.hom,
    schemeDualBaseChangeIso_hom_points, schemeDualBaseChangeIso_hom_points]
  apply Additive.ofMul.injective
  apply ((schemeDualCharacters ((BC).obj G)).app (op T)).addCommGroupIsoToAddEquiv.injective
  change (schemeDualCharacters ((BC).obj G)).hom.app (op T)
      (Additive.ofMul (schemeDualBaseChangePoints G T (y ≫ t.toMul.hom.hom))) =
    (schemeDualCharacters ((BC).obj G)).hom.app (op T)
      (Additive.ofMul (schemeDualBaseChangePoints H T y ≫ (schemeDualMap ((BC).map f)).toMul.hom.hom))
  rw [schemeDualBaseChangePoints_character, schemeDualCharacters_precompose,
    schemeDualBaseChangePoints_character]
  have h := baseChangePointsEquiv_comp b (schemeDualMap f).toMul T y
  change baseChangePointsEquiv b (schemeDual G).toGrp T (y ≫ t.toMul.hom.hom) = _ at h
  rw [h, schemeDualCharacters_precompose, charactersBaseChangeIso_precompose]

end Langlands.GroupScheme.Cartier.FiniteDual
