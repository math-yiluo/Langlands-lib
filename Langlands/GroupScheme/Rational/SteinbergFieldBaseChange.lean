import Langlands.GroupScheme.Rational.SteinbergRootFieldBaseChange
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.ClassFunctionsQuotientDescent

/-! # Actual field extension of supplied Steinberg products -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} [Algebra.IsAlgebraic k F]

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

local instance productStandardAffine (K : Type u) [Field K] (d : ℕ) :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of K) d).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of K) d

namespace SimpleReflectionRepresentative

variable {a : p.base.support} (n : p.SimpleReflectionRepresentative a)

/-- Transport the actual supplied normalizer point and its torus automorphism. -/
def fieldBaseChange :
    (p.baseChange (F := F)).SimpleReflectionRepresentative
      (p.baseChangeSimpleEquiv (F := F) a) where
  point := baseChangeBasePoint bc G n.point
  torusAut := (CommGroupScheme.baseChange bc).mapIso n.torusAut
  normalizes := n.normalizes.baseChangeBasePoint bc
  characterAut_eq := by
    apply LinearEquiv.ext
    intro χF
    obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).surjective χF
    change characterAut ((CommGroupScheme.baseChange bc).mapIso n.torusAut)
      (characterLattice.baseChange bc p.torus χ) =
        (SplitRootDatum.baseChange bc p.torus p.isSplitTorus p.rootDatum).reflection a.val
          (characterLattice.baseChange bc p.torus χ)
    rw [characterAut_baseChange, SplitRootDatum.baseChange_reflection, n.characterAut_eq]

end SimpleReflectionRepresentative

/-- Transport every supplied normalized root map through the canonical simple-index equivalence. -/
def fieldBaseChangeRootMaps (x : p.NormalizedSimpleRootParametrizations) :
    (p.baseChange (F := F)).NormalizedSimpleRootParametrizations :=
  Equiv.piCongrLeft (p.baseChange (F := F)).NormalizedRootParametrization
    (p.baseChangeSimpleEquiv (F := F)) (fun a => (x a).fieldBaseChange)

/-- Transport every supplied reflection representative, retaining the original sections. -/
def fieldBaseChangeRepresentatives (n : p.SimpleReflectionRepresentatives) :
    (p.baseChange (F := F)).SimpleReflectionRepresentatives :=
  Equiv.piCongrLeft (p.baseChange (F := F)).SimpleReflectionRepresentative
    (p.baseChangeSimpleEquiv (F := F)) (fun a => (n a).fieldBaseChange)

@[simp]
theorem fieldBaseChangeRootMaps_apply (x : p.NormalizedSimpleRootParametrizations)
    (a : p.base.support) :
    fieldBaseChangeRootMaps (F := F) x (p.baseChangeSimpleEquiv (F := F) a) =
      (x a).fieldBaseChange := by
  exact Equiv.piCongrLeft_apply_apply _ _ _ a

@[simp]
theorem fieldBaseChangeRepresentatives_apply (n : p.SimpleReflectionRepresentatives)
    (a : p.base.support) :
    fieldBaseChangeRepresentatives (F := F) n (p.baseChangeSimpleEquiv (F := F) a) =
      (n a).fieldBaseChange := by
  exact Equiv.piCongrLeft_apply_apply _ _ _ a

variable {r : ℕ} (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

/-- Retain the original ordered simple indices under actual field extension. -/
def fieldBaseChangeOrder : Fin r ≃ (p.baseChange (F := F)).base.support :=
  e.trans (p.baseChangeSimpleEquiv (F := F))

/-- The original ordered product is recovered on every test through actual pullback projection. -/
theorem fieldBaseChange_steinbergProductPoint (T : Over (Spec (CommRingCat.of F)))
    (c : Fin r → Γ(T.left, ⊤)) :
    baseChangePointsEquiv bc G T
      (steinbergProductPoint (fieldBaseChangeOrder (F := F) e)
        (fieldBaseChangeRootMaps x) (fieldBaseChangeRepresentatives n) T c) =
      steinbergProductPoint e x n ((Over.map bc).obj T) c := by
  have hf (j : Fin r) :
      baseChangePointsEquiv bc G T
        (((x (e j)).fieldBaseChange (F := F)).point T (c j) *
          (toUnit T ≫ ((n (e j)).fieldBaseChange (F := F)).point)) =
        (x (e j)).point ((Over.map bc).obj T) (c j) *
          (toUnit ((Over.map bc).obj T) ≫ (n (e j)).point) := by
    rw [map_mul]
    change baseChangePointsEquiv bc G T
        (VectorGroup.scalarPoint (CommRingCat.of F) T (c j) ≫
          ((x (e j)).fieldBaseChangeHom (F := F)).hom.hom) *
        baseChangePointsEquiv bc G T
          (constantPoint GF (baseChangeBasePoint bc G (n (e j)).point) T) = _
    rw [NormalizedRootParametrization.fieldBaseChangeHom_point,
      baseChangePointsEquiv_constantPoint]
    rfl
  unfold steinbergProductPoint
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext hf))

/-- The ordered morphism commutes with actual field extension and the standard source comparison. -/
theorem fieldBaseChange_steinbergProduct :
    (VectorGroup.fieldBaseChangeIso k F r).hom.hom.hom ≫
        steinbergProduct (fieldBaseChangeOrder (F := F) e)
          (fieldBaseChangeRootMaps x) (fieldBaseChangeRepresentatives n) =
      (Over.pullback bc).map (steinbergProduct e x n) := by
  apply (baseChangePointsEquiv bc G _).injective
  have hcoord := VectorGroup.coordinates_fieldBaseChangeIso_hom k F r _ (𝟙 _)
  rw [Category.id_comp] at hcoord
  have hleft :
      baseChangePointsEquiv bc G _
        ((VectorGroup.fieldBaseChangeIso k F r).hom.hom.hom ≫
          steinbergProduct (fieldBaseChangeOrder (F := F) e)
            (fieldBaseChangeRootMaps x) (fieldBaseChangeRepresentatives n)) =
        baseChangePointsEquiv bc (VectorGroup.groupScheme (CommRingCat.of k) r) _
          (𝟙 _) ≫ steinbergProduct e x n := by
    rw [comp_steinbergProduct]
    change baseChangePointsEquiv bc G _
        (steinbergProductPoint (fieldBaseChangeOrder (F := F) e)
          (fieldBaseChangeRootMaps x) (fieldBaseChangeRepresentatives n) _
          (VectorGroup.coordinates (CommRingCat.of F) r _
            (VectorGroup.fieldBaseChangeIso k F r).hom.hom.hom).toAdd) = _
    rw [fieldBaseChange_steinbergProductPoint, comp_steinbergProduct, hcoord]
    rfl
  refine hleft.trans ?_
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, Over.comp_left, Over.id_left,
    Over.pullback_map_left, pullback.lift_fst, Category.id_comp]

/-- The exact supplied ordered product has the quotient-isomorphism property if and only if
its transported supplied data do, over an algebraic field extension. -/
theorem isIso_steinbergQuotient_baseChange_iff :
    IsIso (steinbergProduct (fieldBaseChangeOrder (F := F) e)
        (fieldBaseChangeRootMaps x) (fieldBaseChangeRepresentatives n) ≫
          ClassFunctions.rho GF) ↔
      IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  have h := isIso_steinbergQuotient_fieldExtension_iff (F := F) e x n
  rw [ClassFunctions.BaseChange.quotientComposite, ← fieldBaseChange_steinbergProduct e x n,
    Category.assoc, isIso_comp_left_iff] at h
  exact h

end Langlands.GroupScheme.SplitPinning
