import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameter
import Mathlib.CategoryTheory.Yoneda

/-! # Actual base change of the supplied-family full-level parameter -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} (A : AbelianScheme S) (g n : ℕ)

/-- Actual tuple-parameter maps before and after arbitrary base change. -/
def torsionTupleBaseChangeHomEquiv (b : S' ⟶ S) (T : Over S') :
    (T ⟶ torsionTupleScheme ((baseChange b).obj A) g n) ≃
      ((Over.map b).obj T ⟶ torsionTupleScheme A g n) :=
  (torsionTupleHomEquiv ((baseChange b).obj A) g n T).trans
    ((Equiv.piCongrRight fun _ : Fin (2 * g) =>
      (levelBaseChangeLinear A.toGrp b T n).toEquiv).trans
      (torsionTupleHomEquiv A g n ((Over.map b).obj T)).symm)

/-- The tuple-map comparison is the original actual torsion comparison
on each prescribed coordinate. -/
@[simp]
theorem torsionTupleBaseChangeHomEquiv_apply (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ torsionTupleScheme ((baseChange b).obj A) g n) (i : Fin (2 * g)) :
    torsionTupleHomEquiv A g n ((Over.map b).obj T)
        (torsionTupleBaseChangeHomEquiv A g n b T f) i =
      levelBaseChangeLinear A.toGrp b T n
        (torsionTupleHomEquiv ((baseChange b).obj A) g n T f i) := by
  exact congrFun ((torsionTupleHomEquiv A g n ((Over.map b).obj T)).apply_symm_apply _) i

/-- The tuple-map comparison commutes with every actual test-scheme map. -/
theorem torsionTupleBaseChangeHomEquiv_comp (b : S' ⟶ S)
    {T T' : Over S'} (a : T' ⟶ T)
    (f : T ⟶ torsionTupleScheme ((baseChange b).obj A) g n) :
    torsionTupleBaseChangeHomEquiv A g n b T' (a ≫ f) =
      (Over.map b).map a ≫ torsionTupleBaseChangeHomEquiv A g n b T f := by
  apply (torsionTupleHomEquiv A g n ((Over.map b).obj T')).injective
  funext i
  rw [torsionTupleBaseChangeHomEquiv_apply, torsionTupleHomEquiv_comp,
    torsionTupleHomEquiv_comp, torsionTupleBaseChangeHomEquiv_apply]
  exact levelBaseChange_testRestrict b A.toGrp a n _

/-- Direct and successive pullbacks retain exactly the same decoded sections,
through the existing actual abelian-scheme comparison. -/
theorem sectionTupleBaseChangeEquiv_comp (b : S' ⟶ S) (T : Over S')
    (v : SectionTuple ((baseChange T.hom).obj ((baseChange b).obj A)) g n)
    (i : Fin (2 * g)) :
    sectionTupleBaseChangeEquiv A g n (T.hom ≫ b)
        (mapTuple (baseChangeCompIso b T.hom A).inv v) i =
      levelBaseChangeLinear A.toGrp b T n
        (sectionTupleBaseChangeEquiv ((baseChange b).obj A) g n T.hom v i) := by
  apply toSection_injective A.toGrp ((Over.map b).obj T) n
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ ((Additive.toMul (v i)).val.left ≫
      (GroupScheme.baseChangeCompIso b T.hom A.toGrp).inv.hom.hom.left)) ≫
      pullback.fst A.X.hom (T.hom ≫ b) =
    (𝟙 _ ≫ ((Additive.toMul (v i)).val.left ≫
      pullback.fst (pullback.snd A.X.hom b) T.hom)) ≫ pullback.fst A.X.hom b
  simp only [Category.id_comp, Category.assoc, GroupScheme.baseChangeCompIso_inv_fst]

/-- The decoded tuple before and after base change agrees through the actual
comparison between direct and successive pullbacks. -/
theorem torsionTupleBaseChangeHomEquiv_sections (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ torsionTupleScheme ((baseChange b).obj A) g n) :
    torsionTupleSectionEquiv A g n (T.hom ≫ b)
        (torsionTupleBaseChangeHomEquiv A g n b T f) =
      mapTuple (baseChangeCompIso b T.hom A).inv
        (torsionTupleSectionEquiv ((baseChange b).obj A) g n T.hom f) := by
  apply (sectionTupleBaseChangeEquiv A g n (T.hom ≫ b)).injective
  funext i
  rw [sectionTupleBaseChangeEquiv_comp]
  change (sectionTupleBaseChangeEquiv A g n (T.hom ≫ b))
    ((sectionTupleBaseChangeEquiv A g n (T.hom ≫ b)).symm _) i = _
  rw [Equiv.apply_symm_apply]
  erw [torsionTupleBaseChangeHomEquiv_apply]
  congr 1
  exact (congrFun
    ((sectionTupleBaseChangeEquiv ((baseChange b).obj A) g n T.hom).apply_symm_apply _) i).symm

private theorem mapTuple_iso_inv_hom {U : Scheme.{u}} {B C : AbelianScheme U}
    (e : B ≅ C) (v : SectionTuple C g n) :
    mapTuple e.hom (mapTuple e.inv v) = v := by
  funext i
  apply toSection_injective C.toGrp (Over.mk (𝟙 U)) n
  change ((Additive.toMul (v i)).val ≫ (groupHom e.inv).hom.hom) ≫
    (groupHom e.hom).hom.hom = (Additive.toMul (v i)).val
  rw [Category.assoc]
  change (Additive.toMul (v i)).val ≫ (groupHom (e.inv ≫ e.hom)).hom.hom = _
  rw [e.inv_hom_id]
  exact Category.comp_id _

/-- Fullness is unchanged by the tuple comparison; no rank or nonemptiness
assumption is needed. -/
theorem isFull_torsionTupleBaseChangeHomEquiv_iff (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ torsionTupleScheme ((baseChange b).obj A) g n) :
    IsFull (torsionTupleSectionEquiv ((baseChange b).obj A) g n T.hom f) ↔
      IsFull (torsionTupleSectionEquiv A g n (T.hom ≫ b)
        (torsionTupleBaseChangeHomEquiv A g n b T f)) := by
  rw [torsionTupleBaseChangeHomEquiv_sections]
  constructor
  · intro h
    exact h.mapIso (baseChangeCompIso b T.hom A).symm
  · intro h
    have h' := h.mapIso (baseChangeCompIso b T.hom A)
    rwa [mapTuple_iso_inv_hom] at h'

/-- Actual full-level parameter maps before and after arbitrary base change. -/
def fullLevelParameterBaseChangeHomEquiv
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (T : Over S') :
    (T ⟶ fullLevelParameterScheme ((baseChange b).obj A) g n hn
      (Tate.isUnit_natCast_pullback b n hunit)) ≃
      ((Over.map b).obj T ⟶ fullLevelParameterScheme A g n hn hunit) :=
  (fullLevelParameterHomTupleEquiv ((baseChange b).obj A) g n hn
    (Tate.isUnit_natCast_pullback b n hunit) T).trans
    (((torsionTupleBaseChangeHomEquiv A g n b T).subtypeEquiv
      (fun f => isFull_torsionTupleBaseChangeHomEquiv_iff A g n b T f)).trans
      (fullLevelParameterHomTupleEquiv A g n hn hunit ((Over.map b).obj T)).symm)

/-- The full-level comparison retains the actual tuple comparison. -/
@[simp]
theorem fullLevelParameterBaseChangeHomEquiv_inclusion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ fullLevelParameterScheme ((baseChange b).obj A) g n hn
      (Tate.isUnit_natCast_pullback b n hunit)) :
    fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T f ≫
        fullLevelParameterInclusion A g n hn hunit =
      torsionTupleBaseChangeHomEquiv A g n b T
        (f ≫ fullLevelParameterInclusion ((baseChange b).obj A) g n hn
          (Tate.isUnit_natCast_pullback b n hunit)) := by
  exact congrArg Subtype.val
    ((fullLevelParameterHomTupleEquiv A g n hn hunit ((Over.map b).obj T)).apply_symm_apply _)

/-- The full-level comparison is natural in every actual test-scheme map. -/
theorem fullLevelParameterBaseChangeHomEquiv_comp
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) {T T' : Over S'} (a : T' ⟶ T)
    (f : T ⟶ fullLevelParameterScheme ((baseChange b).obj A) g n hn
      (Tate.isUnit_natCast_pullback b n hunit)) :
    fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T' (a ≫ f) =
      (Over.map b).map a ≫
        fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T f := by
  apply (fullLevelParameterHomTupleEquiv A g n hn hunit ((Over.map b).obj T')).injective
  apply Subtype.ext
  change fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T' (a ≫ f) ≫
      fullLevelParameterInclusion A g n hn hunit =
    ((Over.map b).map a ≫ fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T f) ≫
      fullLevelParameterInclusion A g n hn hunit
  simp only [fullLevelParameterBaseChangeHomEquiv_inclusion, Category.assoc]
  exact torsionTupleBaseChangeHomEquiv_comp A g n b a _

/-- The classified full levels agree on their prescribed ordered sections
through the actual comparison for successive pullbacks. -/
theorem fullLevelParameterBaseChangeHomEquiv_sections
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ fullLevelParameterScheme ((baseChange b).obj A) g n hn
      (Tate.isUnit_natCast_pullback b n hunit)) :
    (fullLevelParameterHomEquiv A g n hn hunit ((Over.map b).obj T)
        (fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T f)).sections =
      mapTuple (baseChangeCompIso b T.hom A).inv
        (fullLevelParameterHomEquiv ((baseChange b).obj A) g n hn
          (Tate.isUnit_natCast_pullback b n hunit) T f).sections := by
  simp only [fullLevelParameterHomEquiv_sections,
    fullLevelParameterBaseChangeHomEquiv_inclusion]
  exact torsionTupleBaseChangeHomEquiv_sections A g n b T _

/-- The full-level parameter of an actual pulled-back abelian scheme is
isomorphic to the actual pullback of its original full-level parameter. -/
def fullLevelParameterBaseChangeIso
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (b : S' ⟶ S) :
    fullLevelParameterScheme ((baseChange b).obj A) g n hn
        (Tate.isUnit_natCast_pullback b n hunit) ≅
      (Over.pullback b).obj (fullLevelParameterScheme A g n hn hunit) := by
  let e (T : Over S') :=
    (fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T).trans
      ((Over.mapPullbackAdj b).homEquiv T (fullLevelParameterScheme A g n hn hunit))
  exact Yoneda.ext _ _ (fun {T} => e T) (fun {T} => (e T).symm)
    (fun f => (e _).symm_apply_apply f) (fun f => (e _).apply_symm_apply f)
    (fun a f => by
      change (Over.mapPullbackAdj b).homEquiv _ _
        (fullLevelParameterBaseChangeHomEquiv A g n hn hunit b _ (a ≫ f)) = _
      rw [fullLevelParameterBaseChangeHomEquiv_comp]
      exact (Over.mapPullbackAdj b).homEquiv_naturality_left a _)

/-- On every actual test scheme, the isomorphism realizes precisely the
coordinate-preserving full-level comparison under the pullback adjunction. -/
theorem fullLevelParameterBaseChangeIso_hom_comp
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (b : S' ⟶ S) (T : Over S')
    (f : T ⟶ fullLevelParameterScheme ((baseChange b).obj A) g n hn
      (Tate.isUnit_natCast_pullback b n hunit)) :
    f ≫ (fullLevelParameterBaseChangeIso A g n hn hunit b).hom =
      (Over.mapPullbackAdj b).homEquiv T (fullLevelParameterScheme A g n hn hunit)
        (fullLevelParameterBaseChangeHomEquiv A g n hn hunit b T f) := by
  change f ≫ (Over.mapPullbackAdj b).homEquiv _ _
    (fullLevelParameterBaseChangeHomEquiv A g n hn hunit b _ (𝟙 _)) = _
  rw [← (Over.mapPullbackAdj b).homEquiv_naturality_left,
    ← fullLevelParameterBaseChangeHomEquiv_comp, Category.comp_id]

end Langlands.AbelianScheme.PolarizedFiniteLevel
