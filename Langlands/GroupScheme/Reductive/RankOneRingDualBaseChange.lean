import Langlands.GroupScheme.Reductive.RankOneRingDualCell
import Langlands.GroupScheme.Reductive.LocalRankOneCellBaseChange

/-! # Coefficient transport for the actual dual-number rank-one cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell.DualCell

open Corepresented.RingCoordinates LocalWeylNormalization LocalSplitCell
open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The identity-scheme comparison of coefficient tests preserves functions. -/
theorem testOverHom_appTop (c : Γ((testOver A B).left, ⊤)) :
    (testOverHom (CommRingCat.of R) A B).left.appTop c = c := by
  change (𝟙 (Spec (CommRingCat.of B)) : _ ⟶ _).appTop c = c
  rw [Scheme.Hom.id_appTop]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Root coordinates are unchanged by the identity comparison of tests. -/
theorem testOverHom_rootPoint (w : Ga R ⟶ G) (c : Γ((testOver A B).left, ⊤)) :
    testOverHom (CommRingCat.of R) A B ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (testOver A B)
          (rootPoint (baseChangeRoot A w) (testOver A B) c) =
      rootPoint w (specOver (CommRingCat.of R) B) c := by
  rw [baseChangePointsEquiv_rootPoint, comp_rootPoint, testOverHom_appTop]

/-- The normalization scalar extracted from a positive dual cell coordinate. -/
def normalizationScalar (x : Γ((dualOver R).left, ⊤)) : R :=
  -((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x).snd

end RingRootCell.DualCell

namespace RingRootCell.WeylData

open LocalWeylNormalization

variable {A : Type u} [CommRing A]

/-- The dual coefficient formula depends only on the underlying cell data. -/
theorem snd_dual_positive_of_cellData_eq
    (E : WeylData A) (D : CellData A) (hE : E.toCellData = D)
    [IsAffine E.G.X.left]
    {y : Γ((dualOver A).left, ⊤)} {t : dualOver A ⟶ D.T.X}
    {x : Γ((dualOver A).left, ⊤)}
    (hx : D.A 1 * D.B (epsSec A) = D.cellPt y t x) :
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom x).snd =
      -(↑E.betaUnit⁻¹ : A) := by
  cases hE
  exact E.snd_dual_positive hx

end RingRootCell.WeylData

namespace LocalRankOneCell

open LocalSplitCell LocalSplitRootBaseChange
open Corepresented.RingCoordinates LocalWeylNormalization

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (a : I → ℤ) (xm xp : Ga R ⟶ G)
  (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
  (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
  (A : Type u) [CommRing A] [Algebra R A]

set_option maxHeartbeats 800000 in
/-- A dual cell factorization transports to any coefficient ring with
exactly the extended negative and positive scalar coordinates. -/
theorem dualFactorization_baseChange
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
      rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x)) :
    ∃ tA : dualOver A ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X,
      (baseChangeCellData i a xm xp hm hp hopen A).A 1 *
          (baseChangeCellData i a xm xp hm hp hopen A).B (epsSec A) =
        (baseChangeCellData i a xm xp hm hp hopen A).cellPt
          ((specMapOver (R := CommRingCat.of R) (RingRootCell.DualCell.coefficientMap (R := R) A)).left.appTop y)
          tA
          ((specMapOver (R := CommRingCat.of R) (RingRootCell.DualCell.coefficientMap (R := R) A)).left.appTop x) := by
  let b := algebraBaseMap R A
  let ψ := specMapOver (R := CommRingCat.of R) (RingRootCell.DualCell.coefficientMap (R := R) A)
  let f := testOverHom (CommRingCat.of R) A (DualNumber A)
  let g := testOverInv (CommRingCat.of R) A (DualNumber A)
  let ET := GroupScheme.baseChangePointsEquiv b (splitTorus _ I) (dualOver A)
  let t₀ := ET.symm (g ≫ ψ ≫ t)
  let tA := t₀ ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  have hf_inj : Function.Injective
      (fun z : (Over.map b).obj (dualOver A) ⟶ G.X => f ≫ z) := by
    intro v w h
    have h' := congrArg (fun z => g ≫ z) h
    simpa only [f, g, ← Category.assoc, testOverInv_comp_testOverHom,
      Category.id_comp] using h'
  have ht : ET (tA ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) =
      g ≫ ψ ≫ t := by
    dsimp only [tA]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
    exact ET.apply_symm_apply _
  refine ⟨tA, ?_⟩
  apply (GroupScheme.baseChangePointsEquiv b G (dualOver A)).injective
  apply hf_inj
  dsimp only
  change f ≫ GroupScheme.baseChangePointsEquiv b G (dualOver A)
      (rootPoint (baseChangeRoot A xp) (dualOver A) 1 *
        rootPoint (baseChangeRoot A xm) (dualOver A) (epsSec A)) = _
  rw [map_mul, MonObj.comp_mul,
    RingRootCell.DualCell.testOverHom_rootPoint,
    RingRootCell.DualCell.testOverHom_rootPoint,
    baseChangePointsEquiv_cellPt, MonObj.comp_mul, MonObj.comp_mul,
    comp_rootPoint, comp_rootPoint,
    RingRootCell.DualCell.testOverHom_appTop,
    RingRootCell.DualCell.testOverHom_appTop, ← Category.assoc]
  change _ = rootPoint xm (specOver (CommRingCat.of R) (DualNumber A)) (ψ.left.appTop y) *
    ((f ≫ ET (tA ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) ≫ i.hom.hom) *
      rootPoint xp (specOver (CommRingCat.of R) (DualNumber A)) (ψ.left.appTop x))
  rw [ht]
  simp only [← Category.assoc, f, g,
    testOverHom_comp_testOverInv, Category.id_comp]
  have heps : ψ.left.appTop (epsSec R) = epsSec A :=
    RingRootCell.DualCell.coefficientMap_appTop_eps A
  have h := congrArg (fun z => ψ ≫ z) hx
  simp only [MonObj.comp_mul, comp_rootPoint, map_one, heps] at h
  simpa only [Category.assoc] using h

/-- The original dual coefficient maps to minus the inverse beta unit of
any Weyl data on the actual coefficient-ring base change. -/
theorem algebraMap_snd_dual_positive
    (E : RingRootCell.WeylData A)
    (hE : E.toCellData = baseChangeCellData i a xm xp hm hp hopen A)
    [IsAffine E.G.X.left]
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
      rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x)) :
    algebraMap R A
        (((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x).snd) =
      -(↑E.betaUnit⁻¹ : A) := by
  obtain ⟨tA, hf⟩ := dualFactorization_baseChange i a xm xp hm hp hopen A hx
  have h := E.snd_dual_positive_of_cellData_eq
    (baseChangeCellData i a xm xp hm hp hopen A) hE hf
  change ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).hom
    ((Spec.map (CommRingCat.ofHom
      (RingRootCell.DualCell.coefficientMap (R := R) A).toRingHom)).appTop x)).snd = _ at h
  rw [ΓSpecIso_hom_specMap_appTop] at h
  change (RingRootCell.DualCell.coefficientMap A
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom x)).snd = _ at h
  rw [RingRootCell.DualCell.snd_coefficientMap] at h
  exact h

/-- Negating the original positive epsilon coefficient gives precisely the
inverse beta unit after coefficient extension. -/
theorem algebraMap_normalizationScalar
    (E : RingRootCell.WeylData A)
    (hE : E.toCellData = baseChangeCellData i a xm xp hm hp hopen A)
    [IsAffine E.G.X.left]
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : rootPoint xp (dualOver R) 1 * rootPoint xm (dualOver R) (epsSec R) =
      rootPoint xm (dualOver R) y * ((t ≫ i.hom.hom) * rootPoint xp (dualOver R) x)) :
    algebraMap R A (RingRootCell.DualCell.normalizationScalar x) =
      (↑E.betaUnit⁻¹ : A) := by
  unfold RingRootCell.DualCell.normalizationScalar
  rw [map_neg, algebraMap_snd_dual_positive i a xm xp hm hp hopen A E hE hx,
    neg_neg]

end LocalRankOneCell

end Langlands.GroupScheme
