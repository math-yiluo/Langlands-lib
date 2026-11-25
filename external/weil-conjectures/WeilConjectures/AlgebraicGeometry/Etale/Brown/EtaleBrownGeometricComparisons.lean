/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelComparisons
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProperSingletonEvaluation
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenSingletonEvaluation

/-! # Canonical projection and left-extension comparisons

Source: Zheng, Lemma 5.13 and the proof of Lemma 5.16, printed pp. 34--35.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive
variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Proper inverse image commutes with singleton extension by conjugating the fixed
right-adjoint evaluation comparison.
Source: Zheng, Lemma 5.13, printed p. 34
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
def strictEtaleBrownProperInsertion (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    S.PY.derivedExtension n ⋙ S.properDerived.system.inverse ≅
      (S.properDerived.level n).inverse ⋙ S.PZ.derivedExtension n :=
  ((conjugateIsoEquiv
    ((S.PY.derivedAdj n).comp S.properDerived.system.adjunction)
    (((S.properDerived.level n).adjunction).comp (S.PZ.derivedAdj n))).symm
      (S.properDerived.directEvaluation n)).symm

/-- The conjugate is exactly the specified proper evaluation comparison.
Source: Zheng, Lemma 5.13, printed p. 34
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
theorem strictEtaleBrownProperInsertion_conjugate
    (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    conjugateEquiv
      ((S.PY.derivedAdj n).comp S.properDerived.system.adjunction)
      (((S.properDerived.level n).adjunction).comp (S.PZ.derivedAdj n))
      (strictEtaleBrownProperInsertion O t c S n).inv =
        (S.properDerived.directEvaluation n).hom := by
  exact Equiv.apply_symm_apply _ _

/-- Open extension commutes with singleton extension by conjugating the fixed
inverse-image evaluation comparison.
Source: Zheng, Construction 5.14 and Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
def strictEtaleBrownOpenInsertion (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    S.PX.derivedExtension n ⋙ S.derivedOpen ≅
      S.levelDerivedOpen n ⋙ S.PZ.derivedExtension n :=
  ((conjugateIsoEquiv
    ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
    ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))).symm
      (S.openDerived.inverseEvaluation n)).symm

/-- The conjugate is exactly the specified open inverse-evaluation comparison.
Source: Zheng, Construction 5.14 and Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
theorem strictEtaleBrownOpenInsertion_conjugate
    (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    conjugateEquiv
      ((S.PX.derivedAdj n).comp S.derivedOpenAdjunction)
      ((S.levelDerivedOpenAdjunction n).comp (S.PZ.derivedAdj n))
      (strictEtaleBrownOpenInsertion O t c S n).inv =
        (S.openDerived.inverseEvaluation n).hom := by
  exact Equiv.apply_symm_apply _ _

/-- The actual proper singleton mate, defined before evaluating it.
Source: Zheng, Lemma 5.13, printed p. 34
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
def strictEtaleBrownProperInsertionMap (S : StrictEtaleCompactSupport O t c) (n : ℕ) :
    (S.properDerived.level n).direct ⋙ S.PY.derivedExtension n ⟶
      S.PZ.derivedExtension n ⋙ S.properDerived.system.direct :=
  (mateEquiv (S.properDerived.level n).adjunction S.properDerived.system.adjunction
    (.mk _ _ _ _ (strictEtaleBrownProperInsertion O t c S n).hom))

/-- Above the selected level the proper singleton mate is a map between zero objects.
Source: Zheng, Lemma 5.13, printed p. 34
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
theorem strictEtaleBrownProperInsertionMap_above
    (S : StrictEtaleCompactSupport O t c) (n m : ℕ) (h : n < m)
    (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
    IsIso ((S.PY.evaluation m).map
      ((strictEtaleBrownProperInsertionMap O t c S n).app P)) := by
  have : (S.properDerived.level m).direct.IsRightAdjoint :=
    ⟨_, ⟨(S.properDerived.level m).adjunction⟩⟩
  have hsrc := S.PY.derivedAbove n m h ((S.properDerived.level n).direct.obj P)
  have hz := S.PZ.derivedAbove n m h P
  have htgt : IsZero ((S.PY.evaluation m).obj
      (S.properDerived.system.direct.obj ((S.PZ.derivedExtension n).obj P))) :=
    ((S.properDerived.directEvaluation m).app _).isZero_iff.mpr
      ((S.properDerived.level m).direct.map_isZero hz)
  exact hsrc.isIso htgt _

/-- Evaluation jointly detects isomorphisms for every recorded strict-system model.
Source: Zheng, Lemma 4.10, printed pp. 23--24
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
theorem strictEtaleBrownEvaluation_detectsIso (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t)
    {M N : DerivedCategory (strictEtaleCoefficientSystem W O t)} (a : M ⟶ N) :
    IsIso a ↔ ∀ n : ℕ, IsIso ((P.evaluation n).map a) := by
  exact coefficientEvaluation_detectsIso O t P a

/-- Joint detection upgrades invertibility below n to the canonical singleton mate
isomorphism; the above-n cases were proved separately.
Source: Zheng, Lemma 5.13, printed p. 34
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
def strictEtaleBrownProperInsertionMate (S : StrictEtaleCompactSupport O t c)
    (hbelow : ∀ (n m : ℕ), m ≤ n →
      ∀ P : DerivedCategory (strictEtaleLevel c.Z O t n),
        IsIso ((S.PY.evaluation m).map
          ((strictEtaleBrownProperInsertionMap O t c S n).app P))) (n : ℕ) :
    (S.properDerived.level n).direct ⋙ S.PY.derivedExtension n ≅
      S.PZ.derivedExtension n ⋙ S.properDerived.system.direct := by
  have : IsIso (strictEtaleBrownProperInsertionMap O t c S n) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    apply (strictEtaleBrownEvaluation_detectsIso O t Y S.PY _).2
    intro m
    rcases le_or_gt m n with hm | hm
    · exact hbelow n m hm P
    · exact strictEtaleBrownProperInsertionMap_above O t c S n m hm P
  exact asIso (strictEtaleBrownProperInsertionMap O t c S n)

/-- The compact-support singleton comparison is the composite of the open insertion
and the inverse proper mate.
Source: Zheng, Construction 5.15 and Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
def strictEtaleBrownLeftExtension (S : StrictEtaleCompactSupport O t c)
    (hbelow : ∀ (n m : ℕ), m ≤ n →
      ∀ P : DerivedCategory (strictEtaleLevel c.Z O t n),
        IsIso ((S.PY.evaluation m).map
          ((strictEtaleBrownProperInsertionMap O t c S n).app P))) (n : ℕ) :
    S.PX.derivedExtension n ⋙ S.functor ≅ S.levelFunctor n ⋙ S.PY.derivedExtension n :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (strictEtaleBrownOpenInsertion O t c S n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (strictEtaleBrownProperInsertionMate O t c S hbelow n).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical geometric comparisons, independently of the Brown right adjoint.
Source: Zheng, Lemma 5.13 and Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-geometric-comparisons). -/
structure StrictEtaleBrownGeometry (S : StrictEtaleCompactSupport O t c) where
  realizationX : StrictEtaleBrownRealization O t X S.PX
  realizationZ : StrictEtaleBrownRealization O t c.Z S.PZ
  realizationY : StrictEtaleBrownRealization O t Y S.PY
  properRealization : ∀ n, StrictEtaleBrownImageRealization O t c.g n
    S.properImage (S.properDerived.level n) realizationZ realizationY
  openRealization : ∀ n, StrictEtaleBrownImageRealization O t c.i n
    S.openImage (S.openDerived.level n) realizationX realizationZ
  openComparison : ∀ n, S.levelDerivedOpen n ⋙ realizationZ.derived n ≅
    realizationX.derived n ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory
  openComparison_mate : ∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n)
      (((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
      (.mk _ _ _ _ (openComparison n).inv)) = (openRealization n).inverse.inv
  levelComparison : ∀ n, S.levelFunctor n ⋙ realizationY.derived n ≅
    realizationX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  levelComparison_def : ∀ n, levelComparison n =
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (properRealization n).right ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (openComparison n) _ ≪≫
      Functor.associator _ _ _
  openProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived
  openMate : ∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ (openProjection h).hom)) = (S.openDerived.derivedTensor h).inv
  properProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level m).direct ≅
      (S.properDerived.level n).direct ⋙ (S.PY.scalar h).derived
  properMate : ∀ {m n : ℕ} (h : m ≤ n),
    (properProjection h).inv =
      (mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom))
  projection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).derived
  projection_def : ∀ {m n : ℕ} (h : m ≤ n),
    projection h = (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (openProjection h) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (properProjection h) ≪≫ (Functor.associator _ _ _).symm
  projection_recorded_q : ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
        ((levelComparison n).inv.app P) ≫
      (realizationY.scalar h).inv.app ((S.levelFunctor n).obj P) ≫
      (realizationY.derived m).map ((projection h).inv.app P) ≫
      (levelComparison m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
          ((realizationX.scalar h).hom.app P) =
    (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
      ((realizationX.derived n).obj P)
  properInsertionBelow : ∀ (n m : ℕ), m ≤ n →
    ∀ P : DerivedCategory (strictEtaleLevel c.Z O t n),
      IsIso ((S.PY.evaluation m).map
        ((strictEtaleBrownProperInsertionMap O t c S n).app P))
  leftExtension_below : ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (S.PY.evaluation m).map
        ((strictEtaleBrownLeftExtension O t c S properInsertionBelow n).hom.app P) ≫
      (S.PY.derivedBelow h).hom.app ((S.levelFunctor n).obj P) =
    (S.evaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
      (S.levelFunctor m).map ((S.PX.derivedBelow h).hom.app P) ≫
        (projection h).hom.app P

private theorem properInsertionMate_hom (S : StrictEtaleCompactSupport O t c)
    (hbelow : ∀ (n m : ℕ), m ≤ n →
      ∀ P : DerivedCategory (strictEtaleLevel c.Z O t n),
        IsIso ((S.PY.evaluation m).map
          ((strictEtaleBrownProperInsertionMap O t c S n).app P))) (n : ℕ) :
    (strictEtaleBrownProperInsertionMate O t c S hbelow n).hom =
      strictEtaleBrownProperInsertionMap O t c S n := rfl

attribute [local irreducible] strictEtaleBrownProperInsertionMate

private theorem inverse_square
    {A B : Type*} [Category A] [Category B] (E : A ⥤ B)
    {X Y : A} {U V : B} (a : X ≅ Y) (b : E.obj X ⟶ U) (c : E.obj Y ⟶ V)
    (d : U ≅ V) (h : E.map a.hom ≫ c = b ≫ d.hom) :
    E.map a.inv ≫ b = c ≫ d.inv := by
  apply (cancel_epi (E.map a.hom)).mp
  rw [← Category.assoc, ← E.map_comp, a.hom_inv_id, E.map_id, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, d.hom_inv_id, Category.comp_id]

private theorem paste_evaluation_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {G : A ⥤ B} {E : B ⥤ C} {H : A ⥤ D} {F : D ⥤ C}
    (e : G ⋙ E ≅ H ⋙ F) {X Y : A} {Z : D} {T : C}
    (a : X ⟶ Y) (b : E.obj (G.obj Y) ⟶ T) (c : H.obj Y ⟶ Z) (d : F.obj Z ⟶ T)
    (hb : b = e.hom.app Y ≫ F.map c ≫ d) :
    E.map (G.map a) ≫ b = e.hom.app X ≫ F.map (H.map a ≫ c) ≫ d := by
  have hn : E.map (G.map a) ≫ e.hom.app Y = e.hom.app X ≫ F.map (H.map a) :=
    e.hom.naturality a
  rw [hb, ← Category.assoc, ← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]

/-- The geometric projection and singleton comparisons for a fixed compact-support
presentation, before Brown representability is applied.
Source: Zheng, Lemma 5.13 and the proof of Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-geometric-comparisons).

Proof: identify modules over the constant quotient sheaf with sheaves over the quotient
ring by restriction along the constant-sheaf unit. Exact localization gives the derived
realizations. Scalar adjoint uniqueness gives their normalized scalar comparisons.
Ordinary direct image agrees on sections in these encodings; the universal right-derived
unit determines its comparison on derived categories, and its mate determines inverse
image. For the open part take the mate against the extension/restriction adjunction.
The proper derived tensor comparison has a right mate whose inverse is the coefficient
projection isomorphism of the proper map with identity open part. The open comparison is
the scalar-balancing isomorphism. Compose them to obtain projection and levelComparison;
the scalar transpose equations identify its inverse with compactScalarMap.
Next conjugate the proper evaluation comparison under the two composite adjunctions
L_n followed by inverse image and inverse image followed by L_n. The resulting
properInsertion is invertible by conjugate uniqueness. Take its proper mate, a map
constructed in the derived category of strict systems. Below n its evaluation is the
proper coefficient projection by the normalized singleton transpose formula, hence
invertible; above n both sides vanish. Joint detection makes properInsertionMate an
isomorphism. Conjugate the open inverse-evaluation comparison in the same way to obtain
openInsertion. Compose openInsertion and the inverse of properInsertionMate to obtain
leftExtension. Mate pasting and the singleton scalar-transpose formula identify its
evaluation below n with the composite projection, giving leftExtension_below.
All maps are constructed before evaluation; no faithfulness of derived evaluation is
used. The coefficient projection theorem applies to the finite l-power-torsion rings
specified in the hypotheses, including identity coefficient transitions. -/
theorem etaleBrownGeometricComparisons
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hfinite : ∀ n : ℕ, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n : ℕ, ∃ a : ℕ, (l ^ a : strictEtaleBrownRing O t n) = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (S : StrictEtaleCompactSupport O t c) :
    Nonempty (StrictEtaleBrownGeometry O t c S) := by
  obtain ⟨RX, RZ, RY, rp, ro, jo, op, pp, hjo, hop, hpp, hrecord⟩ :=
    etaleBrownLevelComparisons D l hl O t hfinite htorsion f c S
  let lc (n : ℕ) : S.levelFunctor n ⋙ RY.derived n ≅
      RX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (rp n).right ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (jo n) _ ≪≫
      Functor.associator _ _ _
  let q {m n : ℕ} (h : m ≤ n) : (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).derived :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (op h) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (pp h) ≪≫ (Functor.associator _ _ _).symm
  have hproper {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      (S.PY.evaluation m).map ((strictEtaleBrownProperInsertionMap O t c S n).app P) ≫
        (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) =
      (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) ≫
        (pp h).inv.app P := by
    exact etaleBrownProperSingletonEvaluation O t c S h (pp h) (hpp h) P
  have hbelow (n m : ℕ) (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      IsIso ((S.PY.evaluation m).map
        ((strictEtaleBrownProperInsertionMap O t c S n).app P)) := by
    have hi : IsIso
        ((S.PY.evaluation m).map ((strictEtaleBrownProperInsertionMap O t c S n).app P) ≫
          (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
          (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P)) := by
      rw [hproper h P]
      infer_instance
    simpa only [isIso_comp_right_iff] using hi
  have hproperInv {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      (S.PY.evaluation m).map
          ((strictEtaleBrownProperInsertionMate O t c S hbelow n).inv.app P) ≫
        (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) =
      (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) ≫
        (pp h).hom.app P := by
    let a := (strictEtaleBrownProperInsertionMate O t c S hbelow n).app P
    have ha : (S.PY.evaluation m).map a.hom ≫
        (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) =
        (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) ≫
          (pp h).inv.app P := by
      simpa only [a, Iso.app_hom, properInsertionMate_hom] using hproper h P
    exact (inverse_square (S.PY.evaluation m) a
      ((S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P))
      ((S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P))
      ((pp h).app P).symm ha).trans (Category.assoc _ _ _)
  have hopen {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel X O t n)) :
      (S.PZ.evaluation m).map ((strictEtaleBrownOpenInsertion O t c S n).hom.app P) ≫
        (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
      (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
        (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ (op h).hom.app P := by
    exact etaleBrownOpenSingletonEvaluation O t c S h (op h) (hop h) P
  refine ⟨{
    realizationX := RX
    realizationZ := RZ
    realizationY := RY
    properRealization := rp
    openRealization := ro
    openComparison := jo
    openComparison_mate := hjo
    levelComparison := lc
    levelComparison_def := fun _ ↦ rfl
    openProjection := op
    openMate := hop
    properProjection := pp
    properMate := hpp
    projection := q
    projection_def := fun _ ↦ rfl
    projection_recorded_q := hrecord
    properInsertionBelow := hbelow
    leftExtension_below := ?_ }⟩
  intro m n h P
  have he := paste_evaluation_square (S.properDerived.directEvaluation m)
    ((strictEtaleBrownOpenInsertion O t c S n).hom.app P)
    ((S.PY.evaluation m).map
        ((strictEtaleBrownProperInsertionMate O t c S hbelow n).inv.app
          ((S.levelDerivedOpen n).obj P)) ≫
      (S.PY.derivedBelow h).hom.app ((S.levelFunctor n).obj P))
    ((S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P))
    ((pp h).hom.app ((S.levelDerivedOpen n).obj P))
    (hproperInv h ((S.levelDerivedOpen n).obj P))
  have ho := congrArg
    (fun z ↦ (S.properDerived.directEvaluation m).hom.app
        (S.derivedOpen.obj ((S.PX.derivedExtension n).obj P)) ≫
      (S.properDerived.level m).direct.map z ≫
        (pp h).hom.app ((S.levelDerivedOpen n).obj P)) (hopen h P)
  have hp := he.trans ho
  simp only [strictEtaleBrownLeftExtension, q, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, CategoryTheory.Functor.map_comp, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc,
    StrictEtaleCompactSupport.evaluation,
    StrictEtaleCompactSupport.levelFunctor]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hp
  dsimp only [StrictEtaleCompactSupport.functor, StrictEtaleCompactSupport.levelFunctor,
    Functor.comp_obj, Functor.comp_map] at hp ⊢
  exact hp

end AlgebraicGeometry
