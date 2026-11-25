/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfect
import WeilConjectures.AlgebraicGeometry.RightAdjointOpenUnitConeTest
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Extending bounded-below support preservation using sums

Source: Stacks Project, Duality for Schemes, Tag 0E4G.
-/

@[expose] public section

set_option autoImplicit false
universe u w v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry

private instance qcoh_tri (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    (schemeDerivedQCohProperty Z).IsTriangulated := by
  simpa [supportedProperty] using supported_qcoh_isTriangulated Z Set.univ

private instance qcoh_iso (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    (schemeDerivedQCohProperty Z).IsClosedUnderIsomorphisms where
  of_iso e hK n := (SheafOfModules.isQuasicoherent (moduleRings Z.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK n)

private theorem compact_lower_bound (Y : Scheme.{u}) [CompactSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y)
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E))) :
    ∃ a : ℤ, E.IsGE a := by
  classical
  choose U hx a hv using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y ↦ (U y : Set Y)) (fun y ↦ (U y).isOpen) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, hx y⟩)
  have hmin : ∃ b : ℤ, ∀ y ∈ s, b ≤ a y := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert y s hy ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨min (a y) b, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb z hz)
  obtain ⟨b, hb⟩ := hmin
  refine ⟨b, (DerivedCategory.isGE_iff E b).mpr ?_⟩
  intro n hn
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E
  apply (IsZero.iff_id_eq_zero M).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change x = 0
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro z hz
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ z))
  obtain ⟨hys, hzy⟩ := Set.mem_iUnion.mp hy
  let W := V.unop ⊓ U y
  have hzero := hv y n (hn.trans_le (hb y hys))
  let WO : Over (U y) := Over.mk (homOfLE (show W ≤ U y from inf_le_right))
  have hid := (IsZero.iff_id_eq_zero _).mp hzero
  refine ⟨W, inf_le_left, ⟨hz, hzy⟩, ?_⟩
  have hh := congrArg
    (fun f ↦ (f.val.app (Opposite.op WO)).hom
      (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op x)) hid
  change (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom x = 0 at hh
  change (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom x =
    (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom 0
  simpa only [map_zero] using hh


private theorem perfect_lower_bound (Y : Scheme.{u}) [CompactSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) (hp : Scheme.IsPerfect Y E) :
    ∃ a : ℤ, E.IsGE a := by
  apply compact_lower_bound Y E
  intro y
  obtain ⟨U, hy, K, ⟨⟨a, b, hzero⟩, hfree⟩, ⟨e⟩⟩ := hp y
  refine ⟨U, hy, a, ?_⟩
  let L := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  have hKa : K.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact HomologicalComplex.ExactAt.of_isZero (hzero n (Or.inl hn))
  have hQa : (DerivedCategory.Q.obj K).IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff K a).mpr hKa
  have hEa : (L.mapDerivedCategory.obj E).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  intro n hn
  have hz := (DerivedCategory.isGE_iff (L.mapDerivedCategory.obj E) a).mp hEa n hn
  exact hz.of_iso ((L.mapDerivedCategoryHomologyFunctorIso n).app E)

private def qcohTriangle (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (A B C : schemeDerivedQCohCategory Y) (g : A.obj ⟶ B.obj)
    (β : B.obj ⟶ C.obj) (δ : C.obj ⟶ A.obj⟦(1 : ℤ)⟧) :
    Triangle (schemeDerivedQCohCategory Y) :=
  Triangle.mk (ObjectProperty.homMk g) (ObjectProperty.homMk β)
    (ObjectProperty.homMk
      (δ ≫ ((schemeDerivedQCohProperty Y).ι.commShiftIso (1 : ℤ)).inv.app A))

private theorem qcohTriangle_distinguished (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (A B C : schemeDerivedQCohCategory Y) (g : A.obj ⟶ B.obj)
    (β : B.obj ⟶ C.obj) (δ : C.obj ⟶ A.obj⟦(1 : ℤ)⟧)
    (hT : Triangle.mk g β δ ∈ distTriang (schemeDerivedCategory Y)) :
    qcohTriangle Y A B C g β δ ∈ distTriang (schemeDerivedQCohCategory Y) := by
  change (schemeDerivedQCohProperty Y).ι.mapTriangle.obj
    (qcohTriangle Y A B C g β δ) ∈ distTriang _
  simpa [Functor.mapTriangle, Triangle.mk, qcohTriangle] using hT

private theorem cofan_killed (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {D : Type*} [Category D] [HasZeroMorphisms D]
    (I : Type v) (K : I → schemeDerivedQCohCategory Y)
    (A : I → schemeDerivedCategory Y) (e : ∀ i, (K i).obj ≅ A i)
    (S : Cofan A) (hc : IsColimit S) (hS : schemeDerivedQCohProperty Y S.pt)
    (G : schemeDerivedQCohCategory Y ⥤ D)
    [PreservesColimitsOfShape (Discrete I) G]
    (hK : ∀ i, IsZero (G.obj (K i))) :
    IsZero (G.obj ⟨S.pt, hS⟩) := by
  let q : Cofan K := Cofan.mk ⟨S.pt, hS⟩
    (fun i ↦ ObjectProperty.homMk ((e i).hom ≫ S.inj i))
  have hq : IsColimit q := by
    refine Cofan.IsColimit.mk q
      (fun s ↦ ObjectProperty.homMk
        (hc.desc (Cofan.mk s.pt.obj (fun i ↦ (e i).inv ≫ (s.inj i).hom)))) ?_ ?_
    · intro s i
      apply ObjectProperty.hom_ext _
      dsimp [q]
      rw [Category.assoc, Cofan.IsColimit.inj_desc]
      simp only [cofan_mk_inj]
      simp
    · intro s m hm
      apply ObjectProperty.hom_ext _
      apply hc.hom_ext
      intro ⟨i⟩
      apply (cancel_epi (e i).hom).mp
      change (e i).hom ≫ S.inj i ≫ m.hom =
        (e i).hom ≫ S.inj i ≫ hc.desc
          (Cofan.mk s.pt.obj (fun i ↦ (e i).inv ≫ (s.inj i).hom))
      rw [Cofan.IsColimit.inj_desc]
      simp only [cofan_mk_inj]
      simpa [q, Category.assoc] using congrArg (fun φ ↦ φ.hom) (hm i)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (isColimitOfPreserves G hq).hom_ext
  intro ⟨i⟩
  exact (hK i).eq_of_src _ _

/-- Preservation of support on bounded-below objects extends to every supported
object when the right adjoint preserves all set-indexed sums.
Source: Stacks Project, Tag 0E4G, proof of Lemma 48.4.3(3), using Tags 0A9A and 09SN.
(blueprint: lem-sc-right-adjoint-open-support-of-bounded).

Proof. Use nonempty_derivedOpenLocalization to supply the open-site derived
localizations in the ambient Hom universe. Put T = Y \ V. The supported quasi-coherent
derived category is generated
by a perfect supported complex E. Perfect complexes on a quasi-compact scheme
are bounded below: choose strictly perfect local models, take a finite subcover,
and take the minimum of their lower bounds. Exact restriction commutes with
homology and sheaves are detected locally, giving a uniform lower bound on Y.
Thus the hypothesis kills the restriction of a(E) to U.
The kernel of the exact functor a followed by ambient inclusion and restriction
to U is closed under shifts, cones, and retracts. It is also closed under all
set-indexed sums: a preserves them by hypothesis, and ambient inclusion and
exact open restriction preserve the quasi-coherent coproducts. Hence it contains
all sums of shifts of E. Every supported Q has the sequential construction of
supported_derived_generated_perfect, starting at zero, whose transition cones
are sums of shifts of E. Induction kills each stage. Applying the same functor
to the telescope triangle kills both copies of the sum of the stages, and thus
kills Q. Vanishing under restriction is equivalent to vanishing of all
cohomology stalks on V, so this construction applies to exactly the input support
condition. This proof includes empty and full opens, and uses preservation of
arbitrary sums only in the transition cones and telescope. -/
theorem rightAdjoint_open_support_of_bounded
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsCompact (V : Set Y))
    (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (hpush : ∀ K : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj K.obj))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush ⊣ a)
    (hsum : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) a)
    (hb : ∀ Q : schemeDerivedQCohCategory Y,
      (∃ n : ℤ, Q.obj.IsGE n) →
      IsZero ((schemeOpenRestriction Y V).mapDerivedCategory.obj Q.obj) →
      IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj (a.obj Q).obj)) :
    ∀ Q : schemeDerivedQCohCategory Y,
      IsZero ((schemeOpenRestriction Y V).mapDerivedCategory.obj Q.obj) →
      IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj (a.obj Q).obj) := by
  classical
  let := Classical.choice (nonempty_derivedOpenLocalization Y)
  obtain ⟨E, hperf, hEsupp, hgen⟩ := supported_derived_generated_perfect Y V hV
  let F := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush
  let : F.CommShift ℤ := inferInstance
  have : F.IsTriangulated := inferInstance
  let : a.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : a.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : a.Additive := adj.right_adjoint_additive
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let radj : L ⊣ R := (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
    (Scheme.Modules.overFunctorEquiv U).symm
  let : L.mapDerivedCategory.IsLeftAdjoint :=
    radj.mapDerivedCategoryRightDerivedAdjunction.isLeftAdjoint
  let : HasCoproducts.{u} (schemeDerivedCategory X) := derivedAmbientHasCoproducts X
  let G := a ⋙ (schemeDerivedQCohProperty X).ι ⋙ L.mapDerivedCategory
  have : G.IsTriangulated := inferInstance
  let : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G := fun I ↦ by
    let : PreservesColimitsOfShape (Discrete I) a := hsum I
    let : (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
      schemeDerivedQCohClosedUnderCoproducts X I
    dsimp [G]
    infer_instance
  have hE : IsZero (G.obj E) := hb E (perfect_lower_bound Y E.obj hperf)
    ((restriction_zero_iff_stalks Y V E.obj).mpr hEsupp)
  have hshift (m : ℤ) : IsZero (G.obj (E⟦m⟧)) :=
    ((shiftFunctor _ m).map_isZero hE).of_iso ((G.commShiftIso m).app E)
  intro Q hQ
  obtain ⟨T, t, hT0, hsteps, S, ⟨hS⟩, s, q, r, htrans, htelescope⟩ :=
    hgen Q ((restriction_zero_iff_stalks Y V Q.obj).mp hQ)
  have hstage : ∀ n, IsZero (G.obj (T n)) := by
    intro n
    induction n with
    | zero =>
        apply G.map_isZero
        apply (IsZero.iff_id_eq_zero _).mpr
        apply (schemeDerivedQCohProperty Y).ι.map_injective
        simpa using hT0.eq_of_src (𝟙 _) 0
    | succ n hn =>
        obtain ⟨I, m, C, ⟨hC⟩, β, δ, htriangle⟩ := hsteps n
        let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete I) :=
          schemeDerivedQCohClosedUnderCoproducts Y I
        have hCqc : schemeDerivedQCohProperty Y C.pt :=
          (schemeDerivedQCohProperty Y).prop_of_isColimit hC (fun ⟨i⟩ ↦
            (schemeDerivedQCohProperty Y).prop_of_iso
              (((schemeDerivedQCohProperty Y).ι.commShiftIso (m i)).app E)
              (E⟦m i⟧).property)
        have hCzero := cofan_killed Y I (fun i ↦ E⟦m i⟧) (fun i ↦ E.obj⟦m i⟧)
          (fun i ↦ ((schemeDerivedQCohProperty Y).ι.commShiftIso (m i)).app E)
          C hC hCqc G (fun i ↦ hshift (m i))
        let tri := qcohTriangle Y (T n) (T (n + 1)) ⟨C.pt, hCqc⟩ (t n) β δ
        have htri : tri ∈ distTriang _ :=
          qcohTriangle_distinguished Y _ _ _ _ _ _ htriangle
        exact Triangle.isZero₂_of_isZero₁₃ (G.mapTriangle.obj tri)
          (G.map_distinguished tri htri) hn hCzero
  let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape
      (Discrete (ULift.{u} ℕ)) := schemeDerivedQCohClosedUnderCoproducts Y _
  let : (schemeDerivedQCohProperty Y).IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence Equiv.ulift)
  let : PreservesColimitsOfShape (Discrete ℕ) G :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) G
  have hSqc : schemeDerivedQCohProperty Y S.pt :=
    (schemeDerivedQCohProperty Y).prop_of_isColimit hS (fun ⟨n⟩ ↦ (T n).property)
  have hSzero := cofan_killed Y ℕ T (fun n ↦ (T n).obj)
    (fun _ ↦ Iso.refl _) S hS hSqc G hstage
  let tri := qcohTriangle Y ⟨S.pt, hSqc⟩ ⟨S.pt, hSqc⟩ Q (𝟙 S.pt - s) q r
  have htri : tri ∈ distTriang _ :=
    qcohTriangle_distinguished Y _ _ _ _ _ _ htelescope
  exact Triangle.isZero₃_of_isZero₁₂ (G.mapTriangle.obj tri)
    (G.map_distinguished tri htri) hSzero hSzero

end AlgebraicGeometry
