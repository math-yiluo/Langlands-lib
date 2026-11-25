/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # The bounded rational t-structure

The category is the raw scalar localization of the completed integral category.
The last, levelwise computation carries its explicit higher-Tor hypothesis.

## References

* BBD 1.3.3--1.3.6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

set_option linter.defProp false in
/-- The existing scalar-localization theorem specialized to the integral category.
It fixes the induced shift, the identity comparison for Q, and exactly the isomorphic
images of integral distinguished triangles. -/
abbrev pbcLocalizedTriangulationData :=
  ScalarLocalization.exists_triangulated_scalarLocalization (PbcIntegralRing l E)
    (PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (pbcUniformizer l E)

/-- The localized zero object, supplied by scalar localization. -/
instance pbcLocalizedZero : HasZeroObject
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  (pbcLocalizedTriangulationData T l E).choose

/-- The induced rational integer shift. -/
instance pbcLocalizedShift : HasShift
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) ℤ :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose

/-- Additivity of the induced shifts. -/
instance pbcLocalizedShiftAdditive (n : ℤ) :
    Functor.Additive
      (shiftFunctor (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) n) :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose n

/-- The canonical comparison between localization and shifts. -/
instance pbcLocalizedCommShift :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).CommShift ℤ :=
  (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose

/-- Distinguished triangles are exactly the isomorphic images of integral ones. -/
instance pbcLocalizedPretriangulated : Pretriangulated
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  Exists.choose
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2

/-- Octahedra descend to the raw scalar localization. -/
instance pbcLocalizedIsTriangulated : IsTriangulated
    (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  And.left (Exists.choose_spec
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2)

/-- Q is exact for precisely this induced triangulation. -/
instance pbcLocalizedQIsTriangulated :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).IsTriangulated :=
  And.left (And.right (Exists.choose_spec
    (pbcLocalizedTriangulationData T l E).choose_spec.choose_spec.2.choose_spec.choose_spec.2))

/-- Rationalization descends the bounded standard integral t-structure. Its two parts
are the strictly full images of the integral parts; Q is t-exact and commutes naturally
with both canonical truncations. The heart is the image of a single integral heart
object. Under the stated Tor condition, rational truncations are also the images of
the Roos limits of the levelwise truncated normalized reduction tower. -/
theorem pbc_localized_tstructure :
    ∃ tE : Triangulated.TStructure
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)),
      (∀ X : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E),
        (tE.le 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).le 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L)) ∧
        (tE.ge 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).ge 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L))) ∧
      tE.bounded = ⊤ ∧
      (∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (m : ℤ),
        ((pbcIntegralTStructure T l E).le m K →
          tE.le m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K)) ∧
        ((pbcIntegralTStructure T l E).ge m K →
          tE.ge m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K))) ∧
      (∀ m : ℤ,
        Nonempty (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
            tE.truncLE m ≅ (pbcIntegralTStructure T l E).truncLE m ⋙
              pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)) ∧
        Nonempty (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
            tE.truncGE m ≅ (pbcIntegralTStructure T l E).truncGE m ⋙
              pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E))) ∧
      (∀ X : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E),
        tE.heart X ↔
          ∃ H : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).heart H ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj H)) ∧
      ∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
        (_hTor : PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj) (m : ℤ),
        ∃ L U : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
          IsDerivedLimit
            (K := fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).obj
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
            (fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).map
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
                (homOfLE (Nat.le_succ n)).op)) L.obj ∧
          IsDerivedLimit
            (K := fun n ↦ ((pbcAmbientTStructure T l E).truncGE m).obj
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
            (fun n ↦ ((pbcAmbientTStructure T l E).truncGE m).map
              ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
                (homOfLE (Nat.le_succ n)).op)) U.obj ∧
          Nonempty ((tE.truncLE m).obj
              ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≅
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L) ∧
          Nonempty ((tE.truncGE m).obj
              ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≅
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj U) := by
  obtain ⟨tE, hImage, hExact⟩ :
    ∃ tE : Triangulated.TStructure
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)),
      (∀ X : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E),
        (tE.le 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).le 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L)) ∧
        (tE.ge 0 X ↔
          ∃ L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
            (pbcIntegralTStructure T l E).ge 0 L ∧
              Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
                (pbcUniformizer l E)).obj L))) ∧
      (∀ (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (m : ℤ),
        ((pbcIntegralTStructure T l E).le m K →
          tE.le m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K)) ∧
        ((pbcIntegralTStructure T l E).ge m K →
          tE.ge m ((pbcRationalization T (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K))) := by
    classical
    let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
    let tA := pbcIntegralTStructure T l E
    let leP : ℤ → ObjectProperty
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
      fun n ↦ (tA.le n).map Q
    let geP : ℤ → ObjectProperty
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
      fun n ↦ (tA.ge n).map Q
    let tE : Triangulated.TStructure
        (PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) := {
      le := leP
      ge := geP
      le_shift := by
        rintro n a n' h X ⟨L, hL, ⟨e⟩⟩
        exact ⟨L⟦a⟧, tA.le_shift n a n' h L hL,
          ⟨(Q.commShiftIso a).app L ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
      ge_shift := by
        rintro n a n' h X ⟨L, hL, ⟨e⟩⟩
        exact ⟨L⟦a⟧, tA.ge_shift n a n' h L hL,
          ⟨(Q.commShiftIso a).app L ≪≫ (shiftFunctor _ a).mapIso e⟩⟩
      zero' := by
        rintro X Y f ⟨K, hK, ⟨e⟩⟩ ⟨L, hL, ⟨d⟩⟩
        have hf : e.hom ≫ f ≫ d.inv = 0 := by
          dsimp only [Q, pbcRationalization, ScalarLocalization.localization,
            ScalarLocalization.category] at *
          generalize e.hom ≫ f ≫ d.inv = g
          induction g using TensorProduct.inductionOn with
          | tmul a g => rw [tA.zero' g hK hL, TensorProduct.tmul_zero]
          | add g g' hg hg' => rw [hg, hg', add_zero]
        calc
          f = e.inv ≫ (e.hom ≫ f ≫ d.inv) ≫ d.hom := by simp
          _ = 0 := by rw [hf]; simp
      le_zero_le := ObjectProperty.map_monotone tA.le_zero_le Q
      ge_one_le := ObjectProperty.map_monotone tA.ge_one_le Q
      exists_triangle_zero_one := by
        intro A
        obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := tA.exists_triangle_zero_one A.obj
        exact ⟨Q.obj X, Q.obj Y, (tA.le 0).prop_map_obj Q hX,
          (tA.ge 1).prop_map_obj Q hY, Q.map f, Q.map g,
          Q.map h ≫ ((Q.commShiftIso (1 : ℤ)).hom.app X),
          Q.map_distinguished _ hT⟩ }
    refine ⟨tE, ?_, ?_⟩
    · intro X
      constructor
      all_goals
        constructor
        · rintro ⟨L, hL, ⟨e⟩⟩
          exact ⟨L, hL, ⟨e.symm⟩⟩
        · rintro ⟨L, hL, ⟨e⟩⟩
          exact ⟨L, hL, ⟨e.symm⟩⟩
    · intro K m
      exact ⟨fun h ↦ (tA.le m).prop_map_obj Q h,
        fun h ↦ (tA.ge m).prop_map_obj Q h⟩
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let tA := pbcIntegralTStructure T l E
  have : Q.IsTExact tA tE := by
    constructor
    · intro K m hK
      exact ⟨(hExact K m).1 hK.le⟩
    · intro K m hK
      exact ⟨(hExact K m).2 hK.ge⟩
  have hTrunc : ∀ m : ℤ,
      Nonempty (Q ⋙ tE.truncLE m ≅ tA.truncLE m ⋙ Q) ∧
      Nonempty (Q ⋙ tE.truncGE m ≅ tA.truncGE m ⋙ Q) := by
    intro m
    constructor
    · exact ⟨(Q.eTruncLTIso tA tE (m + 1 : ℤ)).symm⟩
    · exact ⟨(Q.eTruncGEIso tA tE (m : ℤ)).symm⟩
  have hBounded : tE.bounded = ⊤ := by
    apply top_unique
    intro X _
    let K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) := X.obj
    have hK : (pbcIntegralTStructure T l E).bounded K := by
      rw [(pbc_integral_tstructure T l E).1]
      trivial
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
    exact ⟨⟨a, ⟨(hExact K a).2 ha.ge⟩⟩, ⟨b, ⟨(hExact K b).1 hb.le⟩⟩⟩
  have hHeart : ∀ X : PbcRationalCategory T (pbcIntegralDatum l E)
      (pbcUniformizer l E), tE.heart X ↔
        ∃ H : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
          (pbcIntegralTStructure T l E).heart H ∧
            Nonempty (X ≅ (pbcRationalization T (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj H) := by
    intro X
    let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
    let tA := pbcIntegralTStructure T l E
    constructor
    · intro hX
      have : tE.IsLE X 0 := ⟨hX.1⟩
      have : tE.IsGE X 0 := ⟨hX.2⟩
      let K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) := X.obj
      let H := (tA.homology₀.obj K).obj
      have hH : tA.heart H := (tA.homology₀.obj K).property
      let e₁ : X ≅ (tE.truncGE 0).obj ((tE.truncLE 0).obj X) :=
        (asIso ((tE.truncLEι 0).app X)).symm ≪≫
          asIso ((tE.truncGEπ 0).app ((tE.truncLE 0).obj X))
      let e₂ := (tE.truncGE 0).mapIso ((hTrunc 0).1.some.app K)
      let e₃ := (hTrunc 0).2.some.app ((tA.truncLE 0).obj K)
      exact ⟨H, hH, ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩⟩
    · rintro ⟨H, hH, ⟨e⟩⟩
      exact ⟨(tE.le 0).prop_of_iso e.symm ((hExact H 0).1 hH.1),
        (tE.ge 0).prop_of_iso e.symm ((hExact H 0).2 hH.2)⟩
  refine ⟨tE, hImage, hBounded, hExact, hTrunc, hHeart, ?_⟩
  intro K hTor m
  let L := (pbcIntegralTruncLE T l E m).obj K
  let U := (pbcIntegralTruncGE T l E m).obj K
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let ι := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
  let eL : ((pbcIntegralTStructure T l E).truncLE m).obj K ≅ L :=
    ι.preimageIso (((pbc_integral_tstructure T l E).2.2.1 m).1.some.app K)
  let eU : ((pbcIntegralTStructure T l E).truncGE m).obj K ≅ U :=
    ι.preimageIso (((pbc_integral_tstructure T l E).2.2.1 m).2.some.app K)
  refine ⟨L, U, (pbc_integral_truncations T l E K hTor m).1, ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, m = a + 1 := ⟨m - 1, by omega⟩
    exact (pbc_integral_truncations T l E K hTor a).2.1
  · exact ⟨((hTrunc m).1).some.app K ≪≫ Q.mapIso eL⟩
  · exact ⟨((hTrunc m).2).some.app K ≪≫ Q.mapIso eU⟩

end AlgebraicGeometry.Scheme
