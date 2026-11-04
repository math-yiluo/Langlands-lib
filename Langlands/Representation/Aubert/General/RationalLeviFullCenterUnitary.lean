import Langlands.Representation.Aubert.General.RationalLeviCentralCharacterNorms
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessStatement
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Langlands.GroupScheme.Rational.CanonicalStandardLeviCenterStatements
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentStatement

/-! # Extending unit modulus from the actual central torus to the full Levi center -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.PositiveCharacter

universe uH

/-- A smooth complex character unitary on a subgroup with compact quotient
is unitary on the whole group. -/
theorem norm_eq_one_of_compact_quotient
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K : Subgroup H) [K.Normal] [CompactSpace (H ⧸ K)]
    (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))
    (hK : ∀ x ∈ K, ‖(χ x : ℂ)‖ = 1) (x : H) :
    ‖(χ x : ℂ)‖ = 1 := by
  have hle : K ≤ (normCharacter χ).ker := by
    intro y hy
    apply Units.ext
    apply NNReal.eq
    exact hK y hy
  let ψ := QuotientGroup.lift K (normCharacter χ) hle
  have hpre : QuotientGroup.mk ⁻¹' (ψ.ker : Set (H ⧸ K)) =
      ((normCharacter χ).ker : Set H) := by
    ext y
    rfl
  have hopen : IsOpen (ψ.ker : Set (H ⧸ K)) := by
    apply (QuotientGroup.isQuotientMap_mk K).isOpen_preimage.mp
    rw [hpre]
    exact isOpen_ker_normCharacter χ hχ
  have hone := eq_one_of_compact ψ hopen (QuotientGroup.mk x)
  exact congrArg (fun y : ℝ≥0ˣ => ((y : ℝ≥0) : ℝ)) hone

end Langlands.PositiveCharacter

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance fullCenterAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology
local instance fullCenterAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The full scheme center of a represented actual Levi maps onto its full
abstract point-group center. -/
theorem surjective_leviSchemeCenterToCenter
    (I : Finset (SimpleRoot i ν))
    (M : GroupScheme (Spec (CommRingCat.of k))) (hM : IsConnectedReductive M)
    (j : M ⟶ G) (hj : (standardLevi i ν (rootSet i ν I)).IsRepresentedBy j) :
    Function.Surjective (standardLeviSchemeCenterToCenter i ν (rootSet i ν I) j hj) := by
  intro z
  let e := Subgroup.centerCongr
    (standardLeviRationalPointsEquiv i ν (rootSet i ν I) j hj)
  let w := e.symm z
  have hw : w.val ∈ schemeCenterPoints M := by
    rw [rationalCenterComparison k M hM]
    exact w.property
  refine ⟨⟨w.val, hw⟩, ?_⟩
  exact e.apply_symm_apply z

/-- Unit modulus on the literal Levi-central torus extends to the entire
actual Levi center through its full scheme-center quotient. -/
theorem leviCentralCharacter_norm_eq_one_of_splitComponent
    (I : Finset (SimpleRoot i ν))
    (M : GroupScheme (Spec (CommRingCat.of k))) (hM : IsConnectedReductive M)
    (j : M ⟶ G) (hj : (standardLevi i ν (rootSet i ν I)).IsRepresentedBy j)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
    (ha : IsSplitComponent a) (g : A.toGrp ⟶ T.toGrp) (hcomp : g ≫ i = a ≫ j)
    (hcompact : CenterSplitComponentCompactness M hM A a ha)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (htorus : ∀ t : leviCentralTorusPoints i ν I,
      ‖(χ (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1)
    (z : Subgroup.center (levi i ν I)) :
    ‖(χ z : ℂ)‖ = 1 := by
  let := hM.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let := hM.smooth
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology k M.X
  let : IsTopologicalGroup (rationalPoints M) := rationalPoint_isTopologicalGroup k M
  let centerMap : schemeCenterPoints M →* Subgroup.center (levi i ν I) :=
    standardLeviSchemeCenterToCenter i ν (rootSet i ν I) j hj
  have hcenterMap : Continuous centerMap :=
    (((continuous_rationalPointMap k j.hom.hom).comp
      continuous_subtype_val).subtype_mk _).subtype_mk _
  let K := centralRationalPointImage a ha.isCentralSplitTorus.isCentral
  let : CompactSpace (schemeCenterPoints M ⧸ K) := hcompact
  have hK : ∀ y ∈ K, ‖((χ.comp centerMap) y : ℂ)‖ = 1 := by
    rintro y ⟨x, rfl⟩
    have hval :
        ((centerMap (centralRationalPointsMap a ha.isCentralSplitTorus.isCentral x)).val :
          rationalPoints G) = rationalPoints.map i (rationalPoints.map g x) := by
      change (x ≫ a.hom.hom) ≫ j.hom.hom = (x ≫ g.hom.hom) ≫ i.hom.hom
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun f => x ≫ f)
        (congrArg (fun f : A.toGrp ⟶ G => f.hom.hom) hcomp).symm
    let t : leviCentralTorusPoints i ν I :=
      ⟨rationalPoints.map g x,
        (mem_leviCentralTorusPoints_iff i ν I _).mpr
          ⟨centerMap (centralRationalPointsMap a ha.isCentralSplitTorus.isCentral x), hval⟩⟩
    have heq : leviCentralTorusPointToCenter i ν I t =
        centerMap (centralRationalPointsMap a ha.isCentralSplitTorus.isCentral x) := by
      apply Subtype.ext
      apply Subtype.ext
      exact hval.symm
    simpa only [heq, MonoidHom.comp_apply] using htorus t
  obtain ⟨y, rfl⟩ := surjective_leviSchemeCenterToCenter i ν I M hM j hj z
  exact PositiveCharacter.norm_eq_one_of_compact_quotient K (χ.comp centerMap)
    (hχ.preimage hcenterMap) hK y

/-- The actual structural split-component and compact-center statements
discharge the displayed structural data of the full-center argument. -/
theorem leviCentralCharacter_norm_eq_one_of_structural_statements
    (hSplit : StandardLeviSplitComponentStatement.{u})
    (hCompact : CenterSplitComponentCompactnessStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (htorus : ∀ t : leviCentralTorusPoints i ν I,
      ‖(χ (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1)
    (z : Subgroup.center (levi i ν I)) :
    ‖(χ z : ℂ)‖ = 1 := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨hM, A, a, g, ha, hcomp⟩ :=
    hSplit k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  exact leviCentralCharacter_norm_eq_one_of_splitComponent i ν I
    (Standard.leviScheme i ν (rootSet i ν I)) hM
    (Standard.leviHom i ν (rootSet i ν I))
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
    A a ha g hcomp
    (hCompact k _ hM A a ha) χ hχ htorus z

/-- A supplied scalar character with unit modulus on the central torus gives
the actual unitary central-character datum after the structural inputs. -/
def leviUnitaryCentralCharacter_of_centralTorus
    (hSplit : StandardLeviSplitComponentStatement.{u})
    (hCompact : CenterSplitComponentCompactnessStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (levi i ν I) V)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (htorus : ∀ t : leviCentralTorusPoints i ν I,
      ‖(χ (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1)
    (hacts : ∀ (z : Subgroup.center (levi i ν I)) (v : V),
      ρ z v = (χ z : ℂ) • v) :
    UnitaryCentralCharacter ρ where
  character := χ
  isOpen_ker := hχ
  norm_eq_one := leviCentralCharacter_norm_eq_one_of_structural_statements
    i ν hSplit hCompact hG hi hν I χ hχ htorus
  acts := hacts

end Langlands.Aubert.General.RationalPointFamily
