import Langlands.AlgebraicGeometry.ProjectiveSpace.PointConfiguration
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionHyperplaneSections
import Langlands.AbelianScheme.PolarizedFiniteLevel.FibreDetection

/-! # Rigidity through the actual torsion-point configuration -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.ProjectiveSpace GroupScheme.Tate

universe u

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ)

/-- Every torsion section is an actual rational point over the coefficient field. -/
def torsionRationalPoints :
    Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n →
      {p : Spec (CommRingCat.of K) ⟶ A.X.left // p ≫ A.X.hom = 𝟙 _} :=
  fun x => ⟨(Additive.toMul x).val.left, (Additive.toMul x).val.w⟩

variable {A n} {m : ℕ}

/-- Compose every actual torsion section with a supplied projective-space map. -/
def torsionProjectivePointConfiguration
    (i : A.X.left ⟶ ProjectiveSpace K m)
    (hi : i ≫ projectiveSpaceToSpec K m = A.X.hom) :
    Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n →
      {p : Spec (CommRingCat.of K) ⟶ ProjectiveSpace K m //
        p ≫ projectiveSpaceToSpec K m = 𝟙 _} :=
  fun x => ⟨(torsionRationalPoints A n x).1 ≫ i, by
    rw [Category.assoc, hi, (torsionRationalPoints A n x).2]⟩

/-- A count for actual nonzero homogeneous linear polynomials is the configuration bound. -/
theorem torsionProjectivePointConfiguration_hyperplaneBound
    (i : A.X.left ⟶ ProjectiveSpace K m)
    (hi : i ≫ projectiveSpaceToSpec K m = A.X.hom) {q : ℕ}
    (h : ∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) i f) ≤ q) :
    RationalPointHyperplaneBound m (torsionProjectivePointConfiguration (n := n) i hi) q := by
  intro ℓ hℓ
  apply h (linearFormPolynomialEquiv K m ℓ)
  intro hz
  apply hℓ
  apply (linearFormPolynomialEquiv K m).injective
  apply Subtype.ext
  simpa only [map_zero, Submodule.coe_zero] using hz

/-- Identity of the underlying scheme map determines the actual polarized automorphism. -/
theorem PolarizedIso.eq_refl_of_hom_eq_id {S : Scheme.{u}} {P : Prerequisites.{u}}
    {g d n : ℕ} {a : Datum P S g d n} (α : PolarizedIso a a)
    (h : hom α.abelianIso.hom = 𝟙 a.abelian.X.left) :
    α = PolarizedIso.refl a := by
  have ha : α.abelianIso = CategoryTheory.Iso.refl a.abelian := by
    apply CategoryTheory.Iso.ext
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact Over.OverMorphism.ext h
  cases α
  cases ha
  rfl

variable [IsAlgClosed K] {P : Prerequisites.{u}} {g d : ℕ}
  {a : Datum P (Spec (CommRingCat.of K)) g d n}

/-- Preserving the ordered full level fixes every actual torsion-point morphism. -/
theorem PolarizedIso.fixes_torsionRationalPoints (α : PolarizedIso a a)
    (x : Level a.abelian.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n) :
    (torsionRationalPoints a.abelian n x).1 ≫ hom α.abelianIso.hom =
      (torsionRationalPoints a.abelian n x).1 := by
  have h := DFunLike.congr_fun (α.fibreLevelIso_eq_refl K (𝟙 _)) x
  exact congrArg
    (fun y : Level a.abelian.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n =>
      (Additive.toMul y).val.left) h

/-- A bounded torsion configuration detects an automorphism with a supplied equivariant lift. -/
theorem PolarizedIso.hom_eq_id_of_torsionConfiguration (α : PolarizedIso a a)
    (hn : 0 < n) (i : a.abelian.X.left ⟶ ProjectiveSpace K m) [Mono i]
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom) {q : ℕ}
    (h : ∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) i f) ≤ q)
    (hsize : (m + 1) * q < n ^ (2 * g))
    (e : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K))
    (he : hom α.abelianIso.hom ≫ i = i ≫ linearAction K m e) :
    hom α.abelianIso.hom = 𝟙 a.abelian.X.left := by
  let := a.level.finite_fibreLevel (𝟙 _) hn
  let : Fintype (Level a.abelian.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n) :=
    Fintype.ofFinite _
  have hsize' : (m + 1) * q <
      Fintype.card (Level a.abelian.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n) := by
    rwa [← Nat.card_eq_fintype_card, a.level.card_fibreLevel (𝟙 _)]
  exact eq_id_of_fixes_embedded_rationalPointConfiguration m a.abelian.X.hom i hi
    (torsionRationalPoints a.abelian n)
    (torsionProjectivePointConfiguration_hyperplaneBound i hi h) hsize' e
    (hom α.abelianIso.hom) he α.fixes_torsionRationalPoints

/-- The same hypotheses determine the actual polarized automorphism, including its level data. -/
theorem PolarizedIso.eq_refl_of_torsionConfiguration (α : PolarizedIso a a)
    (hn : 0 < n) (i : a.abelian.X.left ⟶ ProjectiveSpace K m) [Mono i]
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom) {q : ℕ}
    (h : ∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
      Nat.card (TorsionHyperplaneSections (n := n) i f) ≤ q)
    (hsize : (m + 1) * q < n ^ (2 * g))
    (e : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K))
    (he : hom α.abelianIso.hom ≫ i = i ≫ linearAction K m e) :
    α = PolarizedIso.refl a :=
  α.eq_refl_of_hom_eq_id (α.hom_eq_id_of_torsionConfiguration hn i hi h hsize e he)

/-- Apply the exact published cubic count, retaining its geometric and numerical premises. -/
theorem PolarizedIso.eq_refl_of_cubicTorsionHyperplaneBound
    (hcount : CubicTorsionHyperplaneBoundStatement.{u}) (α : PolarizedIso a a)
    (hg : 0 < g) (hd : 0 < d) (hn : 0 < n) (hnK : (n : K) ≠ 0)
    (i : a.abelian.X.left ⟶ ProjectiveSpace K m) (hclosed : IsClosedImmersion i)
    (hi : i ≫ projectiveSpaceToSpec K m = a.abelian.X.hom)
    (hbundle : Nonempty ((Scheme.Modules.pullback i).obj (twistOne K m) ≅ a.cubicBundle.obj))
    (hndeg : ∀ f : projectiveSpaceGrading K m 1, (f : ProjectiveCoordinateRing K m) ≠ 0 →
      ∃ x : a.abelian.X.left, (f : ProjectiveCoordinateRing K m) ∉
        (i x).asHomogeneousIdeal)
    (hsize : (m + 1) * (6 ^ g * d * Nat.factorial g * n ^ (2 * g - 2)) < n ^ (2 * g))
    (e : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K))
    (he : hom α.abelianIso.hom ≫ i = i ≫ linearAction K m e) :
    α = PolarizedIso.refl a := by
  let : IsClosedImmersion i := hclosed
  apply α.eq_refl_of_torsionConfiguration hn i hi _ hsize e he
  exact hcount P K g d n hg hd hn hnK a m i hclosed hi hbundle hndeg

end Langlands.AbelianScheme.PolarizedFiniteLevel
