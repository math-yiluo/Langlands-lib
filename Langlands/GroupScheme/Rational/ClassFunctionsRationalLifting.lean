import Langlands.GroupScheme.Rational.ClassFunctionsRationalLiftingStatement
import Langlands.GroupScheme.Rational.EvenChainCrossSection
import Langlands.GroupScheme.Rational.EvenChainGaloisData
import Langlands.GroupScheme.Rational.ClassFunctionsBaseChange
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # Proof: rational lifting of values of the canonical class quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.ClassFunctions

namespace RationalLifting

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- The base change to `L` of a rational point of an object over `Spec k`. -/
def pullbackPoint (X : Over (Spec (CommRingCat.of k)))
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ (Over.pullback (algebraBaseMap k L)).obj X :=
  Over.homMk (pullback.lift (algebraBaseMap k L ≫ y.left) (𝟙 _) (by
    have hy : y.left ≫ X.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, hy]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)) (by
    change pullback.lift _ _ _ ≫ pullback.snd X.hom (algebraBaseMap k L) = 𝟙 _
    exact pullback.lift_snd _ _ _)

/-- A rational point of the base change is determined by its projection to the original
object. -/
theorem point_ext {X : Over (Spec (CommRingCat.of k))}
    {h h' : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ (Over.pullback (algebraBaseMap k L)).obj X}
    (hfst : h.left ≫ pullback.fst X.hom (algebraBaseMap k L) =
      h'.left ≫ pullback.fst X.hom (algebraBaseMap k L)) : h = h' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext hfst
  have h1 : h.left ≫ pullback.snd X.hom (algebraBaseMap k L) = 𝟙 _ := Over.w h
  have h2 : h'.left ≫ pullback.snd X.hom (algebraBaseMap k L) = 𝟙 _ := Over.w h'
  rw [h1, h2]

theorem pullbackPoint_fst (X : Over (Spec (CommRingCat.of k)))
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    (pullbackPoint (L := L) X y).left ≫ pullback.fst X.hom (algebraBaseMap k L) =
      algebraBaseMap k L ≫ y.left :=
  pullback.lift_fst _ _ _

theorem map_left_fst {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    ((Over.pullback (algebraBaseMap k L)).map f).left ≫
        pullback.fst Y.hom (algebraBaseMap k L) =
      pullback.fst X.hom (algebraBaseMap k L) ≫ f.left := by
  simp

end RationalLifting

end Langlands.GroupScheme.ClassFunctions

namespace Langlands.GroupScheme.ClassFunctions.RationalLifting

section Quotient

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "GLb" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

local instance rationalLiftingBaseChangeIsAffineHom : IsAffineHom (GLb).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- The rational point of the quotient of the base change corresponding to a rational point
of the original quotient. -/
def quotientPoint (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ quotient G) :
    Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ quotient (GLb) :=
  pullbackPoint (quotient G) v ≫ (BaseChange.quotientComparison k L G).hom

/-- A rational point of the base change maps to the base-changed quotient point exactly when
the corresponding `L`-point of the original group maps to the restriction of that point. -/
theorem rho_eq_quotientPoint_iff (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ quotient G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ (GLb).X) :
    g ≫ rho (GLb) = quotientPoint k L G v ↔
      baseChangeBasePointsEquiv (algebraBaseMap k L) G g ≫ rho G = toUnit _ ≫ v := by
  rw [← BaseChange.quotientComparison_rho k L G, quotientPoint, ← Category.assoc,
    cancel_mono]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    have h' := congrArg
      (fun z : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
          (Over.pullback (algebraBaseMap k L)).obj (quotient G) =>
        z.left ≫ pullback.fst (quotient G).hom (algebraBaseMap k L)) h
    simp only [Over.comp_left, Category.assoc, map_left_fst, pullbackPoint_fst] at h'
    simp only [Over.comp_left, baseChangeBasePointsEquiv_left, Category.assoc]
    rw [h']
    rfl
  · intro h
    apply point_ext
    have h' := congrArg (fun z => z.left) h
    simp only [Over.comp_left, baseChangeBasePointsEquiv_left, Category.assoc] at h'
    simp only [Over.comp_left, Category.assoc, map_left_fst, pullbackPoint_fst]
    rw [h']
    rfl

/-- Galois conjugation of rational points of the base change preserves the condition of
mapping to a base-changed quotient point. -/
theorem rationalConjugate_rho_eq [FiniteDimensional k L] [IsGalois k L]
    (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ quotient G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ (GLb).X)
    (hg : g ≫ rho (GLb) = quotientPoint k L G v) (σ : L ≃ₐ[k] L) :
    GaloisPointComparison.rationalConjugate k L G σ g ≫ rho (GLb) = quotientPoint k L G v := by
  rw [rho_eq_quotientPoint_iff] at hg ⊢
  have h := GaloisPointComparison.baseChangeCoeffEquiv_rationalConjugate k L G σ g
  change baseChangeBasePointsEquiv (algebraBaseMap k L) G
      (GaloisPointComparison.rationalConjugate k L G σ g) = _ at h
  rw [h]
  change ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      baseChangeBasePointsEquiv (algebraBaseMap k L) G g) ≫ rho G = _
  rw [Category.assoc, hg, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

/-- A rational point of the original group whose base change maps to the base-changed
quotient point maps to the original quotient point. -/
theorem rho_eq_of_baseChangeBasePoint (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ quotient G)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hx : baseChangeBasePoint (algebraBaseMap k L) G x ≫ rho (GLb) = quotientPoint k L G v) :
    x ≫ rho G = v := by
  rw [rho_eq_quotientPoint_iff] at hx
  have hb : baseChangeBasePointsEquiv (algebraBaseMap k L) G
      (baseChangeBasePoint (algebraBaseMap k L) G x) =
        G.constantPoint x (Over.mk (algebraBaseMap k L)) :=
    (baseChangeBasePointsEquiv (algebraBaseMap k L) G).apply_symm_apply _
  rw [hb] at hx
  have hfpqc := fieldExtension_fpqc k L
  have : Surjective (algebraBaseMap k L) := hfpqc.1
  have : Flat (algebraBaseMap k L) := hfpqc.2.1
  have : Epi (algebraBaseMap k L) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply (cancel_epi (algebraBaseMap k L)).mp
  have h := congrArg (fun z => z.left) hx
  simpa [GroupScheme.constantPoint] using h

end Quotient

end Langlands.GroupScheme.ClassFunctions.RationalLifting

namespace Langlands.GroupScheme.ClassFunctions

open RationalLifting

/-- Rational lifting from the split even-path cross-section and Galois-stable even-path
data. Both statements are explicit inputs here. -/
theorem stronglyRegularRationalLifting_of_evenChain
    (hCS : SplitEvenChainCrossSectionStatement.{u})
    (hGal : EvenChainGaloisDataStatement.{u}) :
    StronglyRegularRationalLiftingStatement.{u} := by
  intro K _ G hsc hqs
  have : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
  intro v _F _ _ _w _S _j _hS _hj _hc _hw
  obtain ⟨L, _, _, hfin, hgal, ⟨D⟩⟩ :=
    hqs.exists_pairingCompatiblePinningData parabolicDynamic rootDatumExistence
  have : IsAffineHom
      (Functor.obj (GroupScheme.baseChange (algebraBaseMap K L)) G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap K L))
    infer_instance
  obtain ⟨J, _, C, r, q, o, e, hmo, hstab⟩ := hGal K L G D
  have hscL : IsSimplyConnected (Functor.obj (GroupScheme.baseChange (algebraBaseMap K L)) G) :=
    isSimplyConnectedFieldExtension K L G hsc
  obtain ⟨g, ⟨hgS, hgρ⟩, huniq⟩ :=
    hCS L _ D.pinning hscL D.rootMaps J C r q o e hmo (quotientPoint K L G v)
  have hfix : ∀ σ : L ≃ₐ[K] L, GaloisPointComparison.rationalConjugate K L G σ g = g := by
    intro σ
    exact huniq _ ⟨hstab σ g hgS, rationalConjugate_rho_eq K L G v g hgρ σ⟩
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  refine ⟨rationalPointOfGaloisFixed K L G g hfix, ?_⟩
  apply rho_eq_of_baseChangeBasePoint K L G v
  have hx := baseChangeBasePoint_rationalPointOfGaloisFixed K L G g hfix
  change baseChangeBasePoint (algebraBaseMap K L) G _ = g at hx
  rw [hx]
  exact hgρ

/-- **Rational lifting of values of the canonical class quotient** (Steinberg 1965, 1.7 = 9.8,
over an arbitrary field). It combines the published split even-path cross-section
`splitEvenChainCrossSection` with the published Galois-stable even-path data
`evenChainGaloisData`. -/
theorem stronglyRegularRationalLifting : StronglyRegularRationalLiftingStatement.{u} :=
  stronglyRegularRationalLifting_of_evenChain splitEvenChainCrossSection evenChainGaloisData

end Langlands.GroupScheme.ClassFunctions
