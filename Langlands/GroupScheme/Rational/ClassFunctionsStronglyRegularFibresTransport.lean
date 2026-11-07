import Langlands.GroupScheme.Rational.AlgebraicClosureCover
import Langlands.GroupScheme.Rational.ClassFunctionsStronglyRegularFibresStatement
import Langlands.GroupScheme.Rational.ClassFunctionsBaseChangeStatement
import Langlands.GroupScheme.Rational.RegularConjugateCentralizerTorus
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Field transport for strongly regular fibres of the canonical quotient -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

section QuotientTransport

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

/-- Equality under the canonical quotient pulls back along an arbitrary field extension,
using the actual quotient comparison supplied by field base change. -/
theorem rho_eq_baseChange (hbc : FieldBaseChangeStatement.{u})
    {T : Over (Spec (CommRingCat.of F))}
    (y w : T ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X)
    (h : baseChangePointsEquiv _ G T y ≫ rho G =
      baseChangePointsEquiv _ G T w ≫ rho G) :
    y ≫ rho ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G) =
      w ≫ rho ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G) := by
  obtain ⟨e, phi, alpha, -, -, -, halpha⟩ := hbc K F G
  rw [← halpha, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ((Over.mapPullbackAdj _).homEquiv T (quotient G)).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_right_symm]
  change baseChangePointsEquiv _ G T y ≫ rho G =
    baseChangePointsEquiv _ G T w ≫ rho G
  exact h

/-- The base-point form of canonical quotient compatibility. -/
theorem rho_eq_baseChangeBasePoints (hbc : FieldBaseChangeStatement.{u})
    (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
    (h : y ≫ rho G = w ≫ rho G) :
    (baseChangeBasePointsEquiv _ G).symm y ≫
        rho ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G) =
      (baseChangeBasePointsEquiv _ G).symm w ≫
        rho ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G) := by
  apply rho_eq_baseChange G hbc
  apply Over.OverMorphism.ext
  have hy := baseChangeBasePointsEquiv_left _ G ((baseChangeBasePointsEquiv _ G).symm y)
  have hw := baseChangeBasePointsEquiv_left _ G ((baseChangeBasePointsEquiv _ G).symm w)
  rw [MulEquiv.apply_symm_apply] at hy hw
  simpa only [Over.comp_left, baseChangePointsEquiv_left, ← hy, ← hw] using
    congrArg (fun f => f.left) h

end QuotientTransport

section CentralizerTransport

variable {B B' : Scheme.{u}} (b : B' ⟶ B) (H : GroupScheme B)

/-- The exact all-test containment of a point centralizer pulls back with its supplied
closed torus. No restriction on the test scheme is introduced. -/
theorem centralizer_le_baseChange
    (w : 𝟙_ (Over B) ⟶ H.X) (S : GroupScheme B) (j : S ⟶ H)
    (hS : IsCommMonObj S.X) (hj : IsClosedSubgroup j)
    (hC : ∀ {Z : Over B} (c : Z ⟶ H.X),
      c * (toUnit Z ≫ w) = (toUnit Z ≫ w) * c →
        ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c)
    {Z : Over B'} (c : Z ⟶ ((baseChange b).obj H).X)
    (hc : c * (toUnit Z ≫ (baseChangeBasePointsEquiv b H).symm
          (toUnit (Over.mk b) ≫ w)) =
        (toUnit Z ≫ (baseChangeBasePointsEquiv b H).symm
          (toUnit (Over.mk b) ≫ w)) * c) :
    ∃ s : Z ⟶ ((baseChange b).obj S).X,
      s ≫ ((baseChange b).map j).hom.hom = c := by
  have : IsCommMonObj S.X := hS
  have : Mono j.hom.hom.left := hj.mono
  have hrep : (H.pointCentralizer w).IsRepresentedBy j := by
    refine ⟨Over.mono_of_mono_left _, range_eq_pointCentralizer H w fun T a ha => ?_⟩
    exact SubgroupFunctor.mem_range.mpr (hC a ((mem_pointCentralizer H w a).mp ha))
  have hrep' := hrep.baseChange b
  rw [pointCentralizer_baseChange] at hrep'
  apply SubgroupFunctor.mem_range.mp
  rw [hrep'.2]
  exact (mem_pointCentralizer _ _ _).mpr hc

end CentralizerTransport

namespace StronglyRegularFibresTransport

variable (K F : Type u) [Field K] [Field F] [Algebra K F]

/-- The shared algebraic-closure cover over the original field. -/
abbrev algebraicClosureCover :=
  QuasiSplitRegularConjugate.algebraicClosureCoverPoint K F

/-- The comparison of the composite structure map with the algebraic closure's
canonical structure map. -/
def algebraicClosureTestComparison :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure F)))) ⟶
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))) :=
  Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫
        (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K F))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure F)))
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq K F (AlgebraicClosure F)])

variable (G : GroupScheme (Spec (CommRingCat.of K)))

/-- Extend an actual point over `F` to a base point of the sequential base change. -/
def algebraicClosureExtendedPoint
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X) :
    𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure F)))) ⟶
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G)).X :=
  (baseChangeBasePointsEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G)).symm
        (toUnit _ ≫ (baseChangeBasePointsEquiv _ G).symm y)

/-- Project a point of the sequential base change to an actual point of the original
group over the compatible algebraic-closure cover. -/
def algebraicClosurePoint
    (g : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure F)))) ⟶
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G)).X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure F)))) ⟶ G.X :=
  algebraicClosureTestComparison K F ≫
    baseChangePointsEquiv _ G _
      (baseChangeBasePointsEquiv _
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G) g)

/-- The projection of the twice-extended point is its pullback along the canonical
algebraic-closure cover. -/
theorem algebraicClosurePoint_baseChange
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X) :
    algebraicClosurePoint K F G (algebraicClosureExtendedPoint K F G y) =
      algebraicClosureCover K F ≫ y := by
  unfold algebraicClosurePoint algebraicClosureExtendedPoint
  rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_toUnit_comp_symm, ← Category.assoc]
  congr 1

/-- Conjugacy in the sequential base change projects to the exact conjugacy equation
in the original group's points. -/
theorem algebraicClosurePoint_conj
    (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
    (g : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure F)))) ⟶
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))))).obj
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G)).X)
    (h : g * algebraicClosureExtendedPoint K F G y * g⁻¹ =
      algebraicClosureExtendedPoint K F G w) :
    algebraicClosurePoint K F G g * (algebraicClosureCover K F ≫ y) *
        (algebraicClosurePoint K F G g)⁻¹ =
      algebraicClosureCover K F ≫ w := by
  have hp := congrArg (algebraicClosurePoint K F G) h
  unfold algebraicClosurePoint at hp
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
    MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv] at hp
  change algebraicClosurePoint K F G g *
      algebraicClosurePoint K F G (algebraicClosureExtendedPoint K F G y) *
        (algebraicClosurePoint K F G g)⁻¹ =
    algebraicClosurePoint K F G (algebraicClosureExtendedPoint K F G w) at hp
  simpa only [algebraicClosurePoint_baseChange] using hp

end StronglyRegularFibresTransport

open StronglyRegularFibresTransport in
/-- Routine conditional field reduction with the algebraically closed geometric
core retained as an explicit hypothesis. -/
theorem stronglyRegularFibres_of_algClosed
    (hbc : FieldBaseChangeStatement.{u})
    (hcore : ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsSemisimple H),
      letI : IsAffineHom H.X.hom := hH.isConnectedReductive.isAffineHom
      ∀ (y w : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
        (S : GroupScheme (Spec (CommRingCat.of k))) (j : S ⟶ H),
        IsTorus S → IsClosedSubgroup j →
        (∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ H.X),
          c * (toUnit Z ≫ w) = (toUnit Z ≫ w) * c →
            ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
        y ≫ rho H = w ≫ rho H →
        ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X,
          g * y * g⁻¹ = w) :
    StronglyRegularFibresStatement.{u} := by
  intro K _ G hsc hqs
  let : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
  intro F _ _ y w S j hS hj hC hrho
  let b := Spec.map (CommRingCat.ofHom (algebraMap K F))
  let GF := (baseChange b).obj G
  have hGF : IsSemisimple GF := isSemisimpleFieldExtension K F G hsc.isSemisimple
  let : IsAffineHom GF.X.hom := hGF.isConnectedReductive.isAffineHom
  let E := AlgebraicClosure F
  let c := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let HE := (baseChange c).obj GF
  have hHE : IsSemisimple HE := isSemisimpleFieldExtension F E GF hGF
  let : IsAffineHom HE.X.hom := hHE.isConnectedReductive.isAffineHom
  let yF := (baseChangeBasePointsEquiv b G).symm y
  let wF := (baseChangeBasePointsEquiv b G).symm w
  have hrhoF : yF ≫ rho GF = wF ≫ rho GF :=
    rho_eq_baseChangeBasePoints G hbc y w hrho
  have hrhoE :
      algebraicClosureExtendedPoint K F G y ≫ rho HE =
        algebraicClosureExtendedPoint K F G w ≫ rho HE := by
    apply rho_eq_baseChangeBasePoints GF hbc
    simpa only [Category.assoc] using
      congrArg (fun f => toUnit (Over.mk c) ≫ f) hrhoF
  have hS' : IsTorus ((baseChange c).obj S) := hS.baseChange
  obtain ⟨g, hg⟩ := hcore E HE hHE
    (algebraicClosureExtendedPoint K F G y)
    (algebraicClosureExtendedPoint K F G w)
    ((baseChange c).obj S) ((baseChange c).map j) hS' (hj.baseChange c)
    (fun a ha => centralizer_le_baseChange c GF wF S j hS.isCommMonObj hj hC a ha)
    hrhoE
  exact ⟨E, inferInstance, inferInstance, algebraicClosureCover K F,
    algebraicClosurePoint K F G g, algebraicClosurePoint_conj K F G y w g hg⟩

end Langlands.GroupScheme.ClassFunctions
