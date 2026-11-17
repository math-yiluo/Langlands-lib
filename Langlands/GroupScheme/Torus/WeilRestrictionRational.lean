import Langlands.GroupScheme.Torus.TorusUnirationalityStatement
import Langlands.GroupScheme.FiniteAlgebraUnits

/-! # Rationality of the Weil restriction of `𝔾_m` along a finite algebra over a field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.WeilGmRational

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Module.Finite k B]
  {n : ℕ} (b : Module.Basis (Fin n) k B)

/-- The coefficient-side unit model `(Γ(T) ⊗ B)ˣ`, moved to the Weil-side order
`(B ⊗ Γ(T))ˣ`. -/
def unitsComm (T : Type u) [CommRing T] [Algebra k T] : (T ⊗[k] B)ˣ ≃* (B ⊗[k] T)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.comm k T B).toMulEquiv

omit [Module.Finite k B] in
theorem unitsComm_naturality {T T' : Type u} [CommRing T] [Algebra k T] [CommRing T']
    [Algebra k T'] (g : T →ₐ[k] T') (x : (T ⊗[k] B)ˣ) :
    unitsComm T' (Units.map (Algebra.TensorProduct.map g (AlgHom.id k B)).toMonoidHom x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B g : B ⊗[k] T →* B ⊗[k] T')
        (unitsComm T x) := by
  apply Units.ext
  change Algebra.TensorProduct.comm k T' B (Algebra.TensorProduct.map g (AlgHom.id k B) x) =
    Algebra.TensorProduct.lTensor (S := B) B g (Algebra.TensorProduct.comm k T B x)
  induction (x : T ⊗[k] B) using TensorProduct.inductionOn with
  | tmul t c => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- The Weil restriction is isomorphic to the determinant-open unit group of the basis. -/
def unitsIso :
    WeilGm.groupScheme (CommRingCat.of k) B ≅ FiniteAlgebraUnits.groupScheme b :=
  isoOfPointModels
    (fun T : Over (Spec (CommRingCat.of k)) =>
      (B ⊗[CommRingCat.of k] ((algΓ (CommRingCat.of k)).obj T).unop)ˣ)
    (fun a => Units.map (Algebra.TensorProduct.lTensor (S := B) B
      ((algΓ (CommRingCat.of k)).map a).unop.hom : B ⊗[CommRingCat.of k] _ →* B ⊗[CommRingCat.of k] _))
    (WeilGm.pointsEquiv (CommRingCat.of k) B)
    (fun T => (FiniteAlgebraUnits.pointsEquiv b T).trans (unitsComm _))
    (WeilGm.pointsEquiv_naturality (CommRingCat.of k) B)
    (fun a y => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, FiniteAlgebraUnits.pointsEquiv_naturality]
      exact unitsComm_naturality _ _)

/-- The underlying scheme isomorphism. -/
def leftIso :
    (WeilGm.groupScheme (CommRingCat.of k) B).X.left ≅
      Spec (CommRingCat.of (FiniteAlgebraUnits.candidateRing b)) :=
  (Over.forget _).mapIso ((Grp.forget _).mapIso (unitsIso b))

theorem leftIso_hom_over :
    (leftIso b).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (FiniteAlgebraUnits.candidateRing b))) =
      (WeilGm.groupScheme (CommRingCat.of k) B).X.hom :=
  Over.w ((Grp.forget _).map (unitsIso b).hom)

variable (k n) in
/-- Renaming the coordinates into the universe of the base. -/
def renameRingHom : MvPolynomial (ULift.{u} (Fin n)) k →+* MvPolynomial (Fin n) k :=
  (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv.toRingHom

/-- The chart of the determinant-open candidate in affine space. -/
def chart :
    Spec (CommRingCat.of (FiniteAlgebraUnits.candidateRing b)) ⟶
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiniteAlgebraUnits.coordinateRing k n)
      (Localization.Away (FiniteAlgebraUnits.determinant b)))) ≫
    Spec.map (CommRingCat.ofHom (renameRingHom k n)) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv

instance : IsIso (Spec.map (CommRingCat.ofHom (renameRingHom k n))) := by
  have : IsIso (CommRingCat.ofHom (renameRingHom k n)) :=
    inferInstanceAs (IsIso (MvPolynomial.renameEquiv k
      (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

instance : IsOpenImmersion (chart b) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap
      (FiniteAlgebraUnits.coordinateRing k n)
      (Localization.Away (FiniteAlgebraUnits.determinant b))))) := inferInstance
  unfold chart
  infer_instance

omit [Module.Finite k B] in
theorem chart_over :
    chart b ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (FiniteAlgebraUnits.candidateRing b))) := by
  rw [chart, Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext x
  simp only [renameRingHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply]
  refine Eq.trans ?_ (IsScalarTower.algebraMap_apply k (FiniteAlgebraUnits.coordinateRing k n)
    (FiniteAlgebraUnits.candidateRing b) x).symm
  congr 1
  simp [MvPolynomial.algebraMap_eq]

omit [Module.Finite k B] in
/-- The determinant-open candidate has a point. -/
theorem candidateRing_nontrivial : Nontrivial (FiniteAlgebraUnits.candidateRing b) :=
  (FiniteAlgebraUnits.unitCoefficientMap b (B := k) 1).toRingHom.domain_nontrivial

/-- The full chart of the Weil restriction. -/
def weilChart :
    (WeilGm.groupScheme (CommRingCat.of k) B).X.left ⟶
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) :=
  (leftIso b).hom ≫ chart b

instance : IsOpenImmersion (weilChart b) := by
  unfold weilChart
  infer_instance

instance : IsDominant (weilChart b) := by
  constructor
  apply (weilChart b).isOpenEmbedding.isOpen_range.dense
  have := candidateRing_nontrivial b
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (FiniteAlgebraUnits.candidateRing b)) := inferInstance
  exact ⟨_, ⟨(leftIso b).inv.base p, rfl⟩⟩

theorem weilChart_over :
    weilChart b ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      (WeilGm.groupScheme (CommRingCat.of k) B).X.hom := by
  rw [weilChart, Category.assoc, chart_over, leftIso_hom_over]

variable (k B) in
/-- The Weil restriction of `𝔾_m` along a finite algebra has a point. -/
theorem nonempty_left : Nonempty (WeilGm.groupScheme (CommRingCat.of k) B).X.left := by
  let b := Module.finBasis k B
  have := candidateRing_nontrivial b
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (FiniteAlgebraUnits.candidateRing b)) := inferInstance
  exact ⟨(leftIso b).inv.base p⟩

variable (k B) in
/-- **Rationality of `R_{B/k} 𝔾_m`.** For every finite algebra `B` over a field `k`, the Weil
restriction of the multiplicative group is birational over `k` to a finite-dimensional affine
space. -/
theorem hasFiniteAffineBirationalModel :
    HasFiniteAffineBirationalModel k (WeilGm.groupScheme (CommRingCat.of k) B).X := by
  let b := Module.finBasis k B
  exact ⟨ULift.{u} (Fin (Module.finrank k B)), inferInstance,
    (weilChart b).birationalOver _ _ (weilChart_over b)⟩

end Langlands.GroupScheme.WeilGmRational
