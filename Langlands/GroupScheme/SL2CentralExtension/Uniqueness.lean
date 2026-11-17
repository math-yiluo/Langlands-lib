import Langlands.GroupScheme.Reductive.RelativeSemisimpleFppfPerfectProof
import Langlands.GroupScheme.SpecialLinearSimplyConnected
import Langlands.GroupScheme.SpecialLinearCentralExtensionSplitStatement

/-! # Uniqueness of sections of central extensions of `SL₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

/-- The actual base change of the integral binary special linear model. -/
abbrev binarySpecialLinear (S : Scheme.{u}) : GroupScheme S :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).obj
    (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ)))

/-- The integral special linear model is reductive after arbitrary base change. -/
theorem isReductive_binarySpecialLinear (S : Scheme.{u}) :
    IsReductive (binarySpecialLinear S) :=
  (SpecialLinear.isReductive (Fin 2) 0 (CommRingCat.of (ULift.{u} ℤ))).baseChange _

/-- Every geometric fibre of the actual binary special linear model is semisimple. -/
theorem isSemisimple_binarySpecialLinear_geometricFiber (S : Scheme.{u}) (s : S) :
    IsSemisimple (geometricFiber (binarySpecialLinear S) s) := by
  let G := SpecialLinear.groupScheme (Fin 2) (CommRingCat.of (ULift.{u} ℤ))
  let K := AlgebraicClosure (S.residueField s)
  let e : geometricFiber (binarySpecialLinear S) s ≅
      SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K) :=
    (baseChangeCompIso (Gm.toSpecZ S) (geometricPoint S s) G).symm ≪≫
      SpecialLinear.baseChangeModelIso (Fin 2) (geometricPoint S s ≫ Gm.toSpecZ S)
  exact IsSemisimple.of_iso e (SpecialLinear.isSimplyConnected (Fin 2) K).isSemisimple

/-- Every binary special linear point is fppf-locally an abstract commutator. -/
theorem binarySpecialLinear_locallyCommutator (S : Scheme.{u}) (T : Over S)
    (x : T ⟶ (binarySpecialLinear S).X) : RelativeDerived.LocallyCommutator x :=
  relativeSemisimpleFppfPerfect S _ (isReductive_binarySpecialLinear S)
    (isSemisimple_binarySpecialLinear_geometricFiber S) T x

/-- Two homomorphisms whose pointwise difference is central have a homomorphic
difference with values in the center. -/
def centralDifference {A B : Type*} [Group A] [Group B] (F G : A →* B)
    (h : ∀ a, F a * (G a)⁻¹ ∈ Subgroup.center B) : A →* Subgroup.center B where
  toFun a := ⟨F a * (G a)⁻¹, h a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change F (a * b) * (G (a * b))⁻¹ =
      (F a * (G a)⁻¹) * (F b * (G b)⁻¹)
    simp only [map_mul, mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp (h b) (G a)⁻¹
    calc
      F a * F b * ((G b)⁻¹ * (G a)⁻¹) =
          F a * ((F b * (G b)⁻¹) * (G a)⁻¹) := by group
      _ = F a * ((G a)⁻¹ * (F b * (G b)⁻¹)) := by rw [hc]
      _ = (F a * (G a)⁻¹) * (F b * (G b)⁻¹) := by group

/-- Homomorphisms differing centrally agree on the abstract commutator subgroup. -/
theorem eq_on_commutator_of_centralDifference {A B : Type*} [Group A] [Group B]
    (F G : A →* B) (h : ∀ a, F a * (G a)⁻¹ ∈ Subgroup.center B)
    (a : A) (ha : a ∈ _root_.commutator A) : F a = G a := by
  let d := centralDifference F G h
  have hd : _root_.commutator A ≤ d.ker := by
    change _root_.commutator A ≤ Subgroup.comap d ⊥
    rw [← Subgroup.map_le_iff_le_comap, map_commutator_eq]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (by rw [← _root_.commutator_def, commutator_eq_bot])
  have he : d a = 1 := hd ha
  have hv := congrArg Subtype.val he
  exact mul_inv_eq_one.mp hv

/-- A group scheme all of whose points are fppf-locally commutators has at most
one section of any homomorphism with central kernel. -/
theorem section_unique_of_locallyCommutator {S : Scheme.{u}} {D E Z : GroupScheme S}
    (z : Z ⟶ E) (q : E ⟶ D) (hz : IsCentral z)
    (hker : ∀ (T : Over S) (x : T ⟶ E.X),
      x ≫ q.hom.hom = 1 → x ∈ (SubgroupFunctor.range z).carrier T)
    (hD : ∀ (T : Over S) (x : T ⟶ D.X), RelativeDerived.LocallyCommutator x)
    (s₁ s₂ : D ⟶ E) (h₁ : s₁ ≫ q = 𝟙 D) (h₂ : s₂ ≫ q = 𝟙 D) : s₁ = s₂ := by
  have h₁p : s₁.hom.hom ≫ q.hom.hom = 𝟙 D.X :=
    congrArg (fun a : D ⟶ D => a.hom.hom) h₁
  have h₂p : s₂.hom.hom ≫ q.hom.hom = 𝟙 D.X :=
    congrArg (fun a : D ⟶ D => a.hom.hom) h₂
  apply hom_ext_points
  intro T x
  obtain ⟨𝒰, h𝒰⟩ := hD T x
  apply RelativeDerived.fppfCover_hom_ext 𝒰
  intro i
  let U : Over S := Over.mk (𝒰.f i ≫ T.hom)
  let F : (U ⟶ D.X) →* (U ⟶ E.X) := ((yonedaGrp.map s₁).app (op U)).hom
  let G : (U ⟶ D.X) →* (U ⟶ E.X) := ((yonedaGrp.map s₂).app (op U)).hom
  have hc (a : U ⟶ D.X) : F a * (G a)⁻¹ ∈ Subgroup.center (U ⟶ E.X) := by
    have hq : (F a * (G a)⁻¹) ≫ q.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp]
      change ((a ≫ s₁.hom.hom) ≫ q.hom.hom) *
        (((a ≫ s₂.hom.hom) ≫ q.hom.hom)⁻¹) = 1
      rw [Category.assoc, Category.assoc, h₁p, h₂p, Category.comp_id, mul_inv_cancel]
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp (hker U _ hq)
    rw [← hb]
    exact Subgroup.mem_center_iff.mpr
      (fun c => (commute_of_mem_center (hz U b) c).eq.symm)
  have he := eq_on_commutator_of_centralDifference F G hc
    ((Over.homMk (𝒰.f i) rfl : U ⟶ T) ≫ x) (h𝒰 i)
  change ((Over.homMk (𝒰.f i) rfl : U ⟶ T) ≫ x) ≫ s₁.hom.hom =
    ((Over.homMk (𝒰.f i) rfl : U ⟶ T) ≫ x) ≫ s₂.hom.hom at he
  simpa only [Category.assoc] using he

/-- Uniqueness of the section in the actual binary special linear central
extension theorem, over every scheme. -/
theorem binarySpecialLinear_section_unique {S : Scheme.{u}} {Z : CommGroupScheme S}
    {E : GroupScheme S} (z : Z.toGrp ⟶ E) (q : E ⟶ binarySpecialLinear S)
    (hz : IsCentral z)
    (hker : ∀ (T : Over S) (x : T ⟶ E.X),
      x ≫ q.hom.hom = 1 ↔ x ∈ (SubgroupFunctor.range z).carrier T)
    (s₁ s₂ : binarySpecialLinear S ⟶ E)
    (h₁ : s₁ ≫ q = 𝟙 (binarySpecialLinear S))
    (h₂ : s₂ ≫ q = 𝟙 (binarySpecialLinear S)) : s₁ = s₂ :=
  section_unique_of_locallyCommutator z q hz (fun T x => (hker T x).mp)
    (binarySpecialLinear_locallyCommutator S) s₁ s₂ h₁ h₂

end Langlands.GroupScheme.SL2CentralExtension
