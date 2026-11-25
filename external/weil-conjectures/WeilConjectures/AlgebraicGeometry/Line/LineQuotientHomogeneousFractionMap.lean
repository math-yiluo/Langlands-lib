/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Graded.GradedImmersionAmpleCriterion
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import all WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent
import all WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Mathlib.Algebra.DirectSum.Algebra
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineHomogeneousFractionAtlas

/-!
# A line quotient and its homogeneous fraction morphism

## References

* Stacks Project, Constructions, Tags 01NA, 01O9 and 01OA
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor powers of a local frame, with the structural unit in degree zero. -/
noncomputable def quotientFramePower {T : Scheme.{u}} {L : T.Modules} {W : T.Opens}
    (l : Γ(L, W)) : (n : ℕ) → Γ(L.tensorPow n, W)
  | 0 => unitSectionsEquiv W 1
  | n + 1 => tmulSection l (quotientFramePower l n)

/-- The coefficient of a homogeneous image relative to a frame power. On a frame the
scalar multiplication function is bijective, so its inverse is uniquely determined. -/
noncomputable def RelativeGradedLineMap.quotientCoefficient
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L) (U : S.affineOpens) (W : T.affineOpens)
    (hWU : W.1 ≤ h ⁻¹ᵁ U.1) (l : Γ(L, W.1)) (d : ℕ) (a : A.grading U d) : Γ(T, W.1) :=
  Function.invFun (fun b : Γ(T, W.1) ↦ b • quotientFramePower l d)
    ((L.tensorPow d).val.map (homOfLE hWU).op (ψ.component U d a))

/-- The coefficient of the quotient image of a degree-one module section. -/
noncomputable def quotientGeneratorCoefficient {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (m : Γ(E, U.1)) : Γ(T, W.1) :=
  Function.invFun (fun b : Γ(T, W.1) ↦ b • l)
    (q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
      (tensorPullbackSection h E U.1 m)))

/-- The symmetric-algebra generator `ι m` of a section `m`, as an element of the degree-one
grading piece. -/
noncomputable def quotientSymmetricGenerator {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (U : S.affineOpens) (m : Γ(E, U.1)) :
    (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1 :=
  ⟨SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1) m, by
    change SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1) m ∈
      (SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1)).range ^ (1 : ℕ)
    rw [pow_one]
    exact ⟨m, rfl⟩⟩

/-- The degree-one component is exactly the specified quotient, in adjoint section form. -/
def RelativeGradedLineMap.ExtendsLineQuotient {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L) : Prop :=
  ∀ (U : S.affineOpens) (m : Γ(E, U.1)),
    (ρ_ L).hom.app (h ⁻¹ᵁ U.1) (ψ.component U 1 (quotientSymmetricGenerator E U m)) =
      q.app (h ⁻¹ᵁ U.1) (tensorPullbackSection h E U.1 m)

/-- The affine source of a fraction chart, canonically mapped into `T`. -/
noncomputable def quotientFractionSource {T : Scheme.{u}} (W : T.affineOpens)
    (b : Γ(T, W.1)) : Spec (.of (Localization.Away b)) ⟶ T :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W.1) (Localization.Away b))) ≫
    W.2.isoSpec.inv ≫ W.1.ι

/-- The fraction a/e^d for a degree-one denominator and degree-d numerator. -/
def degreeOneQuotientFraction {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) (d : ℕ) (a : A.grading U d) :
    HomogeneousLocalization.Away (A.grading U) e.val :=
  HomogeneousLocalization.Away.mk (A.grading U) e.property d a.val
    (by simpa only [smul_eq_mul, mul_one] using a.property)

/-- The scalar r/1 in the homogeneous localization; this specifies its R-algebra structure. -/
def quotientFractionScalar {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.obj U) (r : Γ(S, U.1)) :
    HomogeneousLocalization.Away (A.grading U) e :=
  HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers e)
    ⟨algebraMap Γ(S, U.1) (A.obj U) r, SetLike.algebraMap_mem_graded (A.grading U) r⟩

/-- A chart homomorphism is specified by all its homogeneous fraction values, its scalar
map, and its spectrum map into the fixed global morphism. The scalar equation says precisely
that the ring homomorphism is an R-algebra homomorphism, without a file-local instance. -/
def RelativeGradedLineMap.IsQuotientFractionChart {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (m : Γ(E, U.1))
    (ρ : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+*
        Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m)) : Prop :=
  (∀ (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
    ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
      (quotientSymmetricGenerator E U m) d a) =
        Localization.mk (ψ.quotientCoefficient U W hWU l d a)
          (⟨quotientGeneratorCoefficient h E L q U W hWU l m ^ d,
            ⟨d, rfl⟩⟩ : Submonoid.powers
              (quotientGeneratorCoefficient h E L q U W hWU l m))) ∧
  (∀ r : Γ(S, U.1),
    ρ (quotientFractionScalar (SymmetricAlgebraSheaf.gradedAlgebraData E) U
      (quotientSymmetricGenerator E U m).val r) =
        algebraMap Γ(T, W.1)
          (Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m))
          (h.appLE U.1 W.1 hWU r)) ∧
  quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l m) ≫ F =
    Spec.map (CommRingCat.ofHom ρ) ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ∧
  ∀ n : Γ(E, U.1),
    IsUnit (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m))
      (P := Localization.Away
        (quotientGeneratorCoefficient h E L q U W hWU l m *
          quotientGeneratorCoefficient h E L q U W hWU l n))
      (quotientGeneratorCoefficient h E L q U W hWU l m)
      (quotientGeneratorCoefficient h E L q U W hWU l n)
      (ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U n))))

/-- All affine line charts, including coefficient normalization, the generator cover,
frame change, source restriction, and affine base restriction. The chart equation with F
expresses agreement on every overlap, including those above distinct base opens, and
identifies the glued map independently of any choices. -/
def RelativeGradedLineMap.HasQuotientFractionCharts {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  F ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h ∧
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    (∀ (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W hWU l d a • quotientFramePower l d =
        (L.tensorPow d).val.map (homOfLE hWU).op (ψ.component U d a)) ∧
    (∀ m : Γ(E, U.1),
      ψ.quotientCoefficient U W hWU l 1 (quotientSymmetricGenerator E U m) =
        quotientGeneratorCoefficient h E L q U W hWU l m) ∧
    (⨆ m : Γ(E, U.1),
      T.basicOpen (quotientGeneratorCoefficient h E L q U W hWU l m)) = W.1 ∧
    (∀ m : Γ(E, U.1), ∃ ρ : HomogeneousLocalization.Away
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val →+*
          Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m),
      ψ.IsQuotientFractionChart h E L q F U W hWU l m ρ) ∧
    (∀ (v : Γ(T, W.1)ˣ) (d : ℕ)
      (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W hWU ((v : Γ(T, W.1)) • l) d a =
        (↑(v⁻¹) : Γ(T, W.1)) ^ d * ψ.quotientCoefficient U W hWU l d a) ∧
    (∀ (W' : T.affineOpens) (j : W' ≤ W)
      (hW'U : W'.1 ≤ h ⁻¹ᵁ U.1) (d : ℕ)
      (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W' hW'U (L.val.map (homOfLE j).op l) d a =
        T.presheaf.map (homOfLE j).op (ψ.quotientCoefficient U W hWU l d a)) ∧
    (∀ (U' : S.affineOpens) (j : U' ≤ U) (hWU' : W.1 ≤ h ⁻¹ᵁ U'.1)
      (d : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U' W hWU' l d
        ⟨(SymmetricAlgebraSheaf.gradedAlgebraData E).res j a,
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).res j).map_mem a.property⟩ =
        ψ.quotientCoefficient U W hWU l d a)

/-- Independence under a change of frame, expressed after any common scalar-preserving
transport of the two localizations. This includes their canonical localization isomorphism. -/
def RelativeGradedLineMap.QuotientFrameIndependent {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    ∀ (v : Γ(T, W.1)ˣ) (m : Γ(E, U.1))
      (ρ : HomogeneousLocalization.Away
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val →+*
          Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m))
      (ρ' : HomogeneousLocalization.Away
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val →+*
          Localization.Away
            (quotientGeneratorCoefficient h E L q U W hWU ((v : Γ(T, W.1)) • l) m)),
      ψ.IsQuotientFractionChart h E L q F U W hWU l m ρ →
      ψ.IsQuotientFractionChart h E L q F U W hWU ((v : Γ(T, W.1)) • l) m ρ' →
      ∀ (C : Type u) [CommRing C]
        (β : Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m) →+* C)
        (β' : Localization.Away
          (quotientGeneratorCoefficient h E L q U W hWU ((v : Γ(T, W.1)) • l) m) →+* C),
        β.comp (algebraMap Γ(T, W.1) _) = β'.comp (algebraMap Γ(T, W.1) _) →
        β.comp ρ = β'.comp ρ'

private noncomputable abbrev LocalComponent {T : Scheme.{u}} (L : T.Modules) (U : T.Opens)
    (n : ℕ) : Type u := Γ(L.tensorPow n, U)

private noncomputable instance localOne {T : Scheme.{u}} (L : T.Modules) (U : T.Opens) :
    GradedMonoid.GOne (LocalComponent L U) where
  one := unitSectionsEquiv U 1

private noncomputable instance localMul {T : Scheme.{u}} (L : T.Modules) (U : T.Opens) :
    GradedMonoid.GMul (LocalComponent L U) where
  mul {i j} a b := (L.tensorPowAddIso i j).inv.app U (tmulSection a b)

private theorem localOneMul {T : Scheme.{u}} (L : T.Modules) (U : T.Opens)
    (a : GradedMonoid (LocalComponent L U)) : 1 * a = a := by
  obtain ⟨i, a⟩ := a
  apply Sigma.ext (Nat.zero_add i)
  change HEq ((L.tensorPowAddIso 0 i).inv.app U
    (tmulSection (unitSectionsEquiv U 1) a)) a
  exact (eqToHom_app_heq (congrArg L.tensorPow (Nat.zero_add i).symm) _).trans
    (heq_of_eq ((leftUnitor_hom_app_tmulSection 1 a).trans (one_smul _ _)))

private theorem localMulOne {T : Scheme.{u}} (L : T.Modules) (U : T.Opens)
    (a : GradedMonoid (LocalComponent L U)) : a * 1 = a := by
  obtain ⟨i, a⟩ := a
  apply Sigma.ext (Nat.add_zero i)
  apply heq_of_eq
  change (L.tensorPowAddIso i 0).inv.app U (tmulSection a (unitSectionsEquiv U 1)) = a
  rw [tensorPowAddIso_zero_inv]
  exact (rightUnitor_hom_app_tmulSection 1 a).trans (one_smul _ _)

private theorem localMulAssoc {T : Scheme.{u}} (L : T.Modules) (U : T.Opens)
    (a b c : GradedMonoid (LocalComponent L U)) : a * b * c = a * (b * c) := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  apply Sigma.ext (Nat.add_assoc i j k)
  have h := congrArg (fun f ↦ f.app U (tmulSection (tmulSection a b) c))
    (tensorPowAddIso_assoc_inv L i j k)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection,
    whiskerLeft_app_tmulSection, associator_hom_app_tmulSection] at h
  exact (heq_of_eq h).trans
    (eqToHom_app_heq (congrArg L.tensorPow (Nat.add_assoc i j k).symm)
      ((L.tensorPowAddIso i (j + k)).inv.app U
        (tmulSection a ((L.tensorPowAddIso j k).inv.app U (tmulSection b c)))))

private theorem localMulComm {T : Scheme.{u}} (L : T.Modules) [L.IsInvertible]
    (U : T.Opens) (a b : GradedMonoid (LocalComponent L U)) : a * b = b * a := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  apply Sigma.ext (Nat.add_comm i j)
  have h : (L.tensorPowAddIso i j).inv.app U (tmulSection a b) =
      (eqToHom (congrArg L.tensorPow (Nat.add_comm j i))).app U
        ((L.tensorPowAddIso j i).inv.app U (tmulSection b a)) := by
    apply TopCat.Presheaf.IsSheaf.section_ext (L.tensorPow (i + j)).isSheaf
    intro x hx
    obtain ⟨V, hxV, e, he⟩ := exists_localGenerator L x
    refine ⟨U ⊓ V, inf_le_left, ⟨hx, hxV⟩, ?_⟩
    simp only [← Hom.app_presheaf_map, tmulSection_map]
    exact tensorPowLocalSection_comm (L := L) (U := U ⊓ V)
      (he.map inf_le_right) i j
      ((L.tensorPow i).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a)
      ((L.tensorPow j).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op b)
  exact (heq_of_eq h).trans (eqToHom_app_heq _ _)

private noncomputable instance localGCommRing {T : Scheme.{u}} (L : T.Modules)
    [L.IsInvertible] (U : T.Opens) : DirectSum.GCommRing (LocalComponent L U) where
  mul_zero a := by
    change (L.tensorPowAddIso _ _).inv.app U (tmulSection a 0) = 0
    rw [tmulSection_zero, map_zero]
  zero_mul a := by
    change (L.tensorPowAddIso _ _).inv.app U (tmulSection 0 a) = 0
    rw [zero_tmulSection, map_zero]
  mul_add a b c := by
    change (L.tensorPowAddIso _ _).inv.app U (tmulSection a (b + c)) = _
    rw [tmulSection_add, map_add]
    rfl
  add_mul a b c := by
    change (L.tensorPowAddIso _ _).inv.app U (tmulSection (a + b) c) = _
    rw [add_tmulSection, map_add]
    rfl
  one_mul := localOneMul L U
  mul_one := localMulOne L U
  mul_assoc := localMulAssoc L U
  mul_comm := localMulComm L U
  natCast n := n • (GradedMonoid.GOne.one : LocalComponent L U 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast z := z • (GradedMonoid.GOne.one : LocalComponent L U 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

private noncomputable instance localGAlgebra {T : Scheme.{u}} (L : T.Modules)
    [L.IsInvertible] (U : T.Opens) : DirectSum.GAlgebra Γ(T, U) (LocalComponent L U) where
  toFun := (unitSectionsEquiv U).toAddMonoidHom
  map_one := rfl
  map_mul r s := by
    apply Sigma.ext (Nat.zero_add 0).symm
    apply heq_of_eq
    change unitSectionsEquiv U (r * s) =
      (L.tensorPowAddIso 0 0).inv.app U
        (tmulSection (unitSectionsEquiv U r) (unitSectionsEquiv U s))
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Hom.comp_app, ConcreteCategory.comp_apply]
    change unitSectionsEquiv U (r * s) =
      (λ_ (𝟙_ T.Modules)).hom.app U
        (tmulSection (unitSectionsEquiv U r) (unitSectionsEquiv U s))
    rw [leftUnitor_hom_app_tmulSection, ← (unitSectionsEquiv U).map_smul, smul_eq_mul]
  commutes r a := localMulComm L U _ _
  smul_def r a := by
    obtain ⟨n, a⟩ := a
    apply Sigma.ext (Nat.zero_add n).symm
    change HEq (r • a) ((L.tensorPowAddIso 0 n).inv.app U
      (tmulSection (unitSectionsEquiv U r) a))
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    change HEq (r • a) ((eqToHom (congrArg L.tensorPow (Nat.zero_add n).symm)).app U
      ((λ_ (L.tensorPow n)).hom.app U (tmulSection (unitSectionsEquiv U r) a)))
    rw [leftUnitor_hom_app_tmulSection]
    exact (eqToHom_app_heq _ _).symm

@[irreducible] private noncomputable def localRestrict {T : Scheme.{u}}
    (L : T.Modules) [L.IsInvertible]
    {U V : T.Opens} (j : V ≤ U) :
    (⨁ n : ℕ, LocalComponent L U n) →+* ⨁ n : ℕ, LocalComponent L V n :=
  DirectSum.toSemiring (fun n ↦ (DirectSum.of (LocalComponent L V) n).comp
    ((L.tensorPow n).presheaf.map (homOfLE j).op).hom)
    (by
      change DirectSum.of (LocalComponent L V) 0
        ((𝟙_ T.Modules).presheaf.map (homOfLE j).op (unitSectionsEquiv U 1)) = _
      rw [presheaf_map_unitSectionsEquiv]
      exact congrArg (DirectSum.of (LocalComponent L V) 0 ∘ unitSectionsEquiv V)
        (map_one (T.presheaf.map (homOfLE j).op).hom))
    (by
      intro i k x y
      change DirectSum.of (LocalComponent L V) (i + k)
        ((L.tensorPow (i + k)).presheaf.map (homOfLE j).op
          ((L.tensorPowAddIso i k).inv.app U (tmulSection x y))) = _
      rw [← Hom.app_presheaf_map, tmulSection_map]
      simp only [AddMonoidHom.comp_apply]
      rw [DirectSum.of_mul_of]
      rfl)

private theorem localRestrict_of {T : Scheme.{u}} (L : T.Modules) [L.IsInvertible]
    {U V : T.Opens} (j : V ≤ U) (n : ℕ) (a : Γ(L.tensorPow n, U)) :
    localRestrict L j (DirectSum.of (LocalComponent L U) n a) =
      DirectSum.of (LocalComponent L V) n
        ((L.tensorPow n).presheaf.map (homOfLE j).op a) := by
  unfold localRestrict
  exact DirectSum.toSemiring_of _ _ _ _ _

private noncomputable def quotientAdjoint {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L) :
    E ⟶ (pushforward h).obj L :=
  (tensorPullbackSectionAdjunction h).homEquiv E L q

private theorem quotientAdjoint_apply {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.Opens) (m : Γ(E, U)) :
    (quotientAdjoint h E L q).app U m =
      q.app (h ⁻¹ᵁ U) (tensorPullbackSection h E U m) := by
  rw [quotientAdjoint, Adjunction.homEquiv_unit]
  change q.app (h ⁻¹ᵁ U) (((tensorPullbackSectionAdjunction h).unit.app E).app U m) = _
  exact congrArg (fun x : Γ((tensorPullback h).obj E, h ⁻¹ᵁ U) ↦
    q.app (h ⁻¹ᵁ U) x)
    ((Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction h)).1 E U m)

@[irreducible] private noncomputable def symmetricSectionLift {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) :
    SymmetricAlgebraSheaf.sections E (op U.1) →+*
      ⨁ n : ℕ, LocalComponent L (h ⁻¹ᵁ U.1) n := by
  let B := Γ(T, h ⁻¹ᵁ U.1)
  let D := ⨁ n : ℕ, LocalComponent L (h ⁻¹ᵁ U.1) n
  letI : Algebra Γ(S, U.1) D :=
    ((algebraMap B D).comp (h.app U.1).hom).toAlgebra
  let f : E.val.obj (op U.1) →ₗ[Γ(S, U.1)] D :=
    { toFun := fun m ↦ DirectSum.of (LocalComponent L (h ⁻¹ᵁ U.1)) 1
        ((ρ_ L).inv.app (h ⁻¹ᵁ U.1) ((quotientAdjoint h E L q).app U.1 m))
      map_add' := by intro m n; simp only [map_add]
      map_smul' := by
        intro r m
        have hm : (quotientAdjoint h E L q).app U.1 (r • m) =
            h.app U.1 r •
              (show Γ(L, h ⁻¹ᵁ U.1) from (quotientAdjoint h E L q).app U.1 m) :=
          Hom.app_smul (quotientAdjoint h E L q) r m
        erw [hm, Hom.app_smul]
        have hd := DirectSum.of_smul Γ(T, h ⁻¹ᵁ U.1)
          (M := LocalComponent L (h ⁻¹ᵁ U.1)) 1
          (h.app U.1 r)
          ((ρ_ L).inv.app (h ⁻¹ᵁ U.1) ((quotientAdjoint h E L q).app U.1 m))
        refine hd.trans ?_
        change (h.app U.1 r) • _ = algebraMap B D (h.app U.1 r) * _
        exact Algebra.smul_def _ _ }
  exact (SymmetricAlgebra.lift f).toRingHom

private theorem symmetricSectionLift_generator {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) (m : Γ(E, U.1)) :
    symmetricSectionLift h E L q U (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m) =
      DirectSum.of (LocalComponent L (h ⁻¹ᵁ U.1)) 1
        ((ρ_ L).inv.app (h ⁻¹ᵁ U.1) ((quotientAdjoint h E L q).app U.1 m)) := by
  let : Algebra Γ(S, U.1) (⨁ n : ℕ, LocalComponent L (h ⁻¹ᵁ U.1) n) :=
    ((algebraMap Γ(T, h ⁻¹ᵁ U.1) _).comp (h.app U.1).hom).toAlgebra
  unfold symmetricSectionLift
  exact SymmetricAlgebra.lift_ι_apply _ _

private theorem symmetricSectionLift_scalar {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) (r : Γ(S, U.1)) :
    symmetricSectionLift h E L q U (algebraMap Γ(S, U.1) _ r) =
      DirectSum.of (LocalComponent L (h ⁻¹ᵁ U.1)) 0
        (unitSectionsEquiv (h ⁻¹ᵁ U.1) (h.app U.1 r)) := by
  let : Algebra Γ(S, U.1) (⨁ n : ℕ, LocalComponent L (h ⁻¹ᵁ U.1) n) :=
    ((algebraMap Γ(T, h ⁻¹ᵁ U.1) _).comp (h.app U.1).hom).toAlgebra
  unfold symmetricSectionLift
  exact AlgHom.commutes _ r

private theorem symmetricSectionLift_homogeneous {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) (n : ℕ)
    (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n) :
    ∃ x : LocalComponent L (h ⁻¹ᵁ U.1) n,
      symmetricSectionLift h E L q U a.val = DirectSum.of _ n x := by
  obtain ⟨a, ha⟩ := a
  change a ∈ (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))).range ^ n at ha
  change ∃ x : LocalComponent L (h ⁻¹ᵁ U.1) n,
    symmetricSectionLift h E L q U a = DirectSum.of _ n x
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => exact ⟨_, symmetricSectionLift_scalar h E L q U r⟩
  | add a b n ha hb iha ihb =>
    obtain ⟨x, hx⟩ := iha
    obtain ⟨y, hy⟩ := ihb
    refine ⟨x + y, ?_⟩
    exact (map_add _ a b).trans ((congrArg₂ (· + ·) hx hy).trans
      ((DirectSum.of (LocalComponent L (h ⁻¹ᵁ U.1)) n).map_add x y).symm)
  | mem_mul a ha n b hb ih =>
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨x, hx⟩ := ih
    rw [mul_comm, map_mul, hx, symmetricSectionLift_generator, DirectSum.of_mul_of]
    exact ⟨_, rfl⟩

@[irreducible] private noncomputable def quotientComponent {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) (n : ℕ) :
    (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n →+
      Γ(L.tensorPow n, h ⁻¹ᵁ U.1) :=
  (DFinsupp.evalAddMonoidHom n).comp
    ((symmetricSectionLift h E L q U).toAddMonoidHom.comp
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n).subtype.toAddMonoidHom)

private theorem quotientComponent_of {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) (U : S.affineOpens) (n : ℕ)
    (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n) :
    symmetricSectionLift h E L q U a.val =
      DirectSum.of (LocalComponent L (h ⁻¹ᵁ U.1)) n (quotientComponent h E L q U n a) := by
  obtain ⟨x, hx⟩ := symmetricSectionLift_homogeneous h E L q U n a
  unfold quotientComponent
  change symmetricSectionLift h E L q U a.val = DirectSum.of _ n
    (symmetricSectionLift h E L q U a.val n)
  rw [hx, DirectSum.of_eq_same]

private theorem symmetricSectionLift_restrict {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) {U V : S.affineOpens} (j : V ≤ U)
    (a : SymmetricAlgebraSheaf.sections E (op U.1)) :
    symmetricSectionLift h E L q V
      (SymmetricAlgebraSheaf.restriction E (homOfLE (X := S.Opens) j).op a) =
      localRestrict L (h.preimage_mono j) (symmetricSectionLift h E L q U a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    have hr := congrArg (symmetricSectionLift h E L q V)
      (SymmetricAlgebraSheaf.restriction_algebraMap E (homOfLE (X := S.Opens) j).op r)
    refine hr.trans ?_
    rw [symmetricSectionLift_scalar, symmetricSectionLift_scalar, localRestrict_of]
    apply congrArg (DirectSum.of (LocalComponent L (h ⁻¹ᵁ V.1)) 0)
    change unitSectionsEquiv (h ⁻¹ᵁ V.1) _ =
      (𝟙_ T.Modules).presheaf.map (homOfLE (h.preimage_mono j)).op
        (unitSectionsEquiv (h ⁻¹ᵁ U.1) _)
    rw [presheaf_map_unitSectionsEquiv]
    exact congrArg (unitSectionsEquiv (h ⁻¹ᵁ V.1))
      (CategoryTheory.congr_fun (h.c.naturality (homOfLE (X := S.Opens) j).op) r)
  | ι m =>
    rw [SymmetricAlgebraSheaf.restriction_ι, symmetricSectionLift_generator,
      symmetricSectionLift_generator, localRestrict_of]
    apply congrArg (DirectSum.of (LocalComponent L (h ⁻¹ᵁ V.1)) 1)
    change (ρ_ L).inv.app (h ⁻¹ᵁ V.1) _ =
      (L ⊗ 𝟙_ T.Modules).presheaf.map (homOfLE (h.preimage_mono j)).op _
    exact (congrArg ((ρ_ L).inv.app (h ⁻¹ᵁ V.1))
      (PresheafOfModules.naturality_apply (quotientAdjoint h E L q).val
        (homOfLE (X := S.Opens) j).op m)).trans
      (Hom.app_presheaf_map (ρ_ L).inv (homOfLE (h.preimage_mono j))
        ((quotientAdjoint h E L q).app U.1 m))
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private noncomputable def quotientGradedExtension {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) :
    RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L where
  component := quotientComponent h E L q
  smul U n r a := by
    apply DirectSum.of_injective n
    rw [DirectSum.of_smul, ← quotientComponent_of]
    change symmetricSectionLift h E L q U
      (r • a.val) = _
    change symmetricSectionLift h E L q U
      (algebraMap Γ(S, U.1) (SymmetricAlgebraSheaf.sections E (op U.1)) r *
        (show SymmetricAlgebraSheaf.sections E (op U.1) from a.val)) = _
    rw [map_mul, symmetricSectionLift_scalar, quotientComponent_of,
      DirectSum.of_mul_of]
    rw [← DirectSum.of_smul]
    exact DFinsupp.single_eq_of_sigma_eq (DirectSum.GAlgebra.smul_def
      (A := LocalComponent L (h ⁻¹ᵁ U.1)) (h.app U.1 r)
      ⟨n, quotientComponent h E L q U n a⟩).symm

  one U := by
    apply (DirectSum.of_injective (β := LocalComponent L (h ⁻¹ᵁ U.1)) 0)
    rw [← quotientComponent_of]
    exact (map_one _).trans rfl
  mul U m n a b := by
    apply (DirectSum.of_injective (β := LocalComponent L (h ⁻¹ᵁ U.1)) (m + n))
    rw [← quotientComponent_of]
    change symmetricSectionLift h E L q U (a.val * b.val) = _
    rw [map_mul, quotientComponent_of h E L q U m a,
      quotientComponent_of h E L q U n b, DirectSum.of_mul_of]
    rfl
  restriction j n a := by
    apply DirectSum.of_injective n
    rw [← quotientComponent_of]
    change symmetricSectionLift h E L q _
      (SymmetricAlgebraSheaf.restriction E (homOfLE j).op a.val) = _
    erw [symmetricSectionLift_restrict]
    rw [quotientComponent_of, localRestrict_of]
    rfl

private theorem quotientGradedExtension_extends {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) :
    (quotientGradedExtension h E L q).ExtendsLineQuotient h E L q := by
  intro U m
  have hh := quotientComponent_of h E L q U 1 (quotientSymmetricGenerator E U m)
  rw [show (quotientSymmetricGenerator E U m).val =
    SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m from rfl,
    symmetricSectionLift_generator] at hh
  have he := DirectSum.of_injective 1 hh
  change (ρ_ L).hom.app (h ⁻¹ᵁ U.1) (quotientComponent h E L q U 1 _) = _
  rw [← he]
  change Hom.app ((ρ_ L).inv ≫ (ρ_ L).hom) (h ⁻¹ᵁ U.1) _ = _
  rw [Iso.inv_hom_id]
  exact quotientAdjoint_apply h E L q U.1 m

private theorem quotientFramePower_generator {T : Scheme.{u}} {L : T.Modules}
    {W : T.Opens} {l : Γ(L, W)} (hl : IsFreeGenerator l) (d : ℕ) :
    IsFreeGenerator (quotientFramePower l d) := by
  induction d with
  | zero => exact isFreeGenerator_one W
  | succ d ih => exact hl.tmulSection ih

private theorem quotientCoefficient_smul_frame {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules} (ψ : RelativeGradedLineMap h A L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (d : ℕ) (a : A.grading U d) :
    ψ.quotientCoefficient U W hWU l d a • quotientFramePower l d =
      (L.tensorPow d).val.map (homOfLE hWU).op (ψ.component U d a) := by
  exact Function.invFun_eq ((quotientFramePower_generator hl d).bijective.surjective _)

private theorem quotientFramePower_smul {T : Scheme.{u}} {L : T.Modules}
    {W : T.Opens} (r : Γ(T, W)) (l : Γ(L, W)) (d : ℕ) :
    quotientFramePower (r • l) d = r ^ d • quotientFramePower l d := by
  induction d with
  | zero => simp only [quotientFramePower, pow_zero, one_smul]
  | succ d ih =>
    simp only [quotientFramePower, ih, smul_tmulSection, tmulSection_smul, smul_smul,
      pow_succ, mul_comm]

private theorem quotientFramePower_map {T : Scheme.{u}} {L : T.Modules}
    {W W' : T.Opens} (j : W' ≤ W) (l : Γ(L, W)) (d : ℕ) :
    quotientFramePower (L.val.map (homOfLE j).op l) d =
      (L.tensorPow d).val.map (homOfLE j).op (quotientFramePower l d) := by
  induction d with
  | zero =>
    change unitSectionsEquiv W' 1 =
      (𝟙_ T.Modules).presheaf.map (homOfLE j).op (unitSectionsEquiv W 1)
    rw [presheaf_map_unitSectionsEquiv]
    exact congrArg (unitSectionsEquiv W') (map_one (T.presheaf.map (homOfLE j).op).hom).symm
  | succ d ih => exact (congrArg (tmulSection _) ih).trans (tmulSection_map j _ _).symm

private theorem quotientCoefficient_generator {S T : Scheme.{u}} {h : T ⟶ S}
    {E : S.Modules} [E.IsQuasicoherent] {L : T.Modules}
    {q : (tensorPullback h).obj E ⟶ L}
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1)) :
    ψ.quotientCoefficient U W hWU l 1 (quotientSymmetricGenerator E U m) =
      quotientGeneratorCoefficient h E L q U W hWU l m := by
  apply hl.smul_left_injective
  dsimp only
  have hc := quotientCoefficient_smul_frame ψ U W hWU l hl 1
    (quotientSymmetricGenerator E U m)
  have he := congrArg (fun x ↦ (ρ_ L).hom.app W.1 x) hc
  rw [Hom.app_smul] at he
  change _ • (ρ_ L).hom.app W.1 (tmulSection l (unitSectionsEquiv W.1 1)) = _ at he
  rw [rightUnitor_hom_app_tmulSection, one_smul] at he
  change _ = (ρ_ L).hom.app W.1
    ((L.tensorPow 1).presheaf.map (homOfLE hWU).op _) at he
  erw [Hom.app_presheaf_map, hψ U m] at he
  rw [he]
  exact (Hom.app_presheaf_map q (homOfLE hWU) _).symm.trans
    (Function.invFun_eq (hl.bijective.surjective
    (q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
      (tensorPullbackSection h E U.1 m))))).symm

private theorem quotientCoefficient_frame_change {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules} (ψ : RelativeGradedLineMap h A L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (v : Γ(T, W.1)ˣ)
    (d : ℕ) (a : A.grading U d) :
    ψ.quotientCoefficient U W hWU (v.val • l) d a =
      (↑(v⁻¹) : Γ(T, W.1)) ^ d * ψ.quotientCoefficient U W hWU l d a := by
  apply (quotientFramePower_generator (hl.units_smul v) d).smul_left_injective
  dsimp only
  rw [quotientCoefficient_smul_frame ψ U W hWU _ (hl.units_smul v),
    quotientFramePower_smul, smul_smul]
  have hv : (↑(v⁻¹) : Γ(T, W.1)) ^ d *
      ψ.quotientCoefficient U W hWU l d a * (↑v : Γ(T, W.1)) ^ d =
        ψ.quotientCoefficient U W hWU l d a := by
    rw [mul_right_comm, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  rw [hv]
  exact (quotientCoefficient_smul_frame ψ U W hWU l hl d a).symm

private theorem quotientCoefficient_source_restrict {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules} (ψ : RelativeGradedLineMap h A L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (W' : T.affineOpens) (j : W' ≤ W)
    (hW'U : W'.1 ≤ h ⁻¹ᵁ U.1) (d : ℕ) (a : A.grading U d) :
    ψ.quotientCoefficient U W' hW'U (L.val.map (homOfLE j).op l) d a =
      T.presheaf.map (homOfLE j).op (ψ.quotientCoefficient U W hWU l d a) := by
  apply (quotientFramePower_generator (hl.map j) d).smul_left_injective
  dsimp only
  erw [quotientCoefficient_smul_frame ψ U W' hW'U _ (hl.map j),
    quotientFramePower_map]
  have he := congrArg (fun x : Γ(L.tensorPow d, W.1) ↦
      (L.tensorPow d).presheaf.map (homOfLE (X := T.Opens) j).op x)
    (quotientCoefficient_smul_frame ψ U W hWU l hl d a)
  rw [map_smul] at he
  have he' : (L.tensorPow d).presheaf.map (homOfLE (X := T.Opens) j).op
      ((L.tensorPow d).presheaf.map (homOfLE hWU).op (ψ.component U d a)) =
        (L.tensorPow d).presheaf.map (homOfLE hW'U).op (ψ.component U d a) := by
    rw [presheaf_map_map_apply]
    rfl
  exact he'.symm.trans he.symm

private theorem quotientCoefficient_base_restrict {S T : Scheme.{u}} {h : T ⟶ S}
    {A : S.GradedAlgebraData} {L : T.Modules} (ψ : RelativeGradedLineMap h A L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (U' : S.affineOpens) (j : U' ≤ U)
    (hWU' : W.1 ≤ h ⁻¹ᵁ U'.1) (d : ℕ) (a : A.grading U d) :
    ψ.quotientCoefficient U' W hWU' l d ⟨A.res j a, (A.res j).map_mem a.property⟩ =
      ψ.quotientCoefficient U W hWU l d a := by
  apply (quotientFramePower_generator hl d).smul_left_injective
  dsimp only
  erw [quotientCoefficient_smul_frame ψ U' W hWU' l hl,
    quotientCoefficient_smul_frame ψ U W hWU l hl, ψ.restriction,
    presheaf_map_map_apply]
  rfl

private theorem lineQuotient_extension_unique {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hψ' : ψ'.ExtendsLineQuotient h E L q) : ψ = ψ' := by
  have hgen (U : S.affineOpens) (m : Γ(E, U.1)) :
      ψ.component U 1 (quotientSymmetricGenerator E U m) =
        ψ'.component U 1 (quotientSymmetricGenerator E U m) := by
    apply (ConcreteCategory.bijective_of_isIso ((ρ_ L).hom.app (h ⁻¹ᵁ U.1))).injective
    exact (hψ U m).trans (hψ' U m).symm
  have hcomp (U : S.affineOpens) (n : ℕ)
      (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n) :
      ψ.component U n a = ψ'.component U n a := by
    obtain ⟨a, ha⟩ := a
    change a ∈ (SymmetricAlgebra.ι Γ(S, U.1) Γ(E, U.1)).range ^ n at ha
    induction ha using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      have hs : (⟨algebraMap Γ(S, U.1) _ r,
        SetLike.algebraMap_mem_graded _ r⟩ :
          (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 0) =
          r • ⟨1, SetLike.one_mem_graded _⟩ := by
        apply Subtype.ext
        exact (Algebra.smul_def r 1).trans (mul_one _ ) |>.symm
      rw [hs, ψ.smul, ψ'.smul, ψ.one, ψ'.one]
    | add a b n ha hb iha ihb =>
      change ψ.component U n (⟨a, ha⟩ + ⟨b, hb⟩) =
        ψ'.component U n (⟨a, ha⟩ + ⟨b, hb⟩)
      rw [map_add, map_add, iha, ihb]
    | mem_mul a ha n b hb ih =>
      obtain ⟨m, rfl⟩ := ha
      have hm := hgen U m
      have hx := ψ.mul U n 1 ⟨b, hb⟩ (quotientSymmetricGenerator E U m)
      have hx' := ψ'.mul U n 1 ⟨b, hb⟩ (quotientSymmetricGenerator E U m)
      have hh := hx.trans ((congrArg₂ (fun x y ↦ (L.tensorPowAddIso n 1).inv.app
        (h ⁻¹ᵁ U.1) (tmulSection x y)) ih hm).trans hx'.symm)
      simpa only [quotientSymmetricGenerator, mul_comm] using hh
  cases ψ
  cases ψ'
  congr
  funext U n
  exact AddMonoidHom.ext (hcomp U n)

private theorem quotientGeneratorCoefficient_smul {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient h E L q U W hWU l m • l =
      q.app W.1 (((tensorPullback h).obj E).val.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)) := by
  exact Function.invFun_eq (hl.bijective.surjective _)

private theorem quotientGeneratorCoefficient_cover {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) :
    (⨆ m : Γ(E, U.1),
      T.basicOpen (quotientGeneratorCoefficient h E L q U W hWU l m)) = W.1 := by
  classical
  let b := quotientGeneratorCoefficient h E L q U W hWU l
  let I : Ideal Γ(T, W.1) := Ideal.span (Set.range b)
  let : Algebra Γ(S, U.1) Γ(T, W.1) := (h.appLE U.1 W.1 hWU).hom.toAlgebra
  let : ∀ G : S.Modules, Module Γ(S, U.1) Γ((tensorPullback h).obj G, W.1) :=
    fun G ↦ Module.compHom _ (h.appLE U.1 W.1 hWU).hom
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections h U W hWU
  have ht (t : Γ(E, U.1) ⊗[Γ(S, U.1)] Γ(T, W.1)) :
      hl.coeff (q.app W.1 (c E inferInstance t)) ∈ I := by
    induction t using TensorProduct.inductionOn with
    | tmul m r =>
      rw [hp, Hom.app_smul, hl.coeff_smul_left]
      apply I.mul_mem_left
      have he : hl.coeff (q.app W.1
          (((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
            (((Classical.choose (exists_tensorPullbackAdjunction h)).unit.app E).val.app
              (op U.1) m))) = b m := by
        apply hl.smul_left_injective
        dsimp only
        rw [hl.coeff_smul, quotientGeneratorCoefficient_smul h E L q U W hWU l hl]
        exact congrArg (fun z : Γ((tensorPullback h).obj E, h ⁻¹ᵁ U.1) ↦
          q.app W.1 (((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op z))
          (Classical.choose_spec (exists_tensorPullbackAdjunction h) E (op U.1) m)
      rw [he]
      exact Ideal.subset_span ⟨m, rfl⟩
    | add t t' ht ht' =>
      rw [map_add, map_add, hl.coeff_add]
      exact I.add_mem ht ht'
  obtain ⟨s, hs⟩ := surjective_affine_of_epi q W.2 l
  obtain ⟨t, rfl⟩ := (hc E inferInstance).surjective s
  have htop : I = ⊤ := by
    apply I.eq_top_of_isUnit_mem (ht t)
    rw [hs]
    have he : hl.coeff l = (1 : Γ(T, W.1)) := by
      simpa only [one_smul] using hl.coeff_smul_self (1 : Γ(T, W.1))
    rw [he]
    exact isUnit_one
  have hcov := iSup_basicOpen_of_span_eq_top W.1 (Set.range b) htop
  simpa only [iSup_range] using hcov

private theorem lineQuotient_generates {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q) : ψ.GeneratesEverywhere := by
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h x) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  have hxU : x ∈ h ⁻¹ᵁ U.1 := hxV
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨W, hxW, hWU, l, hl⟩ := exists_isFreeGenerator L hxU
  have hx : x ∈ (⨆ m : Γ(E, U.1),
      T.basicOpen (quotientGeneratorCoefficient h E L q U W hWU l m)) := by
    rw [quotientGeneratorCoefficient_cover h E L q U W hWU l hl]
    exact hxW
  obtain ⟨m, hxm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨U, hxU, 1, by decide, quotientSymmetricGenerator E U m, ?_⟩
  let p := quotientFramePower l 1
  let b := quotientGeneratorCoefficient h E L q U W hWU l m
  let px := (L.tensorPow 1).presheaf.germ W.1 x hxW p
  have hb : Function.Bijective (fun a : T.presheaf.stalk x ↦ a • px) :=
    stalk_generator_bijective (quotientFramePower_generator hl 1) x hxW
  have hspan : Submodule.span (T.presheaf.stalk x) {px} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff _ px).mpr hb.surjective
  have hs : (L.tensorPow 1).presheaf.map (homOfLE hWU).op
      (ψ.component U 1 (quotientSymmetricGenerator E U m)) = b • p := by
    have he := (quotientCoefficient_smul_frame ψ U W hWU l hl 1
      (quotientSymmetricGenerator E U m)).symm
    erw [quotientCoefficient_generator ψ hψ U W hWU l hl] at he
    exact he
  change (L.tensorPow 1).presheaf.germ (h ⁻¹ᵁ U.1) x hxU _ ∉ _
  rw [← (L.tensorPow 1).presheaf.germ_res_apply (homOfLE hWU) x hxW, hs, germ_smul]
  rw [← hspan, Submodule.mem_smul_span_singleton]
  rintro ⟨a, ha, he⟩
  have hab : a = T.presheaf.germ W.1 x hxW b := hb.injective he
  rw [hab, IsLocalRing.mem_maximalIdeal] at ha
  exact ha ((T.mem_basicOpen b x hxW).mp hxm)

private theorem localized_ratio_isUnit {R : Type u} [CommRing R] (b c : R) :
    IsUnit (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away b) (P := Localization.Away (b * c)) b c
      (Localization.mk c (⟨b ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers b))) := by
  let φ := IsLocalization.Away.awayToAwayRight
    (S := Localization.Away b) (P := Localization.Away (b * c)) b c
  have he := congrArg φ (IsLocalization.mk'_spec (Localization.Away b) c
    (⟨b, ⟨1, pow_one b⟩⟩ : Submonoid.powers b))
  rw [map_mul, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayRight_eq] at he
  have hu : IsUnit (algebraMap R (Localization.Away (b * c)) c) :=
    IsLocalization.Away.isUnit_of_dvd (b * c) (dvd_mul_left c b)
  rw [← he] at hu
  simpa only [Localization.mk_eq_mk', pow_one] using isUnit_of_mul_isUnit_left hu

private instance quotientFractionSource_isOpenImmersion {T : Scheme.{u}}
    (W : T.affineOpens) (b : Γ(T, W.1)) :
    IsOpenImmersion (quotientFractionSource W b) := by
  unfold quotientFractionSource
  infer_instance

private theorem quotientFractionSource_opensRange {T : Scheme.{u}}
    (W : T.affineOpens) (b : Γ(T, W.1)) :
    (quotientFractionSource W b).opensRange = T.basicOpen b := by
  change (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W.1) (Localization.Away b))) ≫
    W.2.fromSpec).opensRange = _
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
    W.2.fromSpec_image_basicOpen]

private theorem quotientFractionCharts_unique {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F F' : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : ψ.HasQuotientFractionCharts h E L q F)
    (hF' : ψ.HasQuotientFractionCharts h E L q F') : F = F' := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := h x) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  have hxU : x ∈ h ⁻¹ᵁ U.1 := hxV
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨W, hxW, hWU, l, hl⟩ := exists_isFreeGenerator L hxU
  have hW := hF.2 U W hWU l hl
  have hW' := hF'.2 U W hWU l hl
  have hx : x ∈ (⨆ m : Γ(E, U.1),
      T.basicOpen (quotientGeneratorCoefficient h E L q U W hWU l m)) := by
    rw [hW.2.2.1]
    exact hxW
  obtain ⟨m, hxm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨ρ, hρ⟩ := hW.2.2.2.1 m
  obtain ⟨ρ', hρ'⟩ := hW'.2.2.2.1 m
  have he : ρ = ρ' := by
    let := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
    ext z
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).property z
    have ha' : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U n := by
      simpa only [smul_eq_mul, mul_one] using ha
    exact (hρ.1 n ⟨a, ha'⟩).trans (hρ'.1 n ⟨a, ha'⟩).symm
  have hs : quotientFractionSource W
      (quotientGeneratorCoefficient h E L q U W hWU l m) ≫ F =
        quotientFractionSource W
      (quotientGeneratorCoefficient h E L q U W hWU l m) ≫ F' := by
    rw [hρ.2.2.1, hρ'.2.2.1, he]
  let f := quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l m)
  refine ⟨f.opensRange, ?_, ?_⟩
  · rwa [quotientFractionSource_opensRange]
  · rw [← cancel_epi (Scheme.Hom.isoOpensRange f).hom]
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι] using hs

private theorem quotientChart_transport_eq
    {S T : Scheme.{u}} (h : T ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l l' : Γ(L, W.1)) (m : Γ(E, U.1))
    (ρ : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+*
        Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m))
    (ρ' : HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val →+*
        Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l' m))
    (hρ : ψ.IsQuotientFractionChart h E L q F U W hWU l m ρ)
    (hρ' : ψ.IsQuotientFractionChart h E L q F U W hWU l' m ρ')
    (C : Type u) [CommRing C]
    (β : Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m) →+* C)
    (β' : Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l' m) →+* C)
    (hβ : β.comp (algebraMap Γ(T, W.1) _) =
      β'.comp (algebraMap Γ(T, W.1) _)) : β.comp ρ = β'.comp ρ' := by
  have hs : Spec.map (CommRingCat.ofHom β) ≫
        quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l m) =
      Spec.map (CommRingCat.ofHom β') ≫
        quotientFractionSource W (quotientGeneratorCoefficient h E L q U W hWU l' m) := by
    simp only [quotientFractionSource, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f) ≫ W.2.isoSpec.inv ≫ W.1.ι) hβ
  have hc := congrArg (fun f ↦ f ≫ F) hs
  simp only [Category.assoc, hρ.2.2.1, hρ'.2.2.1] at hc
  simp only [← Category.assoc] at hc
  have hc' := (cancel_mono ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).1 hc
  have hc'' := (cancel_mono (Proj.awayι
    ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
    (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
    (by decide : 0 < (1 : ℕ)))).1 hc'
  have he : CommRingCat.ofHom (β.comp ρ) = CommRingCat.ofHom (β'.comp ρ') := by
    apply Spec.map_injective
    simpa only [← Spec.map_comp, CommRingCat.ofHom_comp] using hc''
  exact congrArg CommRingCat.Hom.hom he

private theorem quotient_frame_independent
    {S T : Scheme.{u}} (h : T ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) :
    ψ.QuotientFrameIndependent h E L q F := by
  intro U W hWU l _ v m ρ ρ' hρ hρ' C _ β β' hβ
  exact quotientChart_transport_eq h E L q ψ F U W hWU l _ m ρ ρ' hρ hρ' C β β' hβ

/-- The unique graded extension of an arbitrary quasi-coherent line quotient, and its
unique morphism to the canonical relative Proj with all homogeneous fraction formulas. -/
theorem line_quotient_homogeneous_fraction_map {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q] :
    ∃ ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L,
      ψ.ExtendsLineQuotient h E L q ∧
      (∀ ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L,
        ψ'.ExtendsLineQuotient h E L q → ψ' = ψ) ∧
      ψ.GeneratesEverywhere ∧
      ∃ F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
        ψ.HasQuotientFractionCharts h E L q F ∧
        ψ.QuotientFrameIndependent h E L q F ∧ ψ.IsCanonicalMap F ∧
        ∀ F' : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          ψ.HasQuotientFractionCharts h E L q F' → F' = F := by
  let ψ := quotientGradedExtension h E L q
  have hψ := quotientGradedExtension_extends h E L q
  have hgen := lineQuotient_generates h E L q ψ hψ
  obtain ⟨F, hcan, hcharts⟩ := graded_line_homogeneous_fraction_atlas h
    (SymmetricAlgebraSheaf.gradedAlgebraData E) L ψ hgen
    (fun l n ↦ quotientFramePower l n) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun U W hWU l n a ↦ ψ.quotientCoefficient U W hWU l n a)
    (fun U W hWU l hl n a ↦ quotientCoefficient_smul_frame ψ U W hWU l hl n a)
  have hF : ψ.HasQuotientFractionCharts h E L q F := by
    refine ⟨hcan.1, ?_⟩
    intro U W hWU l hl
    refine ⟨quotientCoefficient_smul_frame ψ U W hWU l hl,
      quotientCoefficient_generator ψ hψ U W hWU l hl,
      quotientGeneratorCoefficient_cover h E L q U W hWU l hl, ?_,
      quotientCoefficient_frame_change ψ U W hWU l hl,
      quotientCoefficient_source_restrict ψ U W hWU l hl,
      quotientCoefficient_base_restrict ψ U W hWU l hl⟩
    intro m
    have hc := hcharts U W hWU l hl 1 (by decide) (quotientSymmetricGenerator E U m)
    dsimp only at hc
    rw [quotientCoefficient_generator ψ hψ U W hWU l hl m] at hc
    simp only [smul_eq_mul] at hc
    obtain ⟨ρ, hρ, hscalar, hscheme⟩ := hc
    refine ⟨ρ, ?_, hscalar, hscheme, ?_⟩
    · intro d a
      have hd := hρ d ⟨a.val, by simpa only [Nat.mul_one] using a.property⟩
      have hn : ∀ (k : ℕ) (hk : k = d),
          ψ.quotientCoefficient U W hWU l k
            ⟨a.val, by simpa only [hk] using a.property⟩ =
              ψ.quotientCoefficient U W hWU l d a := by
        intro k hk
        subst k
        rfl
      rw [hn (d * 1) (Nat.mul_one d)] at hd
      simpa only [degreeOneQuotientFraction] using hd
    · intro n
      rw [show ρ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
        (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U n)) =
          Localization.mk (ψ.quotientCoefficient U W hWU l 1
            (quotientSymmetricGenerator E U n))
            (⟨quotientGeneratorCoefficient h E L q U W hWU l m ^ 1,
              ⟨1, rfl⟩⟩ : Submonoid.powers
                (quotientGeneratorCoefficient h E L q U W hWU l m)) from
          by simpa only [smul_eq_mul, mul_one, degreeOneQuotientFraction] using
            hρ 1 (quotientSymmetricGenerator E U n),
        quotientCoefficient_generator ψ hψ U W hWU l hl]
      exact localized_ratio_isUnit _ _
  refine ⟨ψ, hψ, ?_, hgen, F, hF, quotient_frame_independent h E L q ψ F, hcan, ?_⟩
  · intro ψ' hψ'
    exact lineQuotient_extension_unique h E L q ψ' ψ hψ' hψ
  · intro F' hF'
    exact quotientFractionCharts_unique h E L q ψ F' F hF' hF

end AlgebraicGeometry.Scheme.Modules
