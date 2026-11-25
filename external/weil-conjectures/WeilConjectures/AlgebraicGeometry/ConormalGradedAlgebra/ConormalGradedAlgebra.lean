/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraBasic
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafStalk
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraConstruction
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraStalk
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalPieceStalk
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore
import all WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The conormal graded algebra of a closed immersion

Source: Stacks Project, Divisors, Tags 0630, 0631, 0632, 0633; coherence, Tag 01XZ
(blueprint: lem-pur-conormal-graded-algebra).

The homogeneous modules are actual tensor pullbacks of the ideal powers. The algebra is
specified by a coproduct universal property and the product of representatives, which
uniquely determine it up to the unique isomorphism preserving its homogeneous inclusions.
Thus the existence theorem below postpones only the construction's universal property;
it cannot supply an arbitrary quasi-coherent algebra unrelated to the closed immersion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.ConormalGradedAlgebra

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- A universal presentation of the actual conormal algebra. Its underlying module is the
sheaf coproduct of `i^*(I^n)`; products and constants have their representative formulas.
The affine and stalk charts preserve those classes, and hence specify graded charts.
Source: Stacks Tags 0630--0633, 01XZ
(blueprint: lem-pur-conormal-graded-algebra). -/
structure Presentation where
  algebra : Z.CommAlgebraSheaf
  inclusion : ∀ n, piece i n ⟶ algebra.toModule
  coproduct : IsColimit (Cofan.mk algebra.toModule inclusion)
  quasicoherent : algebra.toModule.IsQuasicoherent
  pieceQuasicoherent : ∀ n, (piece i n).IsQuasicoherent
  powerIdentification : ∀ n,
    ∃ e : power i n ≅ (i.ker ^ n).toModules,
      e.hom ≫ (i.ker ^ n).toModulesι = powerInclusion i n
  multiplication : ∀ (m n : ℕ) (U : X.Opens)
    (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
    (d : (power i (m + n)).val.obj (op U)),
    (powerInclusion i (m + n)).val.app (op U) d =
        (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
          (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b)) →
      homogeneousClass i algebra inclusion m U a * homogeneousClass i algebra inclusion n U b =
        homogeneousClass i algebra inclusion (m + n) U d
  constants : ∀ (U : X.Opens) (a : (power i 0).val.obj (op U)),
    homogeneousClass i algebra inclusion 0 U a =
      algebra.hom.hom.app (op (i ⁻¹ᵁ U)) (i.app U a)
  pushforwardPiece : ∀ n,
    ∃ e : (Scheme.Modules.pushforward i).obj (piece i n) ≅
        formalAssociatedGradedPiece i.ker n,
      ∀ (U : X.Opens) (a : (power i n).val.obj (op U)),
        e.hom.val.app (op U) (representative i n U a) =
          (formalAssociatedGradedπ i.ker n).val.app (op U) a
  degreeZero : Nonempty (piece i 0 ≅ SheafOfModules.unit Z.ringCatSheaf)
  affineChart : ∀ U : X.affineOpens,
    ∃ e : algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
        CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)),
      ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
        ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
          e.hom (homogeneousClass i algebra inclusion n U.1 a) =
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)
  stalkChart : ∀ z : Z,
    ∃ e : TopCat.Presheaf.stalk algebra.right.obj z ≅
        CommRingCat.of (Ideal.associatedGraded (RingHom.ker (i.stalkMap z).hom)),
      ∀ (n : ℕ) (U : X.Opens) (hz : i z ∈ U) (a : (power i n).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i n).val.app (op U) a) ∈
              RingHom.ker (i.stalkMap z).hom ^ n,
          e.hom (TopCat.Presheaf.germ algebra.right.obj (i ⁻¹ᵁ U) z hz
            (homogeneousClass i algebra inclusion n U a)) =
              DirectSum.of (Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom)) n
                (Submodule.Quotient.mk
                  ⟨X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a), h⟩)
  conormalStalk : ∀ z : Z,
    ∃ e : ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)) ≃+
        (RingHom.ker (i.stalkMap z).hom).Cotangent,
      (∀ (r : X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom)
        (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)),
        e (quotientStalk i z r • x) = r • e x) ∧
      ∀ (U : X.Opens) (hz : i z ∈ U) (a : (power i 1).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i 1).val.app (op U) a) ∈ RingHom.ker (i.stalkMap z).hom,
          e (TopCat.Presheaf.germ (piece i 1).presheaf (i ⁻¹ᵁ U) z hz
            (representative i 1 U a)) =
              (RingHom.ker (i.stalkMap z).hom).toCotangent
                ⟨X.presheaf.germ U (i z) hz ((powerInclusion i 1).val.app (op U) a), h⟩
  symmetricStalk : ∀ z : Z,
    ∃ e : TopCat.Presheaf.stalk (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj z ≅
        CommRingCat.of (SymmetricAlgebra (Z.presheaf.stalk z)
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1))),
      (∀ (U : Z.Opens) (hz : z ∈ U) (r : Γ(Z, U)),
        e.hom (TopCat.Presheaf.germ (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj
          U z hz ((SymmetricAlgebraSheaf.algebra (piece i 1)).hom.hom.app (op U) r)) =
            algebraMap (Z.presheaf.stalk z)
              (SymmetricAlgebra (Z.presheaf.stalk z)
                ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)))
              (Z.presheaf.germ U z hz r)) ∧
      ∀ (U : Z.Opens) (hz : z ∈ U) (a : (piece i 1).val.obj (op U)),
        e.hom (TopCat.Presheaf.germ (SymmetricAlgebraSheaf.algebra (piece i 1)).right.obj
          U z hz ((SymmetricAlgebraSheaf.inclusion (piece i 1)).val.app (op U) a)) =
            SymmetricAlgebra.ι (Z.presheaf.stalk z)
              ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1))
              (TopCat.Presheaf.germ (piece i 1).presheaf U z hz a)
  coherent : IsLocallyNoetherian X → ∀ n,
    RingedSpace.IsCoherent Z.toRingedSpace (piece i n)
  symmetricComparison : ∃! ψ : SymmetricAlgebraSheaf.algebra (piece i 1) ⟶ algebra,
    ∀ (U : Z.Opens) (a : (piece i 1).val.obj (op U)),
      ψ.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion (piece i 1)).val.app (op U) a) =
        (inclusion 1).val.app (op U) a
  augmentation : ∃! ε : algebra ⟶ Under.mk (𝟙 Z.sheaf),
    ∀ (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)),
      ε.right.hom.app (op (i ⁻¹ᵁ U)) (homogeneousClass i algebra inclusion n U a) =
        if n = 0 then i.app U ((powerInclusion i n).val.app (op U) a) else 0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ring_iso_inv_eq {R S : CommRingCat.{u}} (e : R ≅ S)
    {a : R} {b : S} (h : e.hom a = b) : e.inv b = a :=
  (congrArg e.inv h.symm).trans (CommRingCat.inv_hom_apply e a)

omit [IsClosedImmersion i] in
private theorem power_identification (n : ℕ) :
    ∃ e : power i n ≅ (i.ker ^ n).toModules,
      e.hom ≫ (i.ker ^ n).toModulesι = powerInclusion i n :=
  power_iso i.ker n

omit [IsClosedImmersion i] in
private theorem power_quasicoherent (n : ℕ) : (power i n).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  cases n with
  | zero => exact inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent
  | succ n =>
    exact (Scheme.Modules.ideal_times_quasiCoherent_affine_sections i.ker
      (SheafOfModules.unit X.ringCatSheaf)).2.2.1 (n + 1) (Nat.succ_pos n)

omit [IsClosedImmersion i] in
private theorem piece_quasicoherent (n : ℕ) : (piece i n).IsQuasicoherent := by
  let F := power i n
  have : F.IsQuasicoherent := power_quasicoherent i n
  let e : Scheme.Modules.tensorPullback i ≅ Scheme.Modules.pullback i :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction i)
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    (e.app F).symm (by infer_instance)

private theorem pushforward_piece (n : ℕ) :
    ∃ e : (Scheme.Modules.pushforward i).obj (piece i n) ≅
        formalAssociatedGradedPiece i.ker n,
      ∀ (U : X.Opens) (a : (power i n).val.obj (op U)),
        e.hom.val.app (op U) (representative i n U a) =
          (formalAssociatedGradedπ i.ker n).val.app (op U) a := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)
  obtain ⟨e, he⟩ := closedImmersion_power_quotient i.ker 1 i (by simp) adj (power i n)
  refine ⟨e.symm, ?_⟩
  intro U a
  have h : adj.unit.app (power i n) ≫ e.inv = formalAssociatedGradedπ i.ker n := by
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
    rfl
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app (op U)) h) a

omit [IsClosedImmersion i] in
private theorem degree_zero : Nonempty (piece i 0 ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  have := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso i).1
  exact ⟨asIso (Scheme.Modules.tensorPullbackObjUnitToUnit i)⟩

private theorem piece_coherent [IsLocallyNoetherian X] (n : ℕ) :
    RingedSpace.IsCoherent Z.toRingedSpace (piece i n) := by
  have hq : (power i n).IsQuasicoherent := power_quasicoherent i n
  have hf (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(power i n, U.1) := by
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let f : Γ(power i n, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) :=
      ((powerInclusion i n).val.app (op U.1)).hom
    exact Module.Finite.of_injective f
      (formalPolynomial_power_injective i.ker.toModulesι n U.1)
  have ht : (power i n).IsFiniteType :=
    ((Scheme.Modules.quasicoherent_finite_type_affine X).2 (power i n) hq).2.1
      X.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top X) (fun U ↦ U.2) hf |>.1
  have hp : (piece i n).IsFiniteType :=
    (Scheme.Modules.tensorPullback_isFiniteType Z X i (power i n)).1
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (piece i n)).mpr ⟨piece_quasicoherent i n, hp⟩

private theorem power_lift (A : Presentation i) (U : X.affineOpens) (n : ℕ)
    (a : Γ(X, U.1)) (ha : a ∈ i.ker.ideal U ^ n) :
    ∃ b : (power i n).val.obj (op U.1),
      (powerInclusion i n).val.app (op U.1) b = a := by
  obtain ⟨e, he⟩ := A.powerIdentification n
  have ha' : a ∈ Set.range ((i.ker ^ n).toModulesι.app U.1) := by
    rw [(i.ker ^ n).range_toModulesι_app U]
    simpa using ha
  obtain ⟨c, hc⟩ := ha'
  refine ⟨e.inv.val.app (op U.1) c, ?_⟩
  have hh : e.inv ≫ powerInclusion i n = (i.ker ^ n).toModulesι := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact (congrArg (fun k ↦ k.val.app (op U.1) c) hh).trans hc

private theorem ambient_affine_section_ext (F : Z.CommAlgebraSheaf) (U : Z.Opens)
    (s t : F.right.obj.obj (op U))
    (h : ∀ (V : X.affineOpens) (hVU : i ⁻¹ᵁ V.1 ≤ U),
      F.right.obj.map (homOfLE hVU).op s = F.right.obj.map (homOfLE hVU).op t) :
    s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.right.property
  intro z hz
  have hb := X.isBasis_affineOpens.of_isInducing i.isClosedEmbedding.isInducing
  obtain ⟨W, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hzW, hWU⟩ :=
    hb.exists_subset_of_mem_open hz U.2
  exact ⟨i ⁻¹ᵁ V, hWU, hzW, h ⟨V, hV⟩ hWU⟩

private theorem linear_comparison_chart (A B : Presentation i)
    (f : A.algebra.toModule ⟶ B.algebra.toModule)
    (hf : ∀ n, A.inclusion n ≫ f = B.inclusion n) (U : X.affineOpens)
    (eA : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
      CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)))
    (heA : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
        eA.hom (homogeneousClass i A.algebra A.inclusion n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩))
    (eB : B.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
      CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)))
    (heB : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
        eB.hom (homogeneousClass i B.algebra B.inclusion n U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
            (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)) :
    ∀ x, f.val.app (op (i ⁻¹ᵁ U.1)) x = eB.inv (eA.hom x) := by
  have hrep (n : ℕ) (a : (power i n).val.obj (op U.1)) :
      f.val.app (op (i ⁻¹ᵁ U.1))
          (homogeneousClass i A.algebra A.inclusion n U.1 a) =
        homogeneousClass i B.algebra B.inclusion n U.1 a :=
    congrArg (fun k ↦ k.val.app (op (i ⁻¹ᵁ U.1)) (representative i n U.1 a)) (hf n)
  intro x
  have hh : ∀ y : Ideal.associatedGraded (i.ker.ideal U),
      f.val.app (op (i ⁻¹ᵁ U.1)) (eA.inv y) = eB.inv y := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        obtain ⟨a, ha⟩ := power_lift i A U n y.val y.property
        obtain ⟨ha', hA⟩ := heA n a
        obtain ⟨hb', hB⟩ := heB n a
        have hA' : eA.inv (DirectSum.of _ n (Submodule.Quotient.mk y)) =
            homogeneousClass i A.algebra A.inclusion n U.1 a := by
          apply ring_iso_inv_eq eA
          exact hA.trans (congrArg (fun t : ↥(i.ker.ideal U ^ n) ↦
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk t)) (Subtype.ext ha))
        have hB' : eB.inv (DirectSum.of _ n (Submodule.Quotient.mk y)) =
            homogeneousClass i B.algebra B.inclusion n U.1 a := by
          apply ring_iso_inv_eq eB
          exact hB.trans (congrArg (fun t : ↥(i.ker.ideal U ^ n) ↦
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk t)) (Subtype.ext ha))
        rw [hA', hB']
        exact hrep n a
    | add a b ha hb => simp only [map_add, ha, hb]
  have hi : eA.inv (eA.hom x) = x := congrArg (fun k ↦ k x) eA.hom_inv_id
  simpa only [hi] using hh (eA.hom x)

private theorem algebra_map_of_affine (A B : Z.CommAlgebraSheaf)
    (f : (A.toModule : Z.Modules) ⟶ (B.toModule : Z.Modules))
    (h : ∀ U : X.affineOpens,
      ∃ g : A.right.obj.obj (op (i ⁻¹ᵁ U.1)) ⟶ B.right.obj.obj (op (i ⁻¹ᵁ U.1)),
        ∀ x, f.val.app (op (i ⁻¹ᵁ U.1)) x = g x) :
    ∃ g : A ⟶ B, ∀ (U : Z.Opens) (x : A.right.obj.obj (op U)),
      g.right.hom.app (op U) x = f.val.app (op U) x := by
  let q (U : Z.Opensᵒᵖ) : A.right.obj.obj U → B.right.obj.obj U := f.val.app U
  have hnat {U V : Z.Opensᵒᵖ} (k : U ⟶ V) (x : A.right.obj.obj U) :
      B.right.obj.map k (q U x) = q V (A.right.obj.map k x) :=
    (congrArg (fun t ↦ t x) (f.val.naturality k)).symm
  have hone (U : Z.Opens) : q (op U) 1 = 1 := by
    apply ambient_affine_section_ext i B U
    intro V hVU
    obtain ⟨g, hg⟩ := h V
    rw [hnat, map_one, map_one]
    exact (hg (1 : A.right.obj.obj (op (i ⁻¹ᵁ V.1)))).trans g.hom.map_one
  have hmul (U : Z.Opens) (x y : A.right.obj.obj (op U)) :
      q (op U) (x * y) = q (op U) x * q (op U) y := by
    apply ambient_affine_section_ext i B U
    intro V hVU
    obtain ⟨g, hg⟩ := h V
    rw [hnat, map_mul, map_mul, hnat, hnat]
    change f.val.app _ _ = (show B.right.obj.obj (op (i ⁻¹ᵁ V.1)) from
      f.val.app _ _) * (show B.right.obj.obj (op (i ⁻¹ᵁ V.1)) from f.val.app _ _)
    rw [hg, hg, hg, map_mul]
  let g : A.right ⟶ B.right :=
    ⟨{ app U := CommRingCat.ofHom
        { toFun := q U
          map_zero' := (f.val.app U).hom.map_zero
          map_one' := hone U.unop
          map_add' := (f.val.app U).hom.map_add
          map_mul' := hmul U.unop }
       naturality {U V} k := by
        apply CommRingCat.hom_ext
        ext x
        exact (hnat k x).symm }⟩
  refine ⟨Under.homMk g ?_, fun _ _ ↦ rfl⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext r
  change q U (A.hom.hom.app U r) = B.hom.hom.app U r
  have hs := (f.val.app U).hom.map_smul r (1 : A.right.obj.obj U)
  change q U (A.hom.hom.app U r * 1) = B.hom.hom.app U r * q U 1 at hs
  simpa only [mul_one, hone] using hs

private def algebra_module_map {A B : Z.CommAlgebraSheaf} (f : A ⟶ B) :
    (A.toModule : Z.Modules) ⟶ (B.toModule : Z.Modules) where
  val :=
    { app U := ModuleCat.ofHom (X := A.toModule.val.obj U)
        (Y := B.toModule.val.obj U)
        { toFun := f.right.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change A.right.obj.obj U at x
            change f.right.hom.app U (A.hom.hom.app U r * x) =
              B.hom.hom.app U r * f.right.hom.app U x
            rw [map_mul]
            congr 1
            exact congrArg (fun k ↦ k.hom.app U r) f.w }
      naturality {U V} k := by
        ext x
        exact congrArg (fun q ↦ q x) (f.right.hom.naturality k) }

omit [IsClosedImmersion i] in
private theorem affineData_quasicoherent (A : AffineData i) :
    A.algebra.toModule.IsQuasicoherent := by
  have : ∀ n, (piece i n).IsQuasicoherent := piece_quasicoherent i
  let F : ULift.{u} ℕ → Z.Modules := fun n ↦ piece i n.down
  have hq := Scheme.Modules.isQuasicoherent_sigma F
  let e := Sigma.reindex (Equiv.ulift : ULift.{u} ℕ ≃ ℕ) (piece i) ≪≫
    (coproductIsCoproduct (piece i)).coconePointUniqueUpToIso A.coproduct
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e hq

omit [IsClosedImmersion i] in
private theorem affineData_induction (A : AffineData i) (U : X.affineOpens)
    (P : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) → Prop)
    (hz : P 0)
    (hrep : ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
      P (homogeneousClass i A.algebra A.inclusion n U.1 a))
    (hadd : ∀ a b, P a → P b → P (a + b)) : ∀ a, P a := by
  obtain ⟨e, he⟩ := A.affineChart U
  have hh (y : Ideal.associatedGraded (i.ker.ideal U)) : P (e.inv y) := by
    induction y using DirectSum.induction_on with
    | zero => simpa only [map_zero] using hz
    | add a b ha hb => simpa only [map_add] using hadd _ _ ha hb
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        have hy : y.val ∈ Set.range ((powerInclusion i n).val.app (op U.1)) := by
          change y.val ∈ Set.range ((Scheme.idealSheafPower i.ker.toModulesι n).2.app U.1)
          rw [power_affine_range i.ker U n]
          exact y.property
        obtain ⟨a, ha⟩ := hy
        obtain ⟨hm, heq⟩ := he n a
        have h : e.inv (DirectSum.of _ n (Submodule.Quotient.mk y)) =
            homogeneousClass i A.algebra A.inclusion n U.1 a := by
          apply ring_iso_inv_eq e
          exact heq.trans (congrArg (fun t : ↥(i.ker.ideal U ^ n) ↦
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk t)) (Subtype.ext ha))
        rw [h]
        exact hrep n a
  intro a
  have hi : e.inv (e.hom a) = a := congrArg (fun k ↦ k a) e.hom_inv_id
  simpa only [hi] using hh (e.hom a)

private theorem addHom_mul_add {R S : Type*}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →+ S) (a b c : R)
    (hb : f (a * b) = f a * f b) (hc : f (a * c) = f a * f c) :
    f (a * (b + c)) = f a * f (b + c) := by
  rw [mul_add, map_add, hb, hc, map_add, mul_add]

private theorem addHom_add_mul {R S : Type*}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →+ S) (a b c : R)
    (ha : f (a * c) = f a * f c) (hb : f (b * c) = f b * f c) :
    f ((a + b) * c) = f (a + b) * f c := by
  rw [add_mul, map_add, ha, hb, map_add, add_mul]

private theorem affineData_augmentation (A : AffineData i) :
    ∃! ε : A.algebra ⟶ Under.mk (𝟙 Z.sheaf),
      ∀ (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)),
        ε.right.hom.app (op (i ⁻¹ᵁ U))
          (homogeneousClass i A.algebra A.inclusion n U a) =
        if n = 0 then i.app U ((powerInclusion i n).val.app (op U) a) else 0 := by
  classical
  let d := Scheme.Modules.tensorPullbackObjUnitToUnit i
  let k : ∀ n, piece i n ⟶ SheafOfModules.unit Z.ringCatSheaf := fun n ↦
    if h : n = 0 then eqToHom (congrArg (piece i) h) ≫ d else 0
  let f := A.coproduct.desc (Cofan.mk _ k)
  have hf (n : ℕ) : A.inclusion n ≫ f = k n := A.coproduct.fac _ ⟨n⟩
  have hd (U : X.Opens) (a : (power i 0).val.obj (op U)) :
      d.val.app (op (i ⁻¹ᵁ U)) (representative i 0 U a) = i.app U a := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t.val.app (op U))
        (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso i).2) a
  let q (U : Z.Opens) : A.algebra.right.obj.obj (op U) →+ Γ(Z, U) :=
    { toFun := f.val.app (op U)
      map_zero' := (f.val.app (op U)).hom.map_zero
      map_add' := (f.val.app (op U)).hom.map_add }
  have hrep (n : ℕ) (U : X.Opens) (a : (power i n).val.obj (op U)) :
      q (i ⁻¹ᵁ U) (homogeneousClass i A.algebra A.inclusion n U a) =
        if n = 0 then i.app U ((powerInclusion i n).val.app (op U) a) else 0 := by
    change (A.inclusion n ≫ f).val.app _ (representative i n U a) = _
    rw [hf]
    by_cases hn : n = 0
    · subst n
      change d.val.app (op (i ⁻¹ᵁ U)) (representative i 0 U a) =
        if (0 : ℕ) = 0 then i.app U a else 0
      rw [ite_eq_left rfl]
      exact hd U a
    · simp only [k, dite_eq_right hn, ite_eq_right hn]
      rfl
  have hone (U : X.affineOpens) : q (i ⁻¹ᵁ U.1) 1 = 1 := by
    have h := A.constants U.1 (1 : Γ(X, U.1))
    have h' : homogeneousClass i A.algebra A.inclusion 0 U.1 (1 : Γ(X, U.1)) = 1 := by
      simpa only [map_one] using h
    rw [← h', hrep]
    change i.app U.1 (1 : Γ(X, U.1)) = 1
    exact (i.app U.1).hom.map_one
  have hmul (U : X.affineOpens) (a b : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1))) :
      q (i ⁻¹ᵁ U.1) (a * b) = q (i ⁻¹ᵁ U.1) a * q (i ⁻¹ᵁ U.1) b := by
    apply affineData_induction i A U (fun a ↦ ∀ b, _ = _) ?_ ?_ ?_ a b
    · intro b
      simp only [zero_mul, map_zero]
    · intro m a
      apply affineData_induction i A U (fun b ↦ _ = _) ?_ ?_ ?_
      · simp only [mul_zero, map_zero]
      · intro n b
        obtain ⟨c, hc⟩ := power_affine_product i.ker m n U a b
        rw [A.multiplication m n U.1 a b c hc, hrep, hrep, hrep]
        by_cases hm : m = 0
        · subst m
          by_cases hn : n = 0
          · subst n
            change i.app U.1 (show Γ(X, U.1) from c) =
              i.app U.1 (show Γ(X, U.1) from a) * i.app U.1 (show Γ(X, U.1) from b)
            have hc' : (show Γ(X, U.1) from c) =
                (show Γ(X, U.1) from a) * (show Γ(X, U.1) from b) := hc
            rw [hc']
            exact (i.app U.1).hom.map_mul _ _
          · simp only [Nat.zero_add, ite_eq_right hn, mul_zero]
        · have hmn : m + n ≠ 0 := by omega
          simp only [ite_eq_right hm, ite_eq_right hmn, zero_mul]
      · intro b c hb hc
        exact addHom_mul_add (q (i ⁻¹ᵁ U.1)) _ b c hb hc
    · intro a c ha hc b
      exact addHom_add_mul (q (i ⁻¹ᵁ U.1)) a c b (ha b) (hc b)
  obtain ⟨ε, hε⟩ := algebra_map_of_affine i A.algebra (Under.mk (𝟙 Z.sheaf)) f (by
    intro U
    let r : A.algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) →+* Γ(Z, i ⁻¹ᵁ U.1) :=
      { toFun := q (i ⁻¹ᵁ U.1)
        map_one' := hone U
        map_mul' := hmul U
        map_zero' := (f.val.app _).hom.map_zero
        map_add' := (f.val.app _).hom.map_add }
    exact ⟨CommRingCat.ofHom r, fun _ ↦ rfl⟩)
  refine ⟨ε, fun n U a ↦ (hε _ _).trans (hrep n U a), ?_⟩
  intro ε' hε'
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  ext a
  apply ambient_affine_section_ext i (Under.mk (𝟙 Z.sheaf)) U.unop
  intro V hVU
  have he (b : A.algebra.right.obj.obj (op (i ⁻¹ᵁ V.1))) :
      ε'.right.hom.app (op (i ⁻¹ᵁ V.1)) b = ε.right.hom.app (op (i ⁻¹ᵁ V.1)) b := by
    apply affineData_induction i A V (fun b ↦ _ = _) ?_ ?_ ?_ b
    · simp only [map_zero]
    · intro n b
      rw [hε', hε]
      exact (hrep n V.1 b).symm
    · intro b c hb hc
      simp only [map_add, hb, hc]
  have hn (g : A.algebra ⟶ Under.mk (𝟙 Z.sheaf)) :=
    ConcreteCategory.congr_hom (g.right.hom.naturality (homOfLE hVU).op) a
  exact (hn ε').symm.trans ((he _).trans (hn ε))

private theorem presentation_comparison (A B : Presentation i) :
    ∃! e : A.algebra ≅ B.algebra,
      ∀ (n : ℕ) (U : Z.Opens) (a : (piece i n).val.obj (op U)),
        e.hom.right.hom.app (op U) ((A.inclusion n).val.app (op U) a) =
          (B.inclusion n).val.app (op U) a := by
  let eM := A.coproduct.coconePointUniqueUpToIso B.coproduct
  have hf (n : ℕ) : A.inclusion n ≫ eM.hom = B.inclusion n :=
    A.coproduct.comp_coconePointUniqueUpToIso_hom B.coproduct ⟨n⟩
  have hg (n : ℕ) : B.inclusion n ≫ eM.inv = A.inclusion n :=
    A.coproduct.comp_coconePointUniqueUpToIso_inv B.coproduct ⟨n⟩
  have hmap (P Q : Presentation i) (f : P.algebra.toModule ⟶ Q.algebra.toModule)
      (hf : ∀ n, P.inclusion n ≫ f = Q.inclusion n) :
      ∃ g : P.algebra ⟶ Q.algebra,
        ∀ (U : Z.Opens) (x : P.algebra.right.obj.obj (op U)),
          g.right.hom.app (op U) x = f.val.app (op U) x := by
    apply algebra_map_of_affine i P.algebra Q.algebra f
    intro U
    obtain ⟨eP, heP⟩ := P.affineChart U
    obtain ⟨eQ, heQ⟩ := Q.affineChart U
    exact ⟨eP.hom ≫ eQ.inv, linear_comparison_chart i P Q f hf U eP heP eQ heQ⟩
  obtain ⟨f, hf'⟩ := hmap A B eM.hom hf
  obtain ⟨g, hg'⟩ := hmap B A eM.inv hg
  have hfg : f ≫ g = 𝟙 A.algebra := by
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    ext x
    change g.right.hom.app U (f.right.hom.app U x) = x
    rw [hg', hf']
    exact congrArg (fun k ↦ k.val.app U x) eM.hom_inv_id
  have hgf : g ≫ f = 𝟙 B.algebra := by
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    ext x
    change f.right.hom.app U (g.right.hom.app U x) = x
    rw [hf', hg']
    exact congrArg (fun k ↦ k.val.app U x) eM.inv_hom_id
  let e : A.algebra ≅ B.algebra := ⟨f, g, hfg, hgf⟩
  refine ⟨e, ?_, ?_⟩
  · intro n U a
    change f.right.hom.app (op U) _ = _
    rw [hf']
    exact congrArg (fun k ↦ k.val.app (op U) a) (hf n)
  · intro e' he'
    have hmod : algebra_module_map e'.hom = eM.hom := by
      apply A.coproduct.hom_ext
      rintro ⟨n⟩
      change A.inclusion n ≫ algebra_module_map e'.hom = A.inclusion n ≫ eM.hom
      rw [hf]
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext a
      exact he' n U.unop a
    apply Iso.ext
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    ext x
    change e'.hom.right.hom.app U x = f.right.hom.app U x
    rw [hf']
    exact congrArg (fun k ↦ k.val.app U x) hmod

/-- The conormal algebra exists, with its unique homogeneous-inclusion-preserving comparison
to any other presentation. This is a universal property, not a mere existence of an
unconstrained algebra or normal-cone datum.
Source: Stacks Divisors Tags 0630--0633; coherent sheaves Tag 01XZ
(blueprint: lem-pur-conormal-graded-algebra).

Proof (the ten steps of `lem-pur-conormal-graded-algebra`):
1. Form the sheaf cokernels B_n = I^n/I^(n+1) on X. Quasi-coherent cokernels and the
   affine tilde adjunction identify B_n on Spec R with the module J^n/J^(n+1), carrying
   quotient representatives to their classes. The shared image-power construction
   identifies with `(i.ker ^ n).toModules` by its inclusion into O_X on affine opens;
   both inclusions have image J^n, so these identifications glue uniquely.
2. Multiply local lifts a and b and take the class of ab. Changing the lifts changes
   this product by an element of J^(m+n+1). These products glue, commute with restriction,
   and satisfy the ring laws on an affine refinement by the associated-graded ring laws.
   Degree-zero constants give the unit. No sectionwise cokernel on arbitrary opens is used.
3. The ideal I annihilates B_n, since a product of an element of J with one of J^n lies
   in J^(n+1). This includes n=0.
4. The closed-immersion annihilation theorem descends B_n to Z, with its pushforward
   identified by the canonical unit; fully faithful pushforward determines this descent.
   On Spec(R/J), the maps a tensor r-bar to ra modulo J^(n+1) and [a] to a tensor 1
   identify the fixed piece i^*(I^n) with that descent. Tensor balancing proves both
   composites are identities. The affine tilde adjunction glues these identifications.
5. The tensor formula transports products to the pieces. Their sheaf coproduct is
   quasi-coherent. On affine opens its sections are the direct sum J^n/J^(n+1), with
   the representative products and constants above. Affine tilde preserves this coproduct;
   no commutation of arbitrary non-affine sections with infinite sums is assumed.
6. Degree one is literally i^*I. On an affine chart, a tensor r-bar maps to ra modulo
   J^2, and the inverse sends [a] to a tensor 1. The tensor relations kill J^2 and prove
   that these are inverse. Degree zero similarly identifies with O_Z.
7. Structure and tilde stalks are localizations. Localization exactness gives
   (J^n/J^(n+1))_p = J_p^n/J_p^(n+1); localization commutes with powers by the fraction
   product formula, also for n=0. Stalks commute with the sheaf coproduct. Thus the stalk
   algebra is gr_(J_p)(R_p), and degree one is its cotangent module. The quotient-stalk
   equivalence is the first-isomorphism equivalence of the actual surjective stalk map.
8. Extend the degree-one inclusion by the symmetric-algebra universal property. On affine
   charts the map sends every generator to its degree-one class. Products of generators
   have the same total degree, so this is the canonical graded comparison.
9. Symmetric-algebra base change along localization identifies the symmetric sheaf stalk
   with the symmetric algebra of the module stalk. The identification fixes scalar germs
   and carries each generator germ to the corresponding generator. In particular it is
   canonical even for a zero module stalk. Naturality and Step 7 give the comparison's
   specified degree-one stalk formula.
10. If X is locally Noetherian, so is Z. Each J^n is finite by the Noetherian submodule
    theorem, and its quotient is finite over R/J. The affine finite-type criterion and
    the coherent/quasi-coherent finite-type equivalence give coherence of each piece.
    No coherence assertion is made about the infinite coproduct.
Finally the coproduct property and representative products determine the algebra up to
its unique homogeneous-inclusion-preserving isomorphism: the unique module comparison
preserves products and constants locally, and the opposite comparison is its inverse.
Projection to degree zero fixes constants and kills positive degrees, hence is the unique
augmentation; nonnegative degrees make it multiplicative. This includes empty schemes,
the zero and unit ideals and n=0. -/
theorem exists_conormalGradedAlgebra :
    ∃ A : Presentation i, ∀ B : Presentation i,
      ∃! e : A.algebra ≅ B.algebra,
        ∀ (n : ℕ) (U : Z.Opens) (a : (piece i n).val.obj (op U)),
          e.hom.right.hom.app (op U) ((A.inclusion n).val.app (op U) a) =
            (B.inclusion n).val.app (op U) a := by
  obtain ⟨A⟩ := exists_affineData i
  let P : Presentation i :=
    { algebra := A.algebra
      inclusion := A.inclusion
      coproduct := A.coproduct
      quasicoherent := affineData_quasicoherent i A
      pieceQuasicoherent := piece_quasicoherent i
      powerIdentification := power_identification i
      multiplication := A.multiplication
      constants := A.constants
      pushforwardPiece := pushforward_piece i
      degreeZero := degree_zero i
      affineChart := A.affineChart
      stalkChart := affineData_stalk_chart i A
      conormalStalk := conormal_stalk i
      symmetricStalk := SymmetricAlgebraSheaf.stalk_iso (piece i 1)
      coherent := by
        intro h n
        have := h
        exact piece_coherent i n
      symmetricComparison := exists_quasiCoherentSymmetricAlgebra_core
        Z (piece i 1) A.algebra (A.inclusion 1)
      augmentation := affineData_augmentation i A }
  exact ⟨P, presentation_comparison i P⟩

/-- The conormal algebra chosen from its universal property. Any two such choices have the
unique isomorphism fixing every homogeneous inclusion, the equality used downstream.
Source: Stacks Tags 0630--0633 (blueprint: lem-pur-conormal-graded-algebra). -/
def presentation : Presentation i := (exists_conormalGradedAlgebra i).choose

/-- The canonical graded algebra map from the symmetric algebra of the conormal module.
Source: Stacks Tag 0632 (blueprint: lem-pur-conormal-graded-algebra). -/
def symmetricComparison : SymmetricAlgebraSheaf.algebra (piece i 1) ⟶
    (presentation i).algebra := (presentation i).symmetricComparison.exists.choose

/-- Projection to degree zero, with its uniquely specified homogeneous representative formula.
Source: Stacks Tags 0630, 0636 (blueprint: lem-pur-conormal-graded-algebra). -/
def augmentation : (presentation i).algebra ⟶ Under.mk (𝟙 Z.sheaf) :=
  (presentation i).augmentation.exists.choose

end AlgebraicGeometry.ConormalGradedAlgebra
