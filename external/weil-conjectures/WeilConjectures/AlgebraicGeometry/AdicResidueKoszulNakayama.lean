/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.Algebra.Homology.FiniteKoszulResidueAcyclic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector

/-! # Residue-zero detection independent of quotient reconstruction

Source: Stacks Project, more-algebra.tex, Tag 0G1U; algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
open scoped ZeroObject
namespace AdicKoszulNakayamaProof

universe w
variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}

private theorem kernel_generating_list
    {R S : Sheaf T CommRingCat.{w}} (q : R ⟶ S) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (hker : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    ∀ U : C, IsRingedIdealGeneratingList R (kernelIdeal q).module
      (kernelIdeal q).inclusion U r (fun i ↦ (b i).val (op U)) := by
  intro U
  let K := ConstantCompletion.overIdeal (kernelIdeal q) U
  let bs (i : Fin r) : ((R.over U).obj ⋙ forget CommRingCat).sections :=
    ⟨fun V ↦ (b i).val (op V.unop.left), fun f ↦ (b i).property f.unop.left.op⟩
  have hs (V : Over U) : K.sections V =
      Ideal.span (Set.range (fun i ↦ (bs i).val (op V))) := by
    exact ((kernelIdeal_existsUnique q).exists.choose_spec V.left).trans (hker V.left)
  obtain ⟨σ, e, he⟩ := ConstantCompletion.ideal_generated_global_sections
    (R.over U) K r bs hs
  exact ⟨σ, e, fun i ↦ congrArg
    (fun s ↦ s.val (op (Over.mk (𝟙 U)))) (he i)⟩

private theorem tensor_tower_acyclic
    (R : Sheaf T CommRingCat.{w}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (P : ringedSiteComplex R)
    (h : ∀ n : ℕ, (((ringedKoszulTensor R).obj P).obj
      ((ringedKoszulDualTower R r b).obj (op n))).Acyclic) :
    (ringedKoszulTensorTowerComplex R r b P).Acyclic := by
  let F := fun n : ℕᵒᵖ ↦ (evaluation ℕᵒᵖ (Mod R)).obj n
  have hf : JointlyReflectIsomorphisms F :=
    ⟨fun f h ↦ by
      have : ∀ n, IsIso (f.app n) := h
      exact NatIso.isIso_of_isIso_app f⟩
  intro i
  apply (hf.exactAt_iff _ i).2
  intro n
  let e : (((F n).mapHomologicalComplex (.up ℤ)).obj
      (ringedKoszulTensorTowerComplex R r b P)) ≅
      (((ringedKoszulTensor R).obj P).obj
        ((ringedKoszulDualTower R r b).obj n)) :=
    HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
      intro j k hjk
      have hk : j + 1 = k := hjk
      subst k
      simp only [F, ringedKoszulTensorTowerComplex, CochainComplex.of_d,
        Functor.mapHomologicalComplex_obj_d]
      rfl)
  exact ((h n.unop).of_iso e.symm) i

private theorem inverseLimit_isZero
    (R : Sheaf T CommRingCat.{w})
    [HasDerivedCategory (Mod R)] [HasDerivedCategory (ℕᵒᵖ ⥤ Mod R)]
    (r : ℕ) (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (D : RingedKoszulLimitPresentation R r b)
    (Z : DerivedCategory (ℕᵒᵖ ⥤ Mod R)) (hZ : IsZero Z) :
    IsZero (D.inverseLimit.obj Z) := by
  let L := (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R)
  have : L.PreservesZeroMorphisms := by
    constructor
    intro X Y
    apply limit.hom_ext
    intro n
    simp only [L, lim_map, limMap_π, NatTrans.app_zero, comp_zero, zero_comp]
  have hk : CochainComplex.IsKInjective (0 : CochainComplex (ℕᵒᵖ ⥤ Mod R) ℤ) := by
    constructor
    intro K f _
    exact ⟨Homotopy.ofEq ((isZero_zero _).eq_of_tgt f 0)⟩
  have := D.comparison_isIso 0 hk
  have hz : IsZero ((DerivedCategory.Q : CochainComplex (ℕᵒᵖ ⥤ Mod R) ℤ ⥤ _).obj 0) :=
    DerivedCategory.Q.map_isZero (isZero_zero _)
  have hlim : IsZero (D.inverseLimit.obj (DerivedCategory.Q.obj 0)) :=
    (DerivedCategory.Q.map_isZero
      ((L.mapHomologicalComplex (.up ℤ)).map_isZero (isZero_zero _))).of_iso
        (asIso (D.comparison.app 0)).symm
  exact hlim.of_iso (D.inverseLimit.mapIso (hZ.iso hz))

private theorem complete_zero
    {R S : Sheaf T CommRingCat.{w}} (q : R ⟶ S) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (hq : ∀ U : C, Function.Surjective (q.hom.app (op U)))
    (hker : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U))))
    (M : ConstantCompletion.D R) (hM : IsComplete q M)
    (h₀ : IsZero ((extend q).obj M)) : IsZero M := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  let (U : C) := HasDerivedCategory.standard (Mod (R.over U))
  have : Mono (kernelIdeal q).inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app V z) h
  obtain ⟨D, _, _, hi, _⟩ := ringedKoszulCompletionReflector R r b
    (kernelIdeal q).module (kernelIdeal q).inclusion (kernel_generating_list q r b hker)
  have := (hi M).2 hM
  let P := (ConstantCompletion.Q R).objPreimage M
  let e := (ConstantCompletion.Q R).objObjPreimageIso M
  have hP := h₀.of_iso ((extend q).mapIso e)
  have hstage := finiteKoszulTensor_acyclic_of_residue q r b hq hker P hP
  have hcx := tensor_tower_acyclic R r b P hstage
  have hz : IsZero (DerivedCategory.Q.obj (ringedKoszulTensorTowerComplex R r b P)) :=
    (DerivedCategory.isZero_Q_obj_iff _).2 hcx
  have ht : IsZero (D.tensorTower.obj M) :=
    (hz.of_iso (D.tensorFactors.app P)).of_iso (D.tensorTower.mapIso e).symm
  exact (inverseLimit_isZero R r b D _ ht).of_iso (asIso (D.unit M))

end AdicKoszulNakayamaProof

namespace AlgebraicGeometry.Scheme

/-- A locally complete complex with zero residue extension is zero.

Source: Stacks Project, more-algebra.tex, Tag 0G1U, lemma-derived-complete-zero-bis,
and Tag 0G1T, lemma-derived-vanishing-mod-I; algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).

Proof: choose finitely many generators of J, whose completed sections generate the
actual residue kernel on every slice by flat_and_quotients. The Koszul reflector
formula represents a complete Q as the total derived inverse limit of the finite
negative Koszul complexes tensored with Q. The homology sheaves of the Koszul
complex at power m+1 are annihilated by a power of the residue ideal, since each
generator to that power acts nullhomotopically. A module annihilated by the residue
ideal has zero derived tensor with Q: scalar balancing identifies it with tensor
of the zero residue extension of Q over the residue coefficient sheaf. Filter a
module annihilated by a higher power by powers of the ideal and use its short
exact sequences to obtain the same vanishing. The bounded Postnikov filtration
of each finite Koszul complex therefore makes its derived tensor with Q zero.
Consequently the strict Koszul tensor tower has zero image in its derived
category: evaluation is exact and jointly detects acyclic complexes. Its total
derived inverse limit is zero. The Koszul unit is invertible because Q is locally
complete, so Q is zero. This proof uses the Koszul reflector, not reconstruction
from the quotient tower or a mapping property of its unit. For the empty list the
Koszul complex is the ring and the residue extension is the identity. For J=A the
unit ideal contains one, so completeness itself forces Q to vanish. The zero ring
and arbitrary unbounded Q are included. -/
theorem adicResidue_isZero_of_complete_residue
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (Q : AdicResidueLocalDerived.{u, v} X J U)
    (hQ : IsComplete (adicResidueLocalProjection.{u, v} X J U 0) Q)
    (h₀ : IsZero ((adicResidueLocalReduction.{u, v} X J U 0).obj Q)) :
    IsZero Q := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := (completed T A J).over U
  let q := adicResidueLocalProjection.{u, v} X J U 0
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  let b (i : Fin r) : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections :=
    ⟨fun V ↦ (algebraSection (coefficientMap T A J) (a i)).val (op V.unop.left),
      fun f ↦ (algebraSection (coefficientMap T A J) (a i)).property f.unop.left.op⟩
  have hq (V : Over U) : Function.Surjective (q.hom.app (op V)) :=
    ((flat_and_quotients T A J).2.1 0 V.left).1
  have hker (V : Over U) : RingHom.ker (q.hom.app (op V)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op V))) := by
    rw [show RingHom.ker (q.hom.app (op V)).hom =
      RingHom.ker ((projection T A J 0).hom.app (op V.left)).hom from rfl,
      ((flat_and_quotients T A J).2.1 0 V.left).2]
    let f : A →+* (completed T A J).obj.obj (op V.left) :=
      (coefficientMap T A J).hom.app (op V.left) |>.hom.comp
        ((toSheafify T ((Functor.const _).obj (CommRingCat.of A))).app (op V.left)).hom
    exact ConstantCompletion.span_subtype_images f (J ^ (0 + 1)) a
      (by simpa only [Nat.zero_add, pow_one] using ha)
  exact AdicKoszulNakayamaProof.complete_zero q r b hq hker Q hQ h₀

end AlgebraicGeometry.Scheme
