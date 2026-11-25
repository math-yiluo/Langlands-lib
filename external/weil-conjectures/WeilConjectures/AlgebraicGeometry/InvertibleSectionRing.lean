/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The graded section ring of an invertible module

Source: Stacks Project, Tags 01PZ and 01N8
(blueprint: def-sc-invertible-section-ring).

The homogeneous component is literally the global sections of the indicated tensor power.
All operations are specified, and their algebraic laws are proved from tensor-section coherence
and local free generators.

## Main definitions

- `InvertibleSectionRing`: the direct sum of tensor-power sections.
- `sectionRingGCommRing`: tensor multiplication and the degree-zero unit.
- `sectionRingGrade`, `sectionRingGradedRing`: homogeneous components and their grading.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Global sections in degree `n` (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable abbrev SectionRingComponent (L : X.Modules) (n : ℕ) : Type u := Γ(L.tensorPow n, ⊤)

/-- The homogeneous unit is the section `1` of the zeroth tensor power (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGOne (L : X.Modules) :
    GradedMonoid.GOne (SectionRingComponent L) where
  one := unitSectionsEquiv ⊤ 1

/-- Homogeneous multiplication tensors sections, then adds tensor exponents (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGMul (L : X.Modules) :
    GradedMonoid.GMul (SectionRingComponent L) where
  mul {i j} a b := (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b)

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The tensor product with zero is
zero; applying the additive tensor-power isomorphism preserves zero. -/
theorem sectionRing_mul_zero (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a : SectionRingComponent L i) :
    GradedMonoid.GMul.mul a (0 : SectionRingComponent L j) = 0 := by
  change (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a 0) = 0
  rw [tmulSection_zero, map_zero]

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The tensor product with zero is
zero, and the tensor-power isomorphism is additive. -/
theorem sectionRing_zero_mul (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (b : SectionRingComponent L j) :
    GradedMonoid.GMul.mul (0 : SectionRingComponent L i) b = 0 := by
  change (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection 0 b) = 0
  rw [zero_tmulSection, map_zero]

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Distribute the tensor of
sections in its second argument and use additivity of the exponent isomorphism. -/
theorem sectionRing_mul_add (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a : SectionRingComponent L i) (b c : SectionRingComponent L j) :
    GradedMonoid.GMul.mul a (b + c) =
      GradedMonoid.GMul.mul a b + GradedMonoid.GMul.mul a c := by
  change (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a (b + c)) =
    (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b) +
      (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a c)
  rw [tmulSection_add, map_add]

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Distribute the tensor of
sections in its first argument and use additivity of the exponent isomorphism. -/
theorem sectionRing_add_mul (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a b : SectionRingComponent L i) (c : SectionRingComponent L j) :
    GradedMonoid.GMul.mul (a + b) c =
      GradedMonoid.GMul.mul a c + GradedMonoid.GMul.mul b c := by
  change (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection (a + b) c) =
    (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a c) +
      (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection b c)
  rw [add_tmulSection, map_add]

private theorem eqToHom_app_heq {M N : X.Modules} {U : X.Opens} (h : M = N)
    (a : Γ(M, U)) : HEq ((eqToHom h).app U a) a := by
  subst N
  rfl

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The degree-zero section is the
monoidal unit; the left unitor and the exponent isomorphism cancel. -/
theorem sectionRing_one_mul (L : X.Modules) [L.IsInvertible]
    (a : GradedMonoid (SectionRingComponent L)) :
    1 * a = a := by
  obtain ⟨i, a⟩ := a
  apply Sigma.ext (Nat.zero_add i)
  change HEq ((L.tensorPowAddIso 0 i).inv.app ⊤
    (tmulSection (unitSectionsEquiv ⊤ 1) a)) a
  exact (eqToHom_app_heq (congrArg L.tensorPow (Nat.zero_add i).symm) _).trans
    (heq_of_eq ((leftUnitor_hom_app_tmulSection 1 a).trans (one_smul _ _)))

-- The recursive exponent-zero isomorphism agrees with the right unitor.
private theorem tensorPowAddIso_zero_inv (L : X.Modules) (n : ℕ) :
    (L.tensorPowAddIso n 0).inv = (ρ_ (L.tensorPow n)).hom := by
  induction n with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Category.comp_id]
    exact unitors_equal
  | succ n ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      eqToHom_refl, Category.comp_id, tensorIso_inv, Iso.refl_inv, ih]
    simp only [id_tensorHom, rightUnitor_tensor_hom, tensorPow_succ]
    rfl

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The right unitor identifies
tensoring with the section one with the identity; coherence cancels the exponent isomorphism. -/
theorem sectionRing_mul_one (L : X.Modules) [L.IsInvertible]
    (a : GradedMonoid (SectionRingComponent L)) :
    a * 1 = a := by
  obtain ⟨i, a⟩ := a
  apply Sigma.ext (Nat.add_zero i)
  apply heq_of_eq
  change (L.tensorPowAddIso i 0).inv.app ⊤
    (tmulSection a (unitSectionsEquiv ⊤ 1)) = a
  rw [tensorPowAddIso_zero_inv]
  exact (rightUnitor_hom_app_tmulSection 1 a).trans (one_smul _ _)

-- Naturality moves the exponent casts to the end; the induction then uses the pentagon.
private theorem tensorPowAddIso_assoc_inv (L : X.Modules) (i j k : ℕ) :
    (L.tensorPowAddIso i j).inv ▷ L.tensorPow k ≫
      (L.tensorPowAddIso (i + j) k).inv =
    (α_ (L.tensorPow i) (L.tensorPow j) (L.tensorPow k)).hom ≫
      L.tensorPow i ◁ (L.tensorPowAddIso j k).inv ≫
      (L.tensorPowAddIso i (j + k)).inv ≫
      eqToHom (congrArg L.tensorPow (Nat.add_assoc i j k).symm) := by
  induction i with
  | zero =>
    dsimp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
    rw [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k) (Nat.zero_add j).symm]
    simp only [Category.assoc, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal
  | succ i ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorPow_succ, tensorIso_inv, Iso.refl_inv, id_tensorHom]
    rw [comp_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight,
      Category.assoc, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k)
        (Nat.succ_add i j).symm]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, id_tensorHom, Category.assoc, eqToHom_trans]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The associator sends (a tensor
b) tensor c to a tensor (b tensor c). The exponent isomorphisms agree by monoidal coherence,
including the equality of the two degree sums. -/
theorem sectionRing_mul_assoc (L : X.Modules) [L.IsInvertible]
    (a b c : GradedMonoid (SectionRingComponent L)) :
    a * b * c = a * (b * c) := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  apply Sigma.ext (Nat.add_assoc i j k)
  have h := congrArg
    (fun f ↦ f.app ⊤ (tmulSection (tmulSection a b) c))
    (tensorPowAddIso_assoc_inv L i j k)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection,
    whiskerLeft_app_tmulSection, associator_hom_app_tmulSection] at h
  exact (heq_of_eq h).trans (eqToHom_app_heq _ _)

-- Tensor powers of a section over an arbitrary open, without extending it globally.
private noncomputable def tensorPowLocalSection {L : X.Modules} {U : X.Opens}
    (e : Γ(L, U)) : (n : ℕ) → Γ(L.tensorPow n, U)
  | 0 => unitSectionsEquiv U 1
  | n + 1 => tmulSection e (tensorPowLocalSection e n)

private theorem tensorPowLocalSection_transport {L : X.Modules} {U : X.Opens}
    (e : Γ(L, U)) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg L.tensorPow h)).app U (tensorPowLocalSection e m) =
      tensorPowLocalSection e n := by
  subst n
  rfl

private theorem tensorPowLocalSection_mul {L : X.Modules} {U : X.Opens}
    (e : Γ(L, U)) (i j : ℕ) :
    (L.tensorPowAddIso i j).inv.app U
      (tmulSection (tensorPowLocalSection e i) (tensorPowLocalSection e j)) =
        tensorPowLocalSection e (i + j) := by
  induction i with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection 1 _).trans (one_smul _ _))).trans
      (tensorPowLocalSection_transport e (Nat.zero_add j).symm)
  | succ i ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change (eqToHom (congrArg L.tensorPow (Nat.succ_add i j).symm)).app U
      ((Iso.refl L ⊗ᵢ L.tensorPowAddIso i j).inv.app U
      ((α_ L (L.tensorPow i) (L.tensorPow j)).hom.app U
        (tmulSection (tmulSection e (tensorPowLocalSection e i))
          (tensorPowLocalSection e j)))) = _
    rw [associator_hom_app_tmulSection]
    have h : (Iso.refl L ⊗ᵢ L.tensorPowAddIso i j).inv.app U
        (tmulSection e (tmulSection (tensorPowLocalSection e i)
          (tensorPowLocalSection e j))) = tmulSection e (tensorPowLocalSection e (i + j)) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    rw [h]
    exact tensorPowLocalSection_transport e (Nat.succ_add i j).symm

private theorem tensorPowLocalSection_generator {L : X.Modules} {U : X.Opens}
    {e : Γ(L, U)} (he : IsFreeGenerator e) (n : ℕ) :
    IsFreeGenerator (tensorPowLocalSection e n) := by
  induction n with
  | zero => exact isFreeGenerator_one U
  | succ n ih => exact he.tmulSection ih

private theorem tensorPowLocalSection_comm {L : X.Modules} {U : X.Opens}
    {e : Γ(L, U)} (he : IsFreeGenerator e) (i j : ℕ)
    (a : Γ(L.tensorPow i, U)) (b : Γ(L.tensorPow j, U)) :
    (L.tensorPowAddIso i j).inv.app U (tmulSection a b) =
      (eqToHom (congrArg L.tensorPow (Nat.add_comm j i))).app U
        ((L.tensorPowAddIso j i).inv.app U (tmulSection b a)) := by
  obtain ⟨f, rfl⟩ := (tensorPowLocalSection_generator he i).exists_smul_eq a
  obtain ⟨g, rfl⟩ := (tensorPowLocalSection_generator he j).exists_smul_eq b
  rw [smul_tmulSection, tmulSection_smul, smul_tmulSection, tmulSection_smul]
  simp only [Hom.app_smul, tensorPowLocalSection_mul, smul_smul]
  rw [mul_comm]
  exact congrArg (fun z ↦ (g * f) • z)
    (tensorPowLocalSection_transport e (Nat.add_comm j i)).symm

-- Convert the scheme-module trivialization to a trivialization over the restricted site.
private theorem exists_localGenerator (L : X.Modules) [L.IsInvertible] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ e : Γ(L, U), IsFreeGenerator e := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := L) x
  let e' := (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app L ≪≫ (restrictFunctorIsoPullback U.ι).app L ≪≫ e ≪≫
      overEquivFunctorObjUnitIso U)
  obtain ⟨s, hs⟩ := exists_isFreeGenerator_of_iso e'
  exact ⟨U, hx, s, hs⟩

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Locally trivialize the
invertible module. Both products then multiply the same two functions in the commutative structure
sheaf, times the same tensor power of the chosen generator. These equalities glue; commutation of
the degree sum supplies the dependent equality. -/
theorem sectionRing_mul_comm (L : X.Modules) [L.IsInvertible]
    (a b : GradedMonoid (SectionRingComponent L)) :
    a * b = b * a := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  apply Sigma.ext (Nat.add_comm i j)
  let S : Sieve (⊤ : X.Opens) := {
    arrows U _ := ∃ e : Γ(L, U), IsFreeGenerator e
    downward_closed := fun ⟨e, he⟩ g ↦ ⟨_, he.map (leOfHom g)⟩ }
  have hS : S ∈ Opens.grothendieckTopology X ⊤ := by
    intro x _
    obtain ⟨U, hx, e, he⟩ := exists_localGenerator L x
    exact ⟨U, homOfLE le_top, ⟨e, he⟩, hx⟩
  have h : (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b) =
      (eqToHom (congrArg L.tensorPow (Nat.add_comm j i))).app ⊤
        ((L.tensorPowAddIso j i).inv.app ⊤ (tmulSection b a)) := by
    refine ((L.tensorPow (i + j)).isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
      fun U f ⟨e, he⟩ ↦ ?_
    change (L.tensorPow (i + j)).presheaf.map f.op
      ((L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b)) =
        (L.tensorPow (i + j)).presheaf.map f.op
          ((eqToHom (congrArg L.tensorPow (Nat.add_comm j i))).app ⊤
            ((L.tensorPowAddIso j i).inv.app ⊤ (tmulSection b a)))
    have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
    rw [hf]
    simp only [← Hom.app_presheaf_map, tmulSection_map]
    exact tensorPowLocalSection_comm he i j _ _
  exact (heq_of_eq h).trans (eqToHom_app_heq _ _)

/-- The graded commutative ring laws on tensor-power sections (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). All operations are explicit; the law fields
refer to the preceding named theorems and the additive-group cast identities. -/
noncomputable instance sectionRingGCommRing (L : X.Modules) [L.IsInvertible] :
    DirectSum.GCommRing (SectionRingComponent L) where
  mul_zero := sectionRing_mul_zero L
  zero_mul := sectionRing_zero_mul L
  mul_add := sectionRing_mul_add L
  add_mul := sectionRing_add_mul L
  one_mul := sectionRing_one_mul L
  mul_one := sectionRing_mul_one L
  mul_assoc := sectionRing_mul_assoc L
  mul_comm := sectionRing_mul_comm L
  natCast n := n • (GradedMonoid.GOne.one : SectionRingComponent L 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast z := z • (GradedMonoid.GOne.one : SectionRingComponent L 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- The section ring `⨁ n, Γ(X, L^{⊗ n})` (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable abbrev InvertibleSectionRing (L : X.Modules) :=
  ⨁ n : ℕ, SectionRingComponent L n

/-- The homogeneous component inside the section ring (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable def sectionRingGrade (L : X.Modules) (n : ℕ) :
    AddSubgroup (InvertibleSectionRing L) :=
  (DirectSum.of (SectionRingComponent L) n).range

/-- The homogeneous components form a multiplicative grading (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). The unit is in degree zero by construction.
The product of two single-component sums is the single-component sum of their tensor product,
so its degree is the sum of the two degrees. -/
theorem sectionRing_gradedMonoid (L : X.Modules) [L.IsInvertible] :
    SetLike.GradedMonoid (sectionRingGrade L) := by
  refine { one_mem := ?_, mul_mem := ?_ }
  · exact ⟨GradedMonoid.GOne.one, rfl⟩
  · intro i j a b ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨GradedMonoid.GMul.mul a b, (DirectSum.of_mul_of a b).symm⟩

/-- The section ring is the internal direct sum of its homogeneous components (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). Every finitely supported section family is the
sum of its single-component families. Evaluation in each degree shows this expression is
unique. Thus the canonical recomposition map is bijective. -/
theorem sectionRing_isInternal (L : X.Modules) :
    DirectSum.IsInternal (sectionRingGrade L) := by
  let f := DirectSum.map (fun n ↦ (DirectSum.of (SectionRingComponent L) n).rangeRestrict)
  have hf : Function.Bijective f := by
    constructor
    · exact (DirectSum.map_injective _).2 fun n ↦
        AddMonoidHom.rangeRestrict_injective_iff.mpr (DirectSum.of_injective n)
    · exact (DirectSum.map_surjective _).2 fun n ↦
        AddMonoidHom.rangeRestrict_surjective _
  have hcomp : (DirectSum.coeAddMonoidHom (sectionRingGrade L)).comp f =
      AddMonoidHom.id (InvertibleSectionRing L) := by
    ext n a
    simp [f, sectionRingGrade, DirectSum.coeAddMonoidHom]
  have h (a : InvertibleSectionRing L) :
      DirectSum.coeAddMonoidHom (sectionRingGrade L) (f a) = a :=
    DFunLike.congr_fun hcomp a
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := hf.2 a
    obtain ⟨b, rfl⟩ := hf.2 b
    exact congrArg f (by simpa only [h] using hab)
  · intro a
    exact ⟨f a, h a⟩

/-- The grading on the section ring, using the inverse of the bijective recomposition map
(Stacks, Tag 01PZ; (blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGradedRing (L : X.Modules) [L.IsInvertible] :
    GradedRing (sectionRingGrade L) :=
  { sectionRing_gradedMonoid L,
    (sectionRing_isInternal L).chooseDecomposition with }

end AlgebraicGeometry.Scheme.Modules
