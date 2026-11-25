/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # The explicit action on the nonnegative twisted section direct sum

Source: Stacks Project, Lemma 01YS(5), construction of the section module.
(blueprint: lem-sc-p1-section-action-laws). -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]
variable (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)

/-- The degree `z` group is the section group when `z ≥ 0`, and the zero group otherwise.
Using functions out of the proposition makes negative degrees empty products. -/
abbrev serreSectionPiece (z : ℤ) :=
  PLift (0 ≤ z) → Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)

/-- Each degree piece `serreSectionPiece k G z` is an additive commutative group, being a
group of functions into the section group of `G ⊗ O(z)`. -/
noncomputable instance serreSectionPieceAddCommGroup (z : ℤ) :
    AddCommGroup (serreSectionPiece k G z) := by
  unfold serreSectionPiece
  infer_instance

/-- The explicit additive direct sum of the nonnegative section groups. -/
abbrev serreSectionSum := DirectSum ℤ (serreSectionPiece k G)

/-- The effect of a homogeneous scalar on a single degree, extended by zero in negative
source degrees. -/
noncomputable def serreSectionHomogeneous (e : ℕ) (z : ℤ)
    (a : MvPolynomial.homogeneousSubmodule (Fin 2) k e) (s : serreSectionPiece k G z) :
    serreSectionPiece k G (z + e) :=
  fun _ ↦ if hz : 0 ≤ z then Scheme.Modules.Hom.app (G ◁ Proj.twistMul z a.property) ⊤
    (s ⟨hz⟩) else 0

/-- Scalar multiplication, explicitly summing the finitely many homogeneous polynomial
components and the finitely many section components. -/
noncomputable def serreSectionSMul (a : MvPolynomial (Fin 2) k) (x : serreSectionSum k G) :
    serreSectionSum k G := by
  classical
  exact ∑ e ∈ (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a).support,
    ∑ z ∈ x.support, DirectSum.of (serreSectionPiece k G) (z + e)
      (serreSectionHomogeneous k G e z
        (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a e) (x z))

/-- The scalar operation on the explicitly constructed additive direct sum. -/
noncomputable instance serreSectionSumSMul :
    SMul (MvPolynomial (Fin 2) k) (serreSectionSum k G) := ⟨serreSectionSMul k G⟩

private theorem twist_cast_val {i j : ℤ} (h : i = j)
    (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
    (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) i, U)) (x : U) :
    ((Scheme.Modules.Hom.app (eqToHom
      (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)) U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = s.1 x := by
  subst j
  rfl

private theorem sections_cast_heq
    {M N : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules}
    (h : M = N) (s : Γ(M, ⊤)) :
    HEq (Scheme.Modules.Hom.app (eqToHom h) ⊤ s) s := by
  subst N
  rfl

/-- Multiplication by the homogeneous unit acts identically on twisted sections.

Source: Stacks Project, Definition 01MN and Lemma 01M7.
Proof: the twist multiplication morphism sends a local homogeneous fraction r to r * (1/1),
which equals r. After identifying z+0 with z, it is the identity morphism of the twist.
Tensoring this identity with G gives the identity of G tensor the twist. Evaluation at the
whole space preserves identity morphisms, so its value on every section is the same section.
The heterogeneous equality records only the degree identification; it adds no hypothesis. -/
private theorem serreTwistedSectionsUnit (z : ℤ)
    (s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)) :
    HEq (Scheme.Modules.Hom.app (G ◁ Proj.twistMul z
      (SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k))) ⊤ s) s := by
  let h : z + ((0 : ℕ) : ℤ) = z := by omega
  let c := eqToHom (congrArg
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)
  have hm : Proj.twistMul z
      (SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫ c =
      𝟙 (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z) := by
    ext U t : 3
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    change ((Scheme.Modules.Hom.app c U
      (Scheme.Modules.Hom.app (Proj.twistMul z
        (SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k))) U t)).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = t.1 x
    rw [twist_cast_val k h]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk 1 1 =
        (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    rw [Localization.mk_one_eq_algebraMap, map_one, mul_one]
  have hc : G ◁ c = eqToHom (congrArg
      (fun n ↦ G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) h) := by
    exact whiskerLeft_eqToHom G _
  have hm' : G ◁ Proj.twistMul z
      (SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k)) ≫ G ◁ c =
      𝟙 (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z) := by
    rw [← whiskerLeft_comp, hm, whiskerLeft_id]
  have hs := congrArg (fun f ↦ Scheme.Modules.Hom.app f ⊤ s) hm'
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at hs
  rw [hc] at hs
  exact (sections_cast_heq k _ _).symm.trans (heq_of_eq hs)


/-- Two successive homogeneous multiplications act by the product on twisted sections.

Source: Stacks Project, Definition 01MN and Lemma 01M7.
Proof: over every open set and at every point, twist multiplication sends r to r*(a/1).
First multiplying by b and then by a gives (r*(b/1))*(a/1)=r*((a*b)/1), by associativity,
commutativity, and multiplicativity of localization. The degree identity
(z+f)+e=z+(e+f) identifies the codomains. These pointwise identities give equality of
morphisms of twists after transport. The tensor-left functor preserves compositions and
that equality. Evaluation at the whole space also preserves composition, so evaluating
on a section gives the stated heterogeneous equality. This holds for zero scalars and
arbitrary integer source degree as well. -/
private theorem serreTwistedSectionsMul (e f : ℕ) (z : ℤ)
    (a b : MvPolynomial (Fin 2) k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k f)
    (s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤)) :
    HEq (Scheme.Modules.Hom.app
      (G ◁ Proj.twistMul z (SetLike.GradedMul.mul_mem ha hb)) ⊤ s)
      (Scheme.Modules.Hom.app (G ◁ Proj.twistMul (z + f) ha) ⊤
        (Scheme.Modules.Hom.app (G ◁ Proj.twistMul z hb) ⊤ s)) := by
  let h : z + ((e + f : ℕ) : ℤ) = (z + f) + e := by omega
  let c := eqToHom (congrArg
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)
  have hm : Proj.twistMul z (SetLike.GradedMul.mul_mem ha hb) ≫ c =
      Proj.twistMul z hb ≫ Proj.twistMul (z + f) ha := by
    ext U t : 3
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    change ((Scheme.Modules.Hom.app c U
      (Scheme.Modules.Hom.app (Proj.twistMul z (SetLike.GradedMul.mul_mem ha hb)) U t)).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    rw [twist_cast_val k h]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (a * b) 1 =
        ((t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk b 1) * Localization.mk a 1
    simp only [Localization.mk_one_eq_algebraMap, map_mul]
    ring
  have hc : G ◁ c = eqToHom (congrArg
      (fun n ↦ G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) h) := by
    exact whiskerLeft_eqToHom G _
  have hm' := congrArg (fun φ ↦ G ◁ φ) hm
  rw [whiskerLeft_comp, whiskerLeft_comp] at hm'
  have hs := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ ⊤ s) hm'
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hs
  rw [hc] at hs
  exact (sections_cast_heq k _ _).symm.trans (heq_of_eq hs)


private theorem homogeneous_zero_section (e : ℕ) (z : ℤ)
    (a : MvPolynomial.homogeneousSubmodule (Fin 2) k e) :
    serreSectionHomogeneous k G e z a 0 = 0 := by
  ext h
  simp [serreSectionHomogeneous]

private theorem twistMul_zero (e : ℕ) (z : ℤ) :
    Proj.twistMul (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k) z
      (show (0 : MvPolynomial (Fin 2) k) ∈
        MvPolynomial.homogeneousSubmodule (Fin 2) k e from zero_mem _) = 0 := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
    Localization.mk 0 1 = 0
  rw [Localization.mk_zero, mul_zero]

private theorem tensorLeft_additive : (tensorLeft G).Additive := by
  let : MonoidalClosed
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules :=
    SheafOfModules.monoidalClosed
        (R := (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).sheaf)
  have : Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft G) :=
    (ihom.adjunction G).leftAdjoint_preservesColimits
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft G)
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem homogeneous_zero_scalar (e : ℕ) (z : ℤ)
    (s : serreSectionPiece k G z) :
    serreSectionHomogeneous k G e z 0 s = 0 := by
  ext h
  have := tensorLeft_additive k G
  have hz : G ◁ (0 : Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z ⟶
      Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z + e)) = 0 :=
    (tensorLeft G).map_zero _ _
  simp [serreSectionHomogeneous, twistMul_zero, hz]

private theorem homogeneous_add_section (e : ℕ) (z : ℤ)
    (a : MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (s t : serreSectionPiece k G z) :
    serreSectionHomogeneous k G e z a (s + t) =
      serreSectionHomogeneous k G e z a s + serreSectionHomogeneous k G e z a t := by
  ext h
  by_cases hz : 0 ≤ z <;> simp [serreSectionHomogeneous, hz]

private theorem twistMul_add (e : ℕ) (z : ℤ)
    (a b : MvPolynomial.homogeneousSubmodule (Fin 2) k e) :
    Proj.twistMul z (a + b).property = Proj.twistMul z a.property +
      Proj.twistMul z b.property := by
  ext U s : 3
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk ((a + b).val) 1 =
    (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk a.val 1 +
      (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk b.val 1
  simp only [AddMemClass.coe_add]
  rw [← Localization.add_mk_self, mul_add]

private theorem homogeneous_add_scalar (e : ℕ) (z : ℤ)
    (a b : MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (s : serreSectionPiece k G z) :
    serreSectionHomogeneous k G e z (a + b) s =
      serreSectionHomogeneous k G e z a s + serreSectionHomogeneous k G e z b s := by
  have := tensorLeft_additive k G
  have hab : G ◁ (Proj.twistMul z a.property + Proj.twistMul z b.property) =
      G ◁ Proj.twistMul z a.property + G ◁ Proj.twistMul z b.property :=
    (tensorLeft G).map_add
  ext h
  by_cases hz : 0 ≤ z <;> simp [serreSectionHomogeneous, hz, twistMul_add, hab]

private noncomputable def homogeneousHom (e : ℕ) (z : ℤ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k e →+
      (serreSectionPiece k G z →+ serreSectionSum k G) where
  toFun a :=
    { toFun := fun s ↦ DirectSum.of _ (z + e) (serreSectionHomogeneous k G e z a s)
      map_zero' := by simp [homogeneous_zero_section]
      map_add' := by intros; simp [homogeneous_add_section] }
  map_zero' := by ext s; simp [homogeneous_zero_scalar]
  map_add' a b := by ext s; simp [homogeneous_add_scalar]

private noncomputable def actionHom :
    MvPolynomial (Fin 2) k →+ (serreSectionSum k G →+ serreSectionSum k G) :=
  (DFinsupp.sumAddHom (fun e ↦
    { toFun := fun a ↦ DFinsupp.sumAddHom (fun z ↦ homogeneousHom k G e z a)
      map_zero' := by simp [map_zero, DFinsupp.sumAddHom_zero]
      map_add' := by intros; simp [map_add, DFinsupp.sumAddHom_add] })).comp
    (DirectSum.decomposeAddEquiv (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toAddMonoidHom

private theorem actionHom_apply (a : MvPolynomial (Fin 2) k) (x : serreSectionSum k G) :
    actionHom k G a x = a • x := by
  classical
  change ((DFinsupp.sumAddHom (fun e ↦
    (show MvPolynomial.homogeneousSubmodule (Fin 2) k e →+
      (serreSectionSum k G →+ serreSectionSum k G) from _)))
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a)) x = _
  rw [DFinsupp.sumAddHom_apply]
  simp only [DFinsupp.sum, AddMonoidHom.finsetSum_apply]
  change (∑ e ∈ (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a).support,
    (DFinsupp.sumAddHom (fun z ↦ homogeneousHom k G e z
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) k) a e))) x) = _
  simp only [DFinsupp.sumAddHom_apply, DFinsupp.sum]
  rfl

private theorem homogeneous_single (e : ℕ) (z : ℤ)
    (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (s : serreSectionPiece k G z) :
    a • DirectSum.of (serreSectionPiece k G) z s =
      DirectSum.of (serreSectionPiece k G) (z + e)
        (serreSectionHomogeneous k G e z ⟨a, ha⟩ s) := by
  classical
  change serreSectionSMul k G a (DirectSum.of _ z s) = _
  unfold serreSectionSMul
  rw [DirectSum.decompose_of_mem _ ha]
  change DFinsupp.sum (DFinsupp.single e ⟨a, ha⟩)
    (fun e a ↦ DFinsupp.sum (DFinsupp.single z s)
      (fun z s ↦ DirectSum.of _ (z + e) (serreSectionHomogeneous k G e z a s))) = _
  rw [DFinsupp.sum_single_index]
  · rw [DFinsupp.sum_single_index]
    simp [homogeneous_zero_section]
  · simp [DFinsupp.sum, homogeneous_zero_scalar]

private theorem smul_add_law (a : MvPolynomial (Fin 2) k) (x y : serreSectionSum k G) :
    a • (x + y) = a • x + a • y := by
  simp only [← actionHom_apply, map_add]

private theorem add_smul_law (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G) :
    (a + b) • x = a • x + b • x := by
  simp only [← actionHom_apply, map_add, AddMonoidHom.add_apply]

private theorem smul_zero_law (a : MvPolynomial (Fin 2) k) :
    a • (0 : serreSectionSum k G) = 0 := by
  simp only [← actionHom_apply, map_zero]

private theorem zero_smul_law (x : serreSectionSum k G) :
    (0 : MvPolynomial (Fin 2) k) • x = 0 := by
  simp only [← actionHom_apply, map_zero, AddMonoidHom.zero_apply]

private theorem piece_heq {z w : ℤ} (h : z = w)
    (s : serreSectionPiece k G z) (t : serreSectionPiece k G w)
    (hs : ∀ (hz : PLift (0 ≤ z)) (hw : PLift (0 ≤ w)), HEq (s hz) (t hw)) :
    HEq s t := by
  subst w
  apply heq_of_eq
  funext hz
  exact eq_of_heq (hs hz hz)

private theorem homogeneous_unit (z : ℤ) (s : serreSectionPiece k G z) :
    HEq (serreSectionHomogeneous k G 0 z
      ⟨1, SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k)⟩ s) s := by
  apply piece_heq k G (by omega)
  intro hz hw
  have h : 0 ≤ z := hw.down
  simp only [serreSectionHomogeneous, dite_eq_left h]
  exact serreTwistedSectionsUnit k G z (s ⟨h⟩)

private theorem section_zero_heq {z w : ℤ} (h : z = w) :
    HEq (0 : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤))
      (0 : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) w, ⊤)) := by
  subst w
  rfl

private theorem homogeneous_mul (e f : ℕ) (z : ℤ)
    (a b : MvPolynomial (Fin 2) k)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
    (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k f)
    (s : serreSectionPiece k G z) :
    HEq (serreSectionHomogeneous k G (e + f) z
      ⟨a * b, SetLike.GradedMul.mul_mem ha hb⟩ s)
      (serreSectionHomogeneous k G e (z + f) ⟨a, ha⟩
        (serreSectionHomogeneous k G f z ⟨b, hb⟩ s)) := by
  apply piece_heq k G (by omega)
  intro hz hw
  by_cases h : 0 ≤ z
  · have hf : 0 ≤ z + f := by omega
    simp only [serreSectionHomogeneous, dite_eq_left h, dite_eq_left hf]
    exact serreTwistedSectionsMul k G e f z a b ha hb (s ⟨h⟩)
  · simp only [serreSectionHomogeneous, dite_eq_right h]
    split_ifs <;> (try simp only [map_zero]) <;>
      exact section_zero_heq k G (by omega)

private theorem one_smul_law (x : serreSectionSum k G) :
    (1 : MvPolynomial (Fin 2) k) • x = x := by
  induction x using DirectSum.induction_on with
  | zero => exact smul_zero_law k G 1
  | of z s =>
    rw [homogeneous_single k G 0 z 1
      (SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin 2) k))]
    exact (DFinsupp.single_eq_single_iff _ _ _ _).mpr
      (Or.inl ⟨by omega, homogeneous_unit k G z s⟩)
  | add x y hx hy => rw [smul_add_law, hx, hy]

private theorem mul_smul_law (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G) :
    (a * b) • x = a • (b • x) := by
  induction a using DirectSum.Decomposition.inductionOn
    (MvPolynomial.homogeneousSubmodule (Fin 2) k) with
  | zero => simp only [zero_mul, zero_smul_law]
  | add a c ha hc =>
    simp only [add_mul, add_smul_law, ha, hc]
  | homogeneous a =>
    induction b using DirectSum.Decomposition.inductionOn
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) with
    | zero => simp only [mul_zero, zero_smul_law, smul_zero_law]
    | add b c hb hc =>
      simp only [mul_add, add_smul_law, smul_add_law, hb, hc]
    | homogeneous b =>
      induction x using DirectSum.induction_on with
      | zero => simp only [smul_zero_law]
      | add x y hx hy => simp only [smul_add_law, hx, hy]
      | of z s =>
        rw [homogeneous_single k G _ z _ (SetLike.GradedMul.mul_mem a.property b.property),
          homogeneous_single k G _ z _ b.property,
          homogeneous_single k G _ _ _ a.property]
        exact (DFinsupp.single_eq_single_iff _ _ _ _).mpr
          (Or.inl ⟨by omega, homogeneous_mul k G _ _ z _ _ a.property b.property s⟩)

/-- The explicit finite-sum action satisfies the polynomial module laws.

Source: Stacks Project, Lemma 01YS(5), the graded module of twisted global sections;
Stacks Definition 01MN for twists and Lemma 01M7 for localizations and functoriality.
(blueprint: lem-sc-p1-section-action-laws).
Proof: the decomposition of a polynomial is additive and multiplicative. On a summand of
nonnegative degree, `serreSectionHomogeneous` is the map on sections induced by multiplication
of local homogeneous fractions, tensored with the identity of G. Multiplication of fractions
is additive in each variable, multiplication by one is the identity, and composition is
multiplication by the product, after transporting the degree equality. Tensoring and taking
sections preserve these equalities. In negative source degrees the section group is the zero
group, so the same equalities hold. Expand the two finite sums defining `serreSectionSMul`,
use distributivity of finite sums, and the decomposition identity for the product of two
polynomials to obtain `mul_smul`; the remaining additive laws follow from the additive and
unit identities. For a homogeneous scalar and a single section summand, both decompositions
have a single possibly nonzero component; the same expansion yields the displayed single
summand formula, including the zero polynomial and zero section. No coherence, nonzero
section, or finite generation hypothesis is used. -/
theorem serreSectionActionLaws :
    (∀ x : serreSectionSum k G, (1 : MvPolynomial (Fin 2) k) • x = x) ∧
    (∀ (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G),
      (a * b) • x = a • (b • x)) ∧
    (∀ (a : MvPolynomial (Fin 2) k) (x y : serreSectionSum k G),
      a • (x + y) = a • x + a • y) ∧
    (∀ (a b : MvPolynomial (Fin 2) k) (x : serreSectionSum k G),
      (a + b) • x = a • x + b • x) ∧
    (∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k)
      (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
      (s : serreSectionPiece k G z),
      a • DirectSum.of (serreSectionPiece k G) z s =
        DirectSum.of (serreSectionPiece k G) (z + e)
          (serreSectionHomogeneous k G e z ⟨a, ha⟩ s)) := by
  exact ⟨one_smul_law k G, mul_smul_law k G, smul_add_law k G,
    add_smul_law k G, homogeneous_single k G⟩

/-- The module structure on the explicit direct sum, using only the named action-law proof. -/
noncomputable instance serreSectionSumModule :
    Module (MvPolynomial (Fin 2) k) (serreSectionSum k G) where
  one_smul := (serreSectionActionLaws k G).1
  mul_smul := (serreSectionActionLaws k G).2.1
  smul_add := (serreSectionActionLaws k G).2.2.1
  smul_zero a := by
    classical
    change serreSectionSMul k G a 0 = 0
    simp [serreSectionSMul]
  add_smul := (serreSectionActionLaws k G).2.2.2.1
  zero_smul x := by
    classical
    change serreSectionSMul k G 0 x = 0
    simp [serreSectionSMul]

end AlgebraicGeometry
