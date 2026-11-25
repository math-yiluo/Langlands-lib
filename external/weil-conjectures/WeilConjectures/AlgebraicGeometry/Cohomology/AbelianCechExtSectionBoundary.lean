/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
public import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionInjective
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionCycle
import WeilConjectures.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Ext boundary equals the horseshoe section boundary

Source: Stacks Project, Tags 01EQ and 0117.
(blueprint: lem-pc-abelian-cech-ext-section-boundary)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf cohomology boundary sends a lifted cocycle to its differential factor.
Source: Stacks Project, Tags 05TE and 06XR.

Proof: Compute the injective-resolution boundary in the standard Ext universe by
`InjectiveResolution.extMk_resolution_connecting_eq_triangle`: the lift b of c has
differential a through the first row map, so the triangle boundary sends extMk(c)
to extMk(a). The triangle connecting morphism is composition with the short-exact
extension class, with degree q followed by degree one and no sign. The canonical
change-of-universe equivalence preserves extMk, the short-exact extension class,
and their compositions. Transport the equation through that equivalence to the
small sheaf Ext instance used by functorHδ. This proves the displayed equation for
any supplied lifts; it requires neither a section complex nor an identification
of Ext with section homology. The same formula holds at q=0. -/
private theorem abelianExt_boundary_cocycle
    {X : Scheme.{u}}
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (I₁ : InjectiveResolution T.X₁) (I₂ : InjectiveResolution T.X₂)
    (I₃ : InjectiveResolution T.X₃)
    (α : I₁.cocomplex ⟶ I₂.cocomplex) (β : I₂.cocomplex ⟶ I₃.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I₁.ι ≫ α = (CochainComplex.single₀ _).map T.f ≫ I₂.ι)
    (hβ : I₂.ι ≫ β = (CochainComplex.single₀ _).map T.g ≫ I₃.ι)
    (hrows : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact)
    (q : ℕ)
    (c : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₃.cocomplex.X q)
    (hc : c ≫ I₃.cocomplex.d q (q + 1) = 0)
    (b : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₂.cocomplex.X q)
    (hb : b ≫ β.f q = c)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₁.cocomplex.X (q + 1))
    (ha : a ≫ I₁.cocomplex.d (q + 1) (q + 1 + 1) = 0)
    (hba : b ≫ I₂.cocomplex.d q (q + 1) = a ≫ α.f (q + 1)) :
    Sheaf.functorHδ hT q (I₃.extMk c (q + 1) rfl hc) =
      I₁.extMk a (q + 1 + 1) rfl ha  := by
  let C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let M := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let := HasDerivedCategory.standard C
  have : HasExt.{u + 1} C := HasExt.standard C
  have h := InjectiveResolution.extMk_resolution_connecting_eq_triangle hT M
    I₁ I₂ I₃ α β hαβ hα hβ hrows q c hc b hb a ha hba
  rw [Abelian.Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply
    hT _ rfl] at h
  apply Abelian.Ext.ext
  rw [Sheaf.functorHδ_apply, Sheaf.H.δSucc_apply]
  simpa only [Abelian.Ext.comp_hom, ShortComplex.ShortExact.extClass_hom,
    InjectiveResolution.extMk_hom] using h


set_option backward.isDefEq.respectTransparency false in
/-- The cocycle-compatible Ext/section identifications preserve the boundary.
Source: Stacks 0117 (lift-differentiate-lift) and 01EQ (resolution sections).
(blueprint: lem-pc-abelian-cech-ext-section-boundary)

Proof: Fix an Ext class t in degree q of the last sheaf and use he₃ to
represent it by a cocycle c and section cycle z₃. Split the horseshoe row
in degree q and compose c with its section to obtain b in the middle
resolution. Its differential maps to zero in the last resolution, hence
factors uniquely through the first inclusion in degree q+1 as a. The
next differential of a is zero because its composite with the monic first
inclusion is the square of the middle differential. The injective-resolution
formula for the Ext boundary sends extMk(c) to extMk(a). Under the
constant-sheaf adjunction evaluated at 1, b lifts the section represented
by c, and its differential is the image of the section represented by a:
the adjunction is natural in each row map and differential. The concrete
homology boundary formula for hS therefore sends homologyπ(z₃) to the
homology class y of this latter section. To identify its Ext class using
he₁ without choosing a preferred representative, apply he₁ to e₁.inv(y).
Its section class is y by the isomorphism equation. The section-homology
injectivity lemma therefore identifies its Ext class with extMk(a).
Applying e₁.hom gives e₁.hom(extMk(a)) = y. Substitute the he₃ class
equation and use extensionality of additive maps. The Ext boundary formula
may first be computed in the standard large Ext universe; transport through
the canonical change-of-universe equivalence, which preserves cocycle
classes and composition with the short-exact extension class.
The lift formula also holds for q=0, with no negative-degree terms. No
cover, tuple set, or total complex is involved in this assertion. -/
theorem abelianCechExtSection_boundary
    {X : Scheme.{u}}
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (I₁ : InjectiveResolution T.X₁) (I₂ : InjectiveResolution T.X₂)
    (I₃ : InjectiveResolution T.X₃)
    (α : I₁.cocomplex ⟶ I₂.cocomplex) (β : I₂.cocomplex ⟶ I₃.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I₁.ι ≫ α = (CochainComplex.single₀ _).map T.f ≫ I₂.ι)
    (hβ : I₂.ι ≫ β = (CochainComplex.single₀ _).map T.g ≫ I₃.ι)
    (hrows : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact)
    (hS : ((ShortComplex.mk α β hαβ).map
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℕ))).ShortExact)
    (q : ℕ)
    (e₁ : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁ ≅
      (abelianCechSections I₁).homology (q + 1))
    (e₃ : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃ ≅
      (abelianCechSections I₃).homology q)
    (he₁ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₁.cocomplex.X (q + 1))
        (ha : a ≫ I₁.cocomplex.d (q + 1) ((q + 1) + 1) = 0)
        (z : (abelianCechSections I₁).cycles (q + 1)),
        I₁.extMk a ((q + 1) + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₁).iCycles (q + 1) z ∧
        e₁.hom t = (abelianCechSections I₁).homologyπ (q + 1) z)
    (he₃ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₃.cocomplex.X q)
        (ha : a ≫ I₃.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I₃).cycles q),
        I₃.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₃).iCycles q z ∧
        e₃.hom t = (abelianCechSections I₃).homologyπ q z) :
    Sheaf.functorHδ hT q ≫ e₁.hom = e₃.hom ≫ hS.δ q (q + 1) rfl  := by
  classical
  let R := ShortComplex.mk α β hαβ
  have inj (n : ℕ) : Injective ((R.map (HomologicalComplex.eval _ (.up ℕ) n)).X₁) :=
    I₁.injective n
  let σ (n : ℕ) := (hrows n).splittingOfInjective
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  ext t
  obtain ⟨c, hc, z₃, hct, hz₃, he₃t⟩ := he₃ t
  let b : _ ⟶ I₂.cocomplex.X q := c ≫ (σ q).s
  have hb : b ≫ β.f q = c := by
    have hs : (σ q).s ≫ β.f q = 𝟙 (I₃.cocomplex.X q) := (σ q).s_g
    dsimp only [b]
    rw [Category.assoc, hs, Category.comp_id]
  have hdb : (b ≫ I₂.cocomplex.d q (q + 1)) ≫ β.f (q + 1) = 0 := by
    rw [Category.assoc, ← β.comm, ← Category.assoc, hb, hc]
  have mono : Mono (R.map (HomologicalComplex.eval _ (.up ℕ) (q + 1))).f :=
    (hrows (q + 1)).mono_f
  let a : _ ⟶ I₁.cocomplex.X (q + 1) :=
    (hrows (q + 1)).exact.lift (b ≫ I₂.cocomplex.d q (q + 1)) hdb
  have hba : a ≫ α.f (q + 1) = b ≫ I₂.cocomplex.d q (q + 1) :=
    (hrows (q + 1)).exact.lift_f _ hdb
  have ha : a ≫ I₁.cocomplex.d (q + 1) (q + 1 + 1) = 0 := by
    have : Mono (α.f (q + 1 + 1)) := (hrows (q + 1 + 1)).mono_f
    rw [← cancel_mono (α.f (q + 1 + 1)), Category.assoc, ← α.comm,
      ← Category.assoc, hba, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, zero_comp]
  obtain ⟨z₁, hz₁⟩ := abelianCech_ext_section_cycle I₁ (q + 1) a ha
  have hδ := abelianExt_boundary_cocycle T hT I₁ I₂ I₃ α β hαβ hα hβ hrows
    q c hc b hb a ha hba.symm
  have hsection : hS.δ q (q + 1) rfl ((abelianCechSections I₃).homologyπ q z₃) =
      (abelianCechSections I₁).homologyπ (q + 1) z₁ := by
    let instForget : HasForget₂ AddCommGrpCat.{u} AddCommGrpCat.{u} :=
      ⟨𝟭 _, rfl⟩
    have : (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).Additive := by
      change (𝟭 AddCommGrpCat.{u}).Additive
      infer_instance
    have : (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).PreservesHomology := by
      change (𝟭 AddCommGrpCat.{u}).PreservesHomology
      infer_instance
    let x₃ := (adj.homEquiv _ _ c) (ULift.up 1)
    let x₂ := (adj.homEquiv _ _ b) (ULift.up 1)
    let x₁ := (adj.homEquiv _ _ a) (ULift.up 1)
    have hx₃ : (abelianCechSections I₃).d q (q + 1) x₃ = 0 := by
      have ht := ConcreteCategory.congr_hom
        (adj.homEquiv_naturality_right c (I₃.cocomplex.d q (q + 1))) (ULift.up 1)
      simp only [ConcreteCategory.comp_apply] at ht
      rw [hc, adj.homAddEquiv_zero] at ht
      exact ht.symm
    have hx₂ : (β.f q).hom.app (op ⊤) x₂ = x₃ := by
      have ht := ConcreteCategory.congr_hom
        (adj.homEquiv_naturality_right b (β.f q)) (ULift.up 1)
      simp only [ConcreteCategory.comp_apply] at ht
      rw [hb] at ht
      exact ht.symm
    have hx₁ : (α.f (q + 1)).hom.app (op ⊤) x₁ =
        (abelianCechSections I₂).d q (q + 1) x₂ := by
      have ht₁ := ConcreteCategory.congr_hom
        (adj.homEquiv_naturality_right a (α.f (q + 1))) (ULift.up 1)
      have ht₂ := ConcreteCategory.congr_hom
        (adj.homEquiv_naturality_right b (I₂.cocomplex.d q (q + 1))) (ULift.up 1)
      simp only [ConcreteCategory.comp_apply] at ht₁ ht₂
      rw [hba] at ht₁
      exact ht₁.symm.trans ht₂
    have hd := hS.δ_apply.{u, u + 1} q (q + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
      (q + 1 + 1) (by simp)
    have hcycle₃ : (abelianCechSections I₃).cyclesMk x₃ (q + 1) (by simp) hx₃ = z₃ := by
      apply (AddCommGrpCat.mono_iff_injective ((abelianCechSections I₃).iCycles q)).mp
        inferInstance
      have hi : (abelianCechSections I₃).iCycles q
          ((abelianCechSections I₃).cyclesMk x₃ (q + 1) (by simp) hx₃) = x₃ :=
        HomologicalComplex.i_cyclesMk.{u, u + 1}
          (abelianCechSections I₃) x₃ (q + 1) (by simp) hx₃
      exact hi.trans hz₃
    have hx₁zero : (abelianCechSections I₁).d (q + 1) (q + 1 + 1) x₁ = 0 := by
      have ht := ConcreteCategory.congr_hom
        (adj.homEquiv_naturality_right a (I₁.cocomplex.d (q + 1) (q + 1 + 1)))
          (ULift.up 1)
      simp only [ConcreteCategory.comp_apply] at ht
      rw [ha, adj.homAddEquiv_zero] at ht
      exact ht.symm
    have hcycle₁ : (abelianCechSections I₁).cyclesMk x₁ (q + 1 + 1)
        (by simp) hx₁zero = z₁ := by
      apply (AddCommGrpCat.mono_iff_injective
        ((abelianCechSections I₁).iCycles (q + 1))).mp inferInstance
      have hi : (abelianCechSections I₁).iCycles (q + 1)
          ((abelianCechSections I₁).cyclesMk x₁ (q + 1 + 1) (by simp) hx₁zero) = x₁ :=
        HomologicalComplex.i_cyclesMk.{u, u + 1}
          (abelianCechSections I₁) x₁ (q + 1 + 1) (by simp) hx₁zero
      exact hi.trans hz₁
    change hS.δ q (q + 1) rfl
      ((abelianCechSections I₃).homologyπ q
        ((abelianCechSections I₃).cyclesMk x₃ (q + 1) (by simp) hx₃)) =
      (abelianCechSections I₁).homologyπ (q + 1)
        ((abelianCechSections I₁).cyclesMk x₁ (q + 1 + 1) (by simp) hx₁zero) at hd
    rw [hcycle₃, hcycle₁] at hd
    exact hd
  let y := (abelianCechSections I₁).homologyπ (q + 1) z₁
  obtain ⟨a', ha', z', hat, hz', he₁t⟩ := he₁ (e₁.inv y)
  have hclass : (abelianCechSections I₁).homologyπ (q + 1) z' = y := by
    rw [← he₁t]
    exact ConcreteCategory.congr_hom e₁.inv_hom_id y
  have hExt := abelianCech_ext_section_injective I₁ (q + 1) a' a ha' ha z' z₁
    hz' hz₁ hclass
  have he₁a : e₁.hom (I₁.extMk a (q + 1 + 1) rfl ha) = y := by
    rw [← hExt, hat]
    exact ConcreteCategory.congr_hom e₁.inv_hom_id y
  simp only [ConcreteCategory.comp_apply]
  rw [← hct, hδ, he₁a, hct, he₃t]
  exact hsection.symm

end AlgebraicGeometry.Scheme.Modules
