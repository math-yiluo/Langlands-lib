/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenDifferenceNaturality
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCompatibleBoundaries

/-! # Difference and boundary maps on canonical open diagrams

Source: Stacks Project, Tags 0A50 and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale


private noncomputable def diagramPairEquiv {J : Type u} [Category.{u} J]
    (A B : J ⥤ AddCommGrpCat.{u + 1}) [HasBinaryBiproduct A B] (j : J) :
    (A ⊞ B).obj j ≃+ (A.obj j × B.obj j) where
  toFun x := ((biprod.fst : A ⊞ B ⟶ A).app j x,
    (biprod.snd : A ⊞ B ⟶ B).app j x)
  invFun x := (biprod.inl : A ⟶ A ⊞ B).app j x.1 +
    (biprod.inr : B ⟶ A ⊞ B).app j x.2
  left_inv x := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : A ⊞ B ⟶ A ⊞ B ↦ f.app j)
        (biprod.total (X := A) (Y := B))) x
    exact h
  right_inv x := by
    have h₁ := ConcreteCategory.congr_hom
      (congrArg (fun f : A ⟶ A ↦ f.app j) (biprod.inl_fst (X := A) (Y := B))) x.1
    have h₂ := ConcreteCategory.congr_hom
      (congrArg (fun f : B ⟶ A ↦ f.app j) (biprod.inr_fst (X := A) (Y := B))) x.2
    have h₃ := ConcreteCategory.congr_hom
      (congrArg (fun f : A ⟶ B ↦ f.app j) (biprod.inl_snd (X := A) (Y := B))) x.1
    have h₄ := ConcreteCategory.congr_hom
      (congrArg (fun f : B ⟶ B ↦ f.app j) (biprod.inr_snd (X := A) (Y := B))) x.2
    change (biprod.fst : A ⊞ B ⟶ A).app j
      ((biprod.inl : A ⟶ A ⊞ B).app j x.1) = x.1 at h₁
    change (biprod.fst : A ⊞ B ⟶ A).app j
      ((biprod.inr : B ⟶ A ⊞ B).app j x.2) = 0 at h₂
    change (biprod.snd : A ⊞ B ⟶ B).app j
      ((biprod.inl : A ⟶ A ⊞ B).app j x.1) = 0 at h₃
    change (biprod.snd : A ⊞ B ⟶ B).app j
      ((biprod.inr : B ⟶ A ⊞ B).app j x.2) = x.2 at h₄
    apply Prod.ext
    · simp only [map_add, h₁, h₂, add_zero]
    · simp only [map_add, h₃, h₄, zero_add]
  map_add' x y := by
    apply Prod.ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add]

private theorem exact_transport
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (ea : A ≃+ A') (eb : B ≃+ B') (ec : C ≃+ C')
    {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}
    (hf : ∀ x, eb (f x) = f' (ea x)) (hg : ∀ x, ec (g x) = g' (eb x))
    (hex : Function.Exact f' g') : Function.Exact f g := by
  intro b
  constructor
  · intro hb
    have hz : g' (eb b) = 0 := by rw [← hg, hb, map_zero]
    obtain ⟨a', ha'⟩ := (hex (eb b)).mp hz
    obtain ⟨a, rfl⟩ := ea.surjective a'
    refine ⟨a, eb.injective ?_⟩
    rw [hf, ha']
  · rintro ⟨a, rfl⟩
    apply ec.injective
    rw [map_zero, hg, hf]
    exact (hex _).mpr ⟨ea a, rfl⟩


private theorem iso_hom_inv {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x :=
  e.addCommGroupIsoToAddEquiv.apply_symm_apply x


private theorem hom_congr {A B : AddCommGrpCat.{u + 1}} {f g : A ⟶ B}
    (h : f = g) (x : A) : f.hom x = g.hom x :=
  congrArg (fun k : A ⟶ B ↦ k.hom x) h


set_option backward.isDefEq.respectTransparency true in
private theorem algebraic_boundary_transport
    {J : Type u} [Category.{u} J]
    (A B C E A₁ B₁ : J ⥤ AddCommGrpCat.{u + 1})
    [HasBinaryBiproduct A B] [HasBinaryBiproduct A₁ B₁]
    (SA SB SC SE SA₁ SB₁ : J → AddCommGrpCat.{u + 1})
    (TA TB TC TE Z : AddCommGrpCat.{u + 1})
    (eA : ∀ j, A.obj j ≅ SA j)
    (eB : ∀ j, B.obj j ≅ SB j)
    (eC : ∀ j, C.obj j ≅ SC j)
    (eE : ∀ j, E.obj j ≅ SE j)
    (eA₁ : ∀ j, A₁.obj j ≅ SA₁ j)
    (eB₁ : ∀ j, B₁.obj j ≅ SB₁ j)
    (eZ : Z ≅ TE)
    (mA : ∀ {j k}, (j ⟶ k) → (SA j ⟶ SA k))
    (mB : ∀ {j k}, (j ⟶ k) → (SB j ⟶ SB k))
    (mC : ∀ {j k}, (j ⟶ k) → (SC j ⟶ SC k))
    (mE : ∀ {j k}, (j ⟶ k) → (SE j ⟶ SE k))
    (hA : ∀ j k (f : j ⟶ k), A.map f = (eA j).hom ≫ mA f ≫ (eA k).inv)
    (hB : ∀ j k (f : j ⟶ k), B.map f = (eB j).hom ≫ mB f ≫ (eB k).inv)
    (hC : ∀ j k (f : j ⟶ k), C.map f = (eC j).hom ≫ mC f ≫ (eC k).inv)
    (hE : ∀ j k (f : j ⟶ k), E.map f = (eE j).hom ≫ mE f ≫ (eE k).inv)
    (ιA : A ⟶ (Functor.const J).obj TA)
    (ιB : B ⟶ (Functor.const J).obj TB)
    (ιC : C ⟶ (Functor.const J).obj TC) (η : E ⟶ (Functor.const J).obj Z)
    (lA : ∀ j, SA j ⟶ TA)
    (lB : ∀ j, SB j ⟶ TB)
    (lC : ∀ j, SC j ⟶ TC)
    (lE : ∀ j, SE j ⟶ TE)
    (hιA : ∀ j, ιA.app j = (eA j).hom ≫ lA j)
    (hιB : ∀ j, ιB.app j = (eB j).hom ≫ lB j)
    (hιC : ∀ j, ιC.app j = (eC j).hom ≫ lC j)
    (hη : ∀ j, η.app j ≫ eZ.hom = (eE j).hom ≫ lE j)
    (ι₁ : A ⊞ B ⟶ (Functor.const J).obj (AddCommGrpCat.of (TA × TB)))
    (h₁U : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst TA TB) =
      (biprod.fst : A ⊞ B ⟶ A).app j ≫ ιA.app j)
    (h₁V : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd TA TB) =
      (biprod.snd : A ⊞ B ⟶ B).app j ≫ ιB.app j)
    (r : E ⟶ A₁ ⊞ B₁) (rA : ∀ j, SE j →+ SA₁ j) (rB : ∀ j, SE j →+ SB₁ j)
    (hrA : ∀ j, r.app j ≫ (biprod.fst : A₁ ⊞ B₁ ⟶ A₁).app j ≫ (eA₁ j).hom =
      (eE j).hom ≫ AddCommGrpCat.ofHom (rA j))
    (hrB : ∀ j, r.app j ≫ (biprod.snd : A₁ ⊞ B₁ ⟶ B₁).app j ≫ (eB₁ j).hom =
      (eE j).hom ≫ AddCommGrpCat.ofHom (rB j))
    (δ : ∀ j, SC j →+ SE j) (δL : TC →+ TE)
    (d : ∀ j, SA j × SB j →+ SC j) (dL : TA × TB →+ TC)
    (hdmap : ∀ j k (f : j ⟶ k) x y,
      d k ((mA f).hom x, (mB f).hom y) =
        (mC f).hom (d j (x, y)))
    (hdleg : ∀ j x y, dL ((lA j).hom x, (lB j).hom y) =
      (lC j).hom (d j (x, y)))
    (hdδ : ∀ j, Function.Exact (d j) (δ j))
    (hδr : ∀ j, Function.Exact (δ j) (fun x ↦ (rA j x, rB j x)))
    (hdLδL : Function.Exact (dL) δL)
    (hδmap : ∀ j k (f : j ⟶ k) x, δ k ((mC f).hom x) = (mE f).hom (δ j x))
    (hδleg : ∀ j x, δL ((lC j).hom x) = (lE j).hom (δ j x)) :
    ∃ (a : A ⊞ B ⟶ C) (b : C ⟶ E)
      (a' : AddCommGrpCat.of (TA × TB) ⟶ TC) (b' : TC ⟶ Z),
      (∀ j, Function.Exact (a.app j) (b.app j)) ∧
      (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
      (∀ j, a.app j ≫ ιC.app j = ι₁.app j ≫ a') ∧
      (∀ j, b.app j ≫ η.app j = ιC.app j ≫ b') := by
  classical
  let eP := fun j ↦ (diagramPairEquiv A B j).trans
    ((eA j).addCommGroupIsoToAddEquiv.prodCongr (eB j).addCommGroupIsoToAddEquiv)
  let eP₁ := fun j ↦ (diagramPairEquiv A₁ B₁ j).trans
    ((eA₁ j).addCommGroupIsoToAddEquiv.prodCongr (eB₁ j).addCommGroupIsoToAddEquiv)
  have ePU (j : J) (x : (A ⊞ B).obj j) :
      (eP j x).1 = (eA j).hom.hom (((biprod.fst : A ⊞ B ⟶ A).app j).hom x) := rfl
  have ePV (j : J) (x : (A ⊞ B).obj j) :
      (eP j x).2 = (eB j).hom.hom (((biprod.snd : A ⊞ B ⟶ B).app j).hom x) := rfl
  have ePmap : ∀ (j k : J) (f : j ⟶ k) (x : (A ⊞ B).obj j),
      eP k (((A ⊞ B).map f).hom x) =
      ((mA f).hom (eP j x).1,
        (mB f).hom (eP j x).2) := by
    intro j k f x
    apply Prod.ext
    · rw [ePU, ePU]
      have h := hom_congr
        ((biprod.fst : A ⊞ B ⟶ A).naturality f) x
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
      change (eA k).hom.hom (_) =
        (mA f).hom
          ((eA j).hom.hom _)
      rw [h, hA j k f]
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
      exact iso_hom_inv (eA k) _
    · rw [ePV, ePV]
      have h := hom_congr
        ((biprod.snd : A ⊞ B ⟶ B).naturality f) x
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
      change (eB k).hom.hom (_) =
        (mB f).hom
          ((eB j).hom.hom _)
      rw [h, hB j k f]
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
      exact iso_hom_inv (eB k) _
  let aApp : ∀ j : J, (A ⊞ B).obj j ⟶ C.obj j := fun j ↦
    AddCommGrpCat.ofHom ((d j).comp (eP j).toAddMonoidHom) ≫ (eC j).inv
  have ha : ∀ (j : J) (x : (A ⊞ B).obj j),
      (eC j).hom.hom ((aApp j).hom x) = d j (eP j x) := by
    intro j x
    exact iso_hom_inv (eC j) _
  let a : A ⊞ B ⟶ C :=
    { app := aApp
      naturality := by
        intro j k f
        ext x
        apply (eC k).addCommGroupIsoToAddEquiv.injective
        change (eC k).hom.hom ((aApp k).hom (((A ⊞ B).map f).hom x)) =
          (eC k).hom.hom (((C).map f).hom ((aApp j).hom x))
        rw [ha, ePmap, hC]
        simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
        rw [iso_hom_inv (eC k), ha]
        exact hdmap j k f _ _ }
  let bApp := fun (j : J) ↦ (eC j).hom ≫ AddCommGrpCat.ofHom (δ j) ≫ (eE j).inv
  have hb : ∀ (j : J) (x : (C).obj j),
      (eE j).hom.hom ((bApp j).hom x) = δ j ((eC j).hom.hom x) := by
    intro j x
    simp only [bApp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
      AddCommGrpCat.hom_ofHom]
    exact iso_hom_inv (eE j) _
  let b : C ⟶ E :=
    { app := bApp
      naturality := by
        intro j k f
        ext x
        apply (eE k).addCommGroupIsoToAddEquiv.injective
        change (eE k).hom.hom ((bApp k).hom (((C).map f).hom x)) =
          (eE k).hom.hom ((E.map f).hom ((bApp j).hom x))
        rw [hb, hC, hE j k f]
        simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
        rw [hb, iso_hom_inv (eC k), iso_hom_inv (eE k)]
        exact hδmap j k f _ }
  let a' := AddCommGrpCat.ofHom dL
  let b' := AddCommGrpCat.ofHom δL ≫ eZ.inv
  have ha' (x : TA × TB) : a'.hom x = dL x := rfl
  refine ⟨a, b, a', b', ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact exact_transport (eP j) (eC j).addCommGroupIsoToAddEquiv
      (eE j).addCommGroupIsoToAddEquiv (ha j) (hb j) (hdδ j)
  · intro j
    apply exact_transport (eC j).addCommGroupIsoToAddEquiv
      (eE j).addCommGroupIsoToAddEquiv (eP₁ j) (hb j)
      (fun x ↦ ?_) (hδr j)
    apply Prod.ext
    · exact hom_congr (hrA j) x
    · exact hom_congr (hrB j) x
  · intro x
    constructor
    · intro hx
      have hz : δL x = 0 := by
        apply eZ.addCommGroupIsoToAddEquiv.symm.injective
        change eZ.inv.hom (δL x) = eZ.inv.hom 0
        change b'.hom x = 0 at hx
        simpa only [b', AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
          AddCommGrpCat.hom_ofHom, map_zero] using hx
      obtain ⟨y, hy⟩ := (hdLδL x).mp hz
      exact ⟨y, (ha' y).trans hy⟩
    · rintro ⟨y, hy⟩
      have hz : δL x = 0 := (hdLδL x).mpr ⟨y, (ha' y).symm.trans hy⟩
      change eZ.inv.hom (δL x) = 0
      rw [hz, map_zero]
  · intro j
    ext x
    have hU := hom_congr (h₁U j) x
    have hV := hom_congr (h₁V j) x
    change ((ι₁.app j).hom x).1 =
      (ιA.app j).hom (((biprod.fst : A ⊞ B ⟶ A).app j).hom x) at hU
    change ((ι₁.app j).hom x).2 =
      (ιB.app j).hom (((biprod.snd : A ⊞ B ⟶ B).app j).hom x) at hV
    change (ιC.app j).hom ((aApp j).hom x) = a'.hom ((ι₁.app j).hom x)
    rw [ha']
    refine (hom_congr (hιC j) ((aApp j).hom x)).trans ?_
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    have hpair : (ι₁.app j).hom x =
        ((lA j).hom (eP j x).1,
          (lB j).hom (eP j x).2) := by
      apply Prod.ext
      · change ((ι₁.app j).hom x).1 =
          (lA j).hom (eP j x).1
        exact hU.trans ((hom_congr (hιA j) _).trans
          (congrArg (lA j).hom
            (ePU j x).symm))
      · change ((ι₁.app j).hom x).2 =
          (lB j).hom (eP j x).2
        exact hV.trans ((hom_congr (hιB j) _).trans
          (congrArg (lB j).hom
            (ePV j x).symm))
    exact (congrArg (lC j).hom
      (ha j x)).trans ((hdleg j _ _).symm.trans (congrArg dL hpair.symm))
  · intro j
    ext x
    apply eZ.addCommGroupIsoToAddEquiv.injective
    change eZ.hom.hom ((η.app j).hom ((bApp j).hom x)) = eZ.hom.hom (b'.hom ((ιC.app j).hom x))
    have h := hom_congr (hη j) ((bApp j).hom x)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
    refine h.trans ?_
    rw [hb j x, hιC j]
    simp only [b', AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
      AddCommGrpCat.hom_ofHom]
    rw [iso_hom_inv eZ]
    exact (hδleg j ((eC j).hom.hom x)).symm


set_option backward.isDefEq.respectTransparency true in
-- The large dependent cohomology signature and its transports require additional elaboration steps.
set_option linter.unusedVariables false in
/-- Construct the difference and boundary maps, leaving the restriction row supplied.

Source: Stacks Project, Tag 0A50, coefficient-natural long exact sequence;
Tag 09YQ, coherent-system maps.
(blueprint: lem-weil-pbc-etale-limit-open-boundary-transform).

Proof: Use the supplied covering equations at each tail stage and at c.pt.
Inverse image preserves intersections, identifying the intersection with the
supplied intersection open.
Use the
functorial Mayer--Vietoris connecting transformation before evaluating at the
coefficient sheaves, so the same boundary is natural for all transitions and
cone legs. Transport the difference and boundary by eKU, eKV, eKI and eH;
at the bottom transport the boundary by eB.inv. More explicitly, identify the
stage biproduct with the ordinary product by evaluation's biproduct comparison
and biprodIsoProd, then apply the two object isomorphisms. The map a_j is this
identification followed by restriction from U_j to the intersection minus
restriction from V_j, followed by eKI_j.inv. The map b_j is eKI_j.hom followed
by the canonical boundary delta_j followed by eH_j.inv. The bottom a' is the
actual difference of intersection restrictions, and b' is delta_L followed by
eB.inv. The comparisons are all isomorphisms, so images and kernels of these
maps are the images and kernels in the original long exact sequence.
Coefficient naturality and
pullback naturality prove that the stage maps are natural transformations.
The long exact sequence gives exactness of (a,b). For (b,r), the supplied
component formulas hrU and hrV identify the kernel of r with the kernel of
the actual pair of restrictions: the biproduct projections are jointly monic
and eKU,eKV are isomorphisms. The long exact sequence gives that kernel as
the image of b. Transport also gives bottom exactness. Naturality under the
restricted cone projections followed by the coefficient legs proves the two
left squares. For the difference square, postcompose the two factors with
intersection restriction and subtract; h₁U and h₁V replace the product leg by the
two supplied legs. Pullback/coefficient naturality identifies each resulting term
with the intersection leg after the corresponding stage restriction. For the
boundary square, substitute hB and hιI, cancel eH and eKI, and apply the naturality
of the same connecting transformation under the cone projection followed by
(eG_j).inv;L_j. These equations are exactly the two asserted left squares.
This theorem constructs neither r nor a product cocone map and
asserts no right square. The argument also applies to empty or coincident
opens. -/
theorem etale_limit_open_boundary_transform
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (q + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (q + 1)) ≫ (eH j).inv)
    (B : Cocone H)
    (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (q + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (q + 1)))
    (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X)
    (hstageCover : ∀ j : Set.Ici i₀,
      tailStageOpen D g₀ U j ⊔ tailStageOpen D g₀ V j = ⊤)
    (hlimitCover : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U) ⊔
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V) = ⊤)
    (KU : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKU : ∀ n j, (KU n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ U j).ι).obj (F j.val)) n))
    (hKU : ∀ n j k (f : j ⟶ k), (KU n).map f =
      (eKU n j).hom ≫ tailOpenCohomologyMapDegree D g₀ U F φ n f ≫ (eKU n k).inv)
    (ιU : ∀ n, KU n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) n)))
    (hιU : ∀ n j, (ιU n).app j =
      (eKU n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ U F G eG L n j)
    (KV : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKV : ∀ n j, (KV n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ V j).ι).obj (F j.val)) n))
    (hKV : ∀ n j k (f : j ⟶ k), (KV n).map f =
      (eKV n j).hom ≫ tailOpenCohomologyMapDegree D g₀ V F φ n f ≫ (eKV n k).inv)
    (ιV : ∀ n, KV n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) n)))
    (hιV : ∀ n j, (ιV n).app j =
      (eKV n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ V F G eG L n j)
    (KI : ℕ → Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
    (eKI : ∀ n j, (KI n).obj j ≅ AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ (U ⊓ V) j).ι).obj (F j.val)) n))
    (hKI : ∀ n j k (f : j ⟶ k), (KI n).map f =
      (eKI n j).hom ≫ tailOpenCohomologyMapDegree D g₀ (U ⊓ V) F φ n f ≫ (eKI n k).inv)
    (ιI : ∀ n, KI n ⟶ (Functor.const (Set.Ici i₀)).obj (AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)).ι).obj L.pt) n)))
    (hιI : ∀ n j, (ιI n).app j =
      (eKI n j).hom ≫ tailOpenCohomologyLegDegree D c g₀ (U ⊓ V) F G eG L n j)
    (ι₁ : KU q ⊞ KV q ⟶ (Functor.const (Set.Ici i₀)).obj
      (AddCommGrpCat.of
        (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) q ×
         Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) q)))
    (h₁U : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (biprod.fst : KU q ⊞ KV q ⟶ KU q).app j ≫ (ιU q).app j)
    (h₁V : ∀ j, ι₁.app j ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (biprod.snd : KU q ⊞ KV q ⟶ KV q).app j ≫ (ιV q).app j)
    (r : ((show Monotone (fun j : Set.Ici i₀ ↦ j.val) from
      fun _ _ h ↦ h).functor) ⋙ H ⟶ KU (q + 1) ⊞ KV (q + 1))
    (hrU : ∀ j, r.app j ≫ (biprod.fst : KU (q + 1) ⊞ KV (q + 1) ⟶
      KU (q + 1)).app j ≫ (eKU (q + 1) j).hom =
      (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (tailStageOpen D g₀ U j).ι (F j.val) (q + 1)))
    (hrV : ∀ j, r.app j ≫ (biprod.snd : KU (q + 1) ⊞ KV (q + 1) ⟶
      KV (q + 1)).app j ≫ (eKV (q + 1) j).hom =
      (eH j.val).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (tailStageOpen D g₀ V j).ι (F j.val) (q + 1)))
 :
    let t : Set.Ici i₀ ⥤ I :=
      (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from fun _ _ h ↦ h).functor
    let WU := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V
    let WI := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)
    let BI := AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WI.ι).obj L.pt) q)
    let BP := fun n ↦ AddCommGrpCat.of
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WU.ι).obj L.pt) n ×
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} WV.ι).obj L.pt) n)
    ∃ (a : KU q ⊞ KV q ⟶ KI q) (b : KI q ⟶ t ⋙ H)
      (a' : BP q ⟶ BI) (b' : BI ⟶ B.pt),
      (∀ j, Function.Exact (a.app j) (b.app j)) ∧
      (∀ j, Function.Exact (b.app j) (r.app j)) ∧ Function.Exact a' b' ∧
      (∀ j, a.app j ≫ (ιI q).app j = ι₁.app j ≫ a') ∧
      (∀ j, b.app j ≫ B.ι.app j.val = (ιI q).app j ≫ b') := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    let t : Set.Ici i₀ ⥤ I :=
      (show Monotone (fun j : Set.Ici i₀ ↦ j.val) from fun _ _ h ↦ h).functor
    let WU := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U
    let WV := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V
    let WI := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)
    have hDifference := tailOpenDifference_naturality X U V D c F φ G eG L q i₀ g₀
    let d := hDifference.choose
    let dL := hDifference.choose_spec.choose
    have hDifferenceProperties := hDifference.choose_spec.choose_spec
    have hd := hDifferenceProperties.1
    have hdL := hDifferenceProperties.2.1
    have hdmap := hDifferenceProperties.2.2.1
    have hdleg := hDifferenceProperties.2.2.2
    have hBoundaries := tailOpenCompatibleBoundaries X U V D c F φ G eG L q i₀ g₀
      d dL hd hdL hstageCover hlimitCover
    let δ := hBoundaries.choose
    let δL := hBoundaries.choose_spec.choose
    have hProperties := hBoundaries.choose_spec.choose_spec
    have hdδ := hProperties.1
    have hδr := hProperties.2.1
    have hdLδL := hProperties.2.2.1
    have hδmap := hProperties.2.2.2.1
    have hδleg := hProperties.2.2.2.2
    let η : t ⋙ H ⟶ (Functor.const (Set.Ici i₀)).obj B.pt :=
      { app := fun j ↦ B.ι.app j.val
        naturality := fun j k f ↦ B.ι.naturality (homOfLE (show j.val ≤ k.val from f.le)) }
    have hResult := algebraic_boundary_transport
      (KU q) (KV q) (KI q) (t ⋙ H) (KU (q + 1)) (KV (q + 1))
      _ _ _ _ _ _ _ _ _ _ B.pt
      (eKU q) (eKV q) (eKI q) (fun j ↦ eH j.val)
      (eKU (q + 1)) (eKV (q + 1)) eB
      (fun {j k} f ↦ tailOpenCohomologyMapDegree D g₀ U F φ q f)
      (fun {j k} f ↦ tailOpenCohomologyMapDegree D g₀ V F φ q f)
      (fun {j k} f ↦ tailOpenCohomologyMapDegree D g₀ (U ⊓ V) F φ q f)
      (fun {j k} f ↦ AddCommGrpCat.ofHom
        (cohomologyMap (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
          (F j.val) (q + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ (homOfLE f.le)) (q + 1)))
      (hKU q) (hKV q) (hKI q)
      (fun j k f ↦ hH j.val k.val (homOfLE (show j.val ≤ k.val from f.le)))
      (ιU q) (ιV q) (ιI q) η
      (fun j ↦ tailOpenCohomologyLegDegree D c g₀ U F G eG L q j)
      (fun j ↦ tailOpenCohomologyLegDegree D c g₀ V F G eG L q j)
      (fun j ↦ tailOpenCohomologyLegDegree D c g₀ (U ⊓ V) F G eG L q j)
      (fun j ↦ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op j.val)) (F j.val)
        (q + 1)) ≫ AddCommGrpCat.ofHom
        (Sheaf.H.map ((eG j.val).inv ≫ L.ι.app j.val) (q + 1)))
      (hιU q) (hιV q) (hιI q) (fun j ↦ hB j.val) ι₁ h₁U h₁V r
      (fun j ↦ cohomologyMap (tailStageOpen D g₀ U j).ι (F j.val) (q + 1))
      (fun j ↦ cohomologyMap (tailStageOpen D g₀ V j).ι (F j.val) (q + 1)) hrU hrV
      δ δL
      d dL
      hdmap hdleg hdδ hδr hdLδL
      (by
        intro j k f x
        simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
          AddCommGrpCat.hom_ofHom] using hδmap j k f x)
      (by
        intro j x
        simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
          AddCommGrpCat.hom_ofHom] using hδleg j x)
    exact hResult

end AlgebraicGeometry.Etale
