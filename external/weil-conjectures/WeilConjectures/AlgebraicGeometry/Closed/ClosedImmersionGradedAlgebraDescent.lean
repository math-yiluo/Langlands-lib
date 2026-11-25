/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Descent of homogeneous algebra operations through a closed immersion

Source: Stacks Project, Divisors, Tag 0630, and Modules, Lemma 08KS.
(blueprint: lem-pur-closed-immersion-graded-algebra-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

private noncomputable def ambient {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) : X.Opens :=
  i.isClosedEmbedding.isEmbedding.isInducing.functorObj V

private theorem pre_ambient {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) : i ⁻¹ᵁ ambient i V = V :=
  i.isClosedEmbedding.isEmbedding.isInducing.map_functorObj V

private noncomputable def rawPairing {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F G H : Z.Modules)
    (b : ∀ U : X.Opens, (F.val.obj (op (i ⁻¹ᵁ U))) →
      (G.val.obj (op (i ⁻¹ᵁ U))) → H.val.obj (op (i ⁻¹ᵁ U)))
    (V : Z.Opens) (a : F.val.obj (op V)) (c : G.val.obj (op V)) :
    H.val.obj (op V) :=
  H.val.map (homOfLE (pre_ambient i V).ge).op
    (b (ambient i V)
      (F.val.map (homOfLE (pre_ambient i V).le).op a)
      (G.val.map (homOfLE (pre_ambient i V).le).op c))

private theorem rawPairing_eq {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F G H : Z.Modules)
    (b : ∀ U : X.Opens, (F.val.obj (op (i ⁻¹ᵁ U))) →
      (G.val.obj (op (i ⁻¹ᵁ U))) → H.val.obj (op (i ⁻¹ᵁ U)))
    (hb : ∀ (U V : X.Opens) (h : V ≤ U)
      (a : F.val.obj (op (i ⁻¹ᵁ U))) (c : G.val.obj (op (i ⁻¹ᵁ U))),
      H.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op (b U a c) =
        b V (F.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op a)
          (G.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op c))
    (U : X.Opens) (a : F.val.obj (op (i ⁻¹ᵁ U)))
    (c : G.val.obj (op (i ⁻¹ᵁ U))) :
    rawPairing i F G H b (i ⁻¹ᵁ U) a c = b U a c := by
  have hU : U ≤ ambient i (i ⁻¹ᵁ U) :=
    i.isClosedEmbedding.isEmbedding.isInducing.le_functorObj_iff.mpr le_rfl
  have h := hb (ambient i (i ⁻¹ᵁ U)) U hU
    (F.val.map (homOfLE (pre_ambient i (i ⁻¹ᵁ U)).le).op a)
    (G.val.map (homOfLE (pre_ambient i (i ⁻¹ᵁ U)).le).op c)
  have hf : F.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE hU)).op
      (F.val.map (homOfLE (pre_ambient i (i ⁻¹ᵁ U)).le).op a) = a := by
    rw [← PresheafOfModules.map_comp_apply]
    change F.val.map (𝟙 (op (i ⁻¹ᵁ U))) a = a
    rw [F.val.map_id]
    rfl
  have hg : G.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE hU)).op
      (G.val.map (homOfLE (pre_ambient i (i ⁻¹ᵁ U)).le).op c) = c := by
    rw [← PresheafOfModules.map_comp_apply]
    change G.val.map (𝟙 (op (i ⁻¹ᵁ U))) c = c
    rw [G.val.map_id]
    rfl
  rw [hf, hg] at h
  exact h

private theorem exists_preimage_open {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : Z.Opens) : ∃ U : X.Opens, i ⁻¹ᵁ U = V :=
  ⟨ambient i V, pre_ambient i V⟩

private theorem exists_preimage_subopen {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.Opens) (V : Z.Opens) (hV : V ≤ i ⁻¹ᵁ U) :
    ∃ W : X.Opens, W ≤ U ∧ i ⁻¹ᵁ W = V := by
  refine ⟨U ⊓ ambient i V, inf_le_left, ?_⟩
  change i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ ambient i V = V
  rw [pre_ambient, inf_eq_right.mpr hV]

private theorem rawPairing_natural {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F G H : Z.Modules)
    (b : ∀ U : X.Opens, (F.val.obj (op (i ⁻¹ᵁ U))) →
      (G.val.obj (op (i ⁻¹ᵁ U))) → H.val.obj (op (i ⁻¹ᵁ U)))
    (hb : ∀ (U V : X.Opens) (h : V ≤ U)
      (a : F.val.obj (op (i ⁻¹ᵁ U))) (c : G.val.obj (op (i ⁻¹ᵁ U))),
      H.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op (b U a c) =
        b V (F.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op a)
          (G.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op c))
    (U V : Z.Opens) (h : V ≤ U) (a : F.val.obj (op U)) (c : G.val.obj (op U)) :
    H.val.map (homOfLE h).op (rawPairing i F G H b U a c) =
      rawPairing i F G H b V (F.val.map (homOfLE h).op a)
        (G.val.map (homOfLE h).op c) := by
  obtain ⟨U, rfl⟩ := exists_preimage_open i U
  obtain ⟨V, hVU, rfl⟩ := exists_preimage_subopen i U V h
  have hh : (homOfLE h).op =
      ((TopologicalSpace.Opens.map i.base).map (homOfLE hVU)).op := Subsingleton.elim _ _
  rw [hh, rawPairing_eq i F G H b hb, rawPairing_eq i F G H b hb]
  exact hb U V hVU a c

private theorem pairing_smul {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F G H : Z.Modules)
    (d : ∀ V : Z.Opens, F.val.obj (op V) → G.val.obj (op V) → H.val.obj (op V))
    (hd : ∀ (U V : Z.Opens) (h : V ≤ U) (a : F.val.obj (op U))
      (b : G.val.obj (op U)), H.val.map (homOfLE h).op (d U a b) =
        d V (F.val.map (homOfLE h).op a) (G.val.map (homOfLE h).op b))
    (hs : ∀ (U : X.Opens) (r : Γ(X, U)) (a : F.val.obj (op (i ⁻¹ᵁ U)))
      (b : G.val.obj (op (i ⁻¹ᵁ U))),
      d (i ⁻¹ᵁ U) ((i.app U).hom r • a) b = (i.app U).hom r • d (i ⁻¹ᵁ U) a b)
    (V : Z.Opens) (r : Γ(Z, V)) (a : F.val.obj (op V)) (b : G.val.obj (op V)) :
    d V (r • a) b = r • d V a b := by
  obtain ⟨U, rfl⟩ := exists_preimage_open i V
  apply TopCat.Presheaf.IsSheaf.section_ext H.isSheaf
  intro z hz
  obtain ⟨W, hW, hzW, hWU⟩ := exists_isAffineOpen_mem_and_subset (show i.base z ∈ U from hz)
  have hpre : i ⁻¹ᵁ W ≤ i ⁻¹ᵁ U := fun _ h ↦ hWU h
  refine ⟨i ⁻¹ᵁ W, hpre, hzW, ?_⟩
  obtain ⟨s, hs'⟩ := i.app_surjective W hW (Z.presheaf.map (homOfLE hpre).op r)
  change H.val.map (homOfLE hpre).op (d (i ⁻¹ᵁ U) (r • a) b) =
    H.val.map (homOfLE hpre).op (r • d (i ⁻¹ᵁ U) a b)
  rw [hd, H.val.map_smul, F.val.map_smul]
  change (i.app W).hom s = Z.ringCatSheaf.obj.map (homOfLE hpre).op r at hs'
  rw [← hs', hd]
  exact hs W s _ _

private theorem descend_bilinear {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F G H : Z.Modules)
    (b : ∀ U : X.Opens,
      ((Scheme.Modules.pushforward i).obj F).val.obj (op U) →ₗ[Γ(X, U)]
        ((Scheme.Modules.pushforward i).obj G).val.obj (op U) →ₗ[Γ(X, U)]
          ((Scheme.Modules.pushforward i).obj H).val.obj (op U))
    (hb : ∀ (U V : X.Opens) (h : V ≤ U)
      (a : F.val.obj (op (i ⁻¹ᵁ U))) (c : G.val.obj (op (i ⁻¹ᵁ U))),
      H.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op (b U a c) =
        b V (F.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op a)
          (G.val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op c)) :
    ∃ d : ∀ V : Z.Opens, F.val.obj (op V) →ₗ[Γ(Z, V)]
        G.val.obj (op V) →ₗ[Γ(Z, V)] H.val.obj (op V),
      (∀ (U V : Z.Opens) (h : V ≤ U) (a : F.val.obj (op U))
        (c : G.val.obj (op U)), H.val.map (homOfLE h).op (d U a c) =
          d V (F.val.map (homOfLE h).op a) (G.val.map (homOfLE h).op c)) ∧
      ∀ (U : X.Opens) (a : F.val.obj (op (i ⁻¹ᵁ U)))
        (c : G.val.obj (op (i ⁻¹ᵁ U))), d (i ⁻¹ᵁ U) a c = b U a c := by
  let b' := fun U a c ↦ b U a c
  let d := rawPairing i F G H b'
  have he (U : X.Opens) (a : F.val.obj (op (i ⁻¹ᵁ U)))
      (c : G.val.obj (op (i ⁻¹ᵁ U))) : d (i ⁻¹ᵁ U) a c = b U a c :=
    rawPairing_eq i F G H b' hb U a c
  have hn := rawPairing_natural i F G H b' hb
  have hs := pairing_smul i F G H d hn (fun U r a c ↦ by
    erw [he, he]
    exact congrArg (fun f ↦ f c) ((b U).map_smul r a))
  have hs' := pairing_smul i G F H (fun V c a ↦ d V a c)
    (fun U V h c a ↦ hn U V h a c) (fun U r c a ↦ by
      erw [he, he]
      exact (b U a).map_smul r c)
  have ha (V : Z.Opens) (a a' : F.val.obj (op V)) (c : G.val.obj (op V)) :
      d V (a + a') c = d V a c + d V a' c := by
    obtain ⟨U, rfl⟩ := exists_preimage_open i V
    erw [he, he, he]
    exact congrArg (fun f ↦ f c) ((b U).map_add a a')
  have ha' (V : Z.Opens) (a : F.val.obj (op V)) (c c' : G.val.obj (op V)) :
      d V a (c + c') = d V a c + d V a c' := by
    obtain ⟨U, rfl⟩ := exists_preimage_open i V
    erw [he, he, he]
    exact (b U a).map_add c c'
  let D (V : Z.Opens) : F.val.obj (op V) →ₗ[Γ(Z, V)]
      G.val.obj (op V) →ₗ[Γ(Z, V)] H.val.obj (op V) :=
    { toFun := fun a ↦ { toFun := d V a, map_add' := ha' V a, map_smul' := fun r c ↦ hs' V r c a }
      map_add' := fun a a' ↦ LinearMap.ext (ha V a a')
      map_smul' := fun r a ↦ LinearMap.ext (hs V r a) }
  exact ⟨D, hn, he⟩

private theorem descend_unit {X Z : Scheme.{u}} (i : Z ⟶ X) (C : Z.Modules)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pushforward i).obj C) :
    ∃ d : SheafOfModules.unit Z.ringCatSheaf ⟶ C,
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward i).map d = a := by
  let s : C.sections := C.val.sectionsMk
    (fun V ↦ C.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op
      (a.val.app (op ⊤) (1 : Γ(X, ⊤)))) (by
        intro V W f
        simp only [← PresheafOfModules.map_comp_apply]
        rfl)
  refine ⟨C.unitHomEquiv.symm s, ?_⟩
  apply (((Scheme.Modules.pushforward i).obj C).unitHomEquiv).injective
  erw [← SheafOfModules.pushforwardSections_unitHomEquiv,
    Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change C.val.map (homOfLE le_top).op (a.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    a.val.app U (1 : X.ringCatSheaf.obj.obj U)
  have h := PresheafOfModules.naturality_apply a.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))
  change a.val.app U
      (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    C.val.map (homOfLE le_top).op (a.val.app (op ⊤) (1 : Γ(X, ⊤))) at h
  simpa only [map_one] using h.symm

private theorem reflect_heq {I : Type*} {M N : I → Type*}
    (f : ∀ k, M k → N k) (hf : ∀ k, Function.Injective (f k))
    {j k : I} (hjk : j = k) {a : M j} {b : M k} (h : HEq (f j a) (f k b)) :
    HEq a b := by
  subst k
  exact heq_of_eq (hf j (eq_of_heq h))

/-- A graded algebra on modules supported on a closed subscheme descends through
specified pushforward isomorphisms, including the structure-sheaf unit.
Source: Stacks Project, Divisors, Tag 0630, paragraph preceding
`definition-conormal-sheaf`, and Modules, Lemma 08KS.
(blueprint: lem-pur-closed-immersion-graded-algebra-descent).

Proof: The projection formula for a closed immersion identifies the pushforward
of `C_m ⊗ C_n` with `i_*C_m ⊗ i_*C_n`: on stalks on the closed subset both are
modules over the quotient local ring, and off it both vanish. Transport the
multiplication through the specified isomorphisms and this tensor comparison,
then lift the resulting morphisms by fully faithful pushforward. Transport the
unit by the equivalence between modules annihilated by the kernel ideal and
modules on the closed subscheme. The induced unit has the stated composite with
`O_X → i_*O_Z`. Faithfulness gives associativity, commutativity and the unit laws.
The tensor comparison sends a pair of sections to their tensor, so evaluating
its multiplication gives exactly the displayed equality. These constructions
also apply to zero modules and to the empty closed subscheme. -/
theorem exists_gradedAlgebra_closed_descent {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (B : ℕ → X.Modules) (C : ℕ → Z.Modules)
    (e : ∀ n, (Scheme.Modules.pushforward i).obj (C n) ≅ B n)
    (A : GradedSheafAlgebra B) :
    ∃ D : GradedSheafAlgebra C,
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward i).map D.unit) ≫ (e 0).hom = A.unit ∧
      ∀ (m n : ℕ) (U : X.Opens)
        (a : (C m).val.obj (op (i ⁻¹ᵁ U))) (b : (C n).val.obj (op (i ⁻¹ᵁ U))),
        (e (m + n)).hom.val.app (op U) (D.mul m n (i ⁻¹ᵁ U) a b) =
          A.mul m n U ((e m).hom.val.app (op U) a) ((e n).hom.val.app (op U) b) := by
  classical
  let E (n : ℕ) (U : X.Opens) :=
    ((SheafOfModules.evaluation (R := X.ringCatSheaf) (op U)).mapIso (e n)).toLinearEquiv
  let b (m n : ℕ) (U : X.Opens) :=
    ((A.mul m n U).compl₁₂ ((e m).hom.val.app (op U)).hom
      ((e n).hom.val.app (op U)).hom).compr₂ ((e (m + n)).inv.val.app (op U)).hom
  have hb (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
      (a : (C m).val.obj (op (i ⁻¹ᵁ U))) (c : (C n).val.obj (op (i ⁻¹ᵁ U))) :
      (C (m + n)).val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op
        (b m n U a c) =
      b m n V
        ((C m).val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op a)
        ((C n).val.map ((TopologicalSpace.Opens.map i.base).map (homOfLE h)).op c) := by
    change ((Scheme.Modules.pushforward i).obj (C (m + n))).val.map (homOfLE h).op
        ((e (m + n)).inv.val.app (op U)
          (A.mul m n U ((e m).hom.val.app (op U) a) ((e n).hom.val.app (op U) c))) =
      (e (m + n)).inv.val.app (op V)
        (A.mul m n V
          ((e m).hom.val.app (op V)
            (((Scheme.Modules.pushforward i).obj (C m)).val.map (homOfLE h).op a))
          ((e n).hom.val.app (op V)
            (((Scheme.Modules.pushforward i).obj (C n)).val.map (homOfLE h).op c)))
    rw [← PresheafOfModules.naturality_apply, A.naturality,
      PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  have hex (m n : ℕ) := descend_bilinear i (C m) (C n) (C (m + n)) (b m n) (hb m n)
  choose d hn hd using hex
  have hm (m n : ℕ) (U : X.Opens)
      (a : (C m).val.obj (op (i ⁻¹ᵁ U))) (c : (C n).val.obj (op (i ⁻¹ᵁ U))) :
      (e (m + n)).hom.val.app (op U) (d m n (i ⁻¹ᵁ U) a c) =
        A.mul m n U ((e m).hom.val.app (op U) a) ((e n).hom.val.app (op U) c) := by
    rw [hd]
    exact (E (m + n) U).apply_symm_apply _
  obtain ⟨d₀, hu₀⟩ := descend_unit i (C 0) (A.unit ≫ (e 0).inv)
  have hu : (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward i).map d₀) ≫ (e 0).hom = A.unit := by
    rw [hu₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hu₁ (U : X.Opens) :
      (e 0).hom.val.app (op U) (d₀.val.app (op (i ⁻¹ᵁ U)) (1 : Γ(Z, i ⁻¹ᵁ U))) =
        A.unit.val.app (op U) (1 : Γ(X, U)) := by
    have h := congrArg (fun f ↦ f.val.app (op U) (1 : Γ(X, U))) hu
    change (e 0).hom.val.app (op U)
      (d₀.val.app (op (i ⁻¹ᵁ U)) ((i.app U).hom 1)) = _ at h
    simpa only [map_one] using h
  let D : GradedSheafAlgebra C :=
    { mul := d
      unit := d₀
      naturality := hn
      assoc := by
        intro l m n V a c t
        obtain ⟨U, rfl⟩ := exists_preimage_open i V
        apply reflect_heq (fun k ↦ (e k).hom.val.app (op U))
          (fun k ↦ (E k U).injective) (Nat.add_assoc l m n)
        simp only [hm]
        exact A.assoc l m n U _ _ _
      comm := by
        intro m n V a c
        obtain ⟨U, rfl⟩ := exists_preimage_open i V
        apply reflect_heq (fun k ↦ (e k).hom.val.app (op U))
          (fun k ↦ (E k U).injective) (Nat.add_comm m n)
        simp only [hm]
        exact A.comm m n U _ _
      one_mul := by
        intro n V a
        obtain ⟨U, rfl⟩ := exists_preimage_open i V
        apply reflect_heq (fun k ↦ (e k).hom.val.app (op U))
          (fun k ↦ (E k U).injective) (Nat.zero_add n)
        rw [hm, hu₁]
        exact A.one_mul n U _
      mul_one := by
        intro n V a
        obtain ⟨U, rfl⟩ := exists_preimage_open i V
        apply reflect_heq (fun k ↦ (e k).hom.val.app (op U))
          (fun k ↦ (E k U).injective) (Nat.add_zero n)
        rw [hm, hu₁]
        exact A.mul_one n U _ }
  exact ⟨D, hu, hm⟩

end AlgebraicGeometry
