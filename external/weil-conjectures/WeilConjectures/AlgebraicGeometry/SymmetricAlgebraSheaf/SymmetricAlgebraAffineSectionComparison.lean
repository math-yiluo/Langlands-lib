/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineComparisonMap
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange

/-! # Sectionwise comparison before sheafification

Source: Stacks Project, Constructions, Lemma 01LN; Schemes, Lemma 01I8;
Algebra, Lemma 0C6F.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite CategoryTheory.Functor
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

open scoped TensorProduct

/-- The symmetric algebras of linearly equivalent modules are isomorphic. -/
noncomputable def symmetricCongr {R M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N := by
  let f := SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp e.toLinearMap)
  let g := SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp e.symm.toLinearMap)
  apply AlgEquiv.ofAlgHom f g
  · apply SymmetricAlgebra.algHom_ext
    ext x
    simp [f, g]
  · apply SymmetricAlgebra.algHom_ext
    ext x
    simp [f, g]

/-- `symmetricCongr` sends a generator to the generator of its image. -/
theorem symmetricCongr_ι {R M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (m : M) :
    symmetricCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) := by
  exact SymmetricAlgebra.lift_ι_apply _ _

/-- Affine restriction of the sectionwise symmetric algebra is extension of scalars.
Source: Stacks Project, Constructions, Lemma 01LN; Algebra, Lemma 0C6F.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).

Proof: quasi-coherent affine-section base change gives the module equivalence after
swapping the tensor factors. Symmetric algebra base change and the symmetric-algebra
lifts of this equivalence and its inverse give the required linear equivalence.
Symmetric-algebra induction identifies its pure tensor formula with restriction. -/
theorem exists_sectionTensorEquiv {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {U W : X.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hUW : U ≤ W) :
    letI : Algebra Γ(X, W) Γ(X, U) :=
      (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
    ∃ e : Γ(X, U) ⊗[Γ(X, W)] sections F (op W) ≃ₗ[Γ(X, U)] sections F (op U),
      ∀ (r : Γ(X, U)) (a : sections F (op W)),
        e (r ⊗ₜ[Γ(X, W)] a) = r • restriction F (homOfLE hUW).op a := by
  classical
  let : Algebra Γ(X, W) Γ(X, U) :=
    (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
  let : Module Γ(X, W) Γ(F, U) :=
    Module.compHom _ (X.presheaf.map (homOfLE hUW).op).hom
  obtain ⟨c, hc, hs, ht⟩ := Scheme.Modules.quasiCoherent_affine_section_baseChange
    X F ⟨U, hU⟩ ⟨W, hW⟩ hUW
  let d : Γ(X, U) ⊗[Γ(X, W)] Γ(F, W) →ₗ[Γ(X, U)] Γ(F, U) :=
    { toFun := fun t ↦ c (TensorProduct.comm Γ(X, W) Γ(X, U) Γ(F, W) t)
      map_add' := by intro x y; simp
      map_smul' := by
        intro r t
        simpa only [TensorProduct.comm_symm, TensorProduct.comm_comm, RingHom.id_apply]
          using hs r (TensorProduct.comm Γ(X, W) Γ(X, U) Γ(F, W) t) }
  let e := LinearEquiv.ofBijective d
    (hc.comp (TensorProduct.comm Γ(X, W) Γ(X, U) Γ(F, W)).bijective)
  let β : sections F (op W) →ₐ[Γ(X, W)]
      SymmetricAlgebra Γ(X, U) (Γ(X, U) ⊗[Γ(X, W)] Γ(F, W)) :=
    SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι Γ(X, U) _).restrictScalars Γ(X, W)).comp
        (TensorProduct.mk Γ(X, W) Γ(X, U) Γ(F, W) 1))
  have hβ (m : Γ(F, W)) : β (SymmetricAlgebra.ι Γ(X, W) _ m) =
      SymmetricAlgebra.ι Γ(X, U) _ (1 ⊗ₜ[Γ(X, W)] m) := by
    exact SymmetricAlgebra.lift_ι_apply _ _
  let k := AlgEquiv.ofBijective
    (AlgHom.liftEquiv Γ(X, W) Γ(X, U) _ _ β)
    (SymmetricAlgebra.baseChange_bijective β hβ)
  let q := symmetricCongr e
  have hq (a : sections F (op W)) :
      q (β a) = restriction F (homOfLE hUW).op a := by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [AlgHom.commutes, restriction_algebraMap]
      change q (algebraMap Γ(X, U) _ (X.presheaf.map (homOfLE hUW).op r)) = _
      exact q.commutes _
    | ι m =>
      rw [hβ, symmetricCongr_ι, restriction_ι]
      change SymmetricAlgebra.ι Γ(X, U) _ (c (m ⊗ₜ[Γ(X, W)] 1)) = _
      rw [ht, one_smul]
      rfl
    | mul a b ha hb => simp_all
    | add a b ha hb => simp_all
  refine ⟨(k.trans q).toLinearEquiv, ?_⟩
  intro r a
  change q (AlgHom.liftEquiv Γ(X, W) Γ(X, U) _ _ β (r ⊗ₜ[Γ(X, W)] a)) = _
  rw [AlgHom.liftEquiv_tmul, _root_.map_smul, hq]

private theorem exists_tildeTensorEquiv {R : CommRingCat.{u}} (M : ModuleCat R)
    (V : (Spec R).affineOpens) :
    ∃ e : Γ(Spec R, V.1) ⊗[R] M ≃ₗ[Γ(Spec R, V.1)] Γ(tilde M, V.1),
      ∀ (r : Γ(Spec R, V.1)) (m : M),
        e (r ⊗ₜ[R] m) = r • (show Γ(tilde M, V.1) from tilde.toOpen M V.1 m) := by
  classical
  let S := Γ(Spec R, V.1)
  let A := Γ(Spec R, ⊤)
  let T := tilde M
  let : Algebra A S := ((Spec R).presheaf.map V.1.leTop.op).hom.toAlgebra
  let : Module A Γ(T, V.1) :=
    Module.compHom _ ((Spec R).presheaf.map V.1.leTop.op).hom
  obtain ⟨c, hc, hs, ht⟩ := Scheme.Modules.quasiCoherent_affine_section_baseChange
    (Spec R) T V ⟨⊤, isAffineOpen_top (Spec R)⟩ le_top
  let d : S ⊗[A] Γ(T, ⊤) →ₗ[S] Γ(T, V.1) :=
    { toFun := fun t ↦ c (TensorProduct.comm A S Γ(T, ⊤) t)
      map_add' := by intro x y; simp
      map_smul' := by
        intro r t
        simpa only [A, S, TensorProduct.comm_symm, TensorProduct.comm_comm, RingHom.id_apply]
          using hs r (TensorProduct.comm Γ(Spec R, ⊤) Γ(Spec R, V.1) Γ(T, ⊤) t) }
  let e₁ := LinearEquiv.ofBijective d (hc.comp (TensorProduct.comm A S Γ(T, ⊤)).bijective)
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A Γ(T, ⊤) := inferInstance
  have : TensorProduct.CompatibleSMul R A S Γ(T, ⊤) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S Γ(T, ⊤)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective
  let e₂ := (TensorProduct.equivOfCompatibleSMul R A S S Γ(T, ⊤)).symm
  let e₃ := (tilde.isoTop M).toLinearEquiv.baseChange R S _ _
  refine ⟨e₃.trans (e₂.trans e₁), ?_⟩
  intro r m
  change c (tilde.toOpen M ⊤ m ⊗ₜ[A] r) = _
  rw [ht]
  congr 1

private theorem exists_sectionEquiv {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (V : (Spec Γ(X, W)).affineOpens) :
    ∃ g : sections F (op (hW.fromSpec ''ᵁ V.1)) ≃+
        Γ(tilde (R := Γ(X, W)) (ModuleCat.of Γ(X, W) (sections F (op W))), V.1),
      ∀ (r : Γ(X, hW.fromSpec ''ᵁ V.1)) (a : sections F (op W)),
        g (r • restriction F (homOfLE (hW.fromSpec_image_le V.1)).op a) =
          (hW.fromSpec.appIso V.1).hom r •
            (show Γ(tilde (R := Γ(X, W))
              (ModuleCat.of Γ(X, W) (sections F (op W))), V.1) from
              tilde.toOpen (ModuleCat.of Γ(X, W) (sections F (op W))) V.1 a) := by
  classical
  let R := Γ(X, W)
  let U := hW.fromSpec ''ᵁ V.1
  let S := Γ(X, U)
  let S' := Γ(Spec R, V.1)
  let A := ModuleCat.of R (sections F (op W))
  let : Algebra R S := (X.presheaf.map (homOfLE (hW.fromSpec_image_le V.1)).op).hom.toAlgebra
  obtain ⟨ell, hell⟩ := exists_sectionTensorEquiv F (V.2.image_of_isOpenImmersion hW.fromSpec)
    hW (hW.fromSpec_image_le V.1)
  obtain ⟨β, hβ⟩ := exists_tildeTensorEquiv A V
  have hscalar (r : R) :
      (hW.fromSpec.appIso V.1).hom
        (X.presheaf.map (homOfLE (hW.fromSpec_image_le V.1)).op r) = algebraMap R S' r := by
    have h := congrArg (fun f ↦ f r) (hW.ΓSpecIso_inv_map_appIso_inv V.1)
    change (hW.fromSpec.appIso V.1).inv (algebraMap R S' r) = _ at h
    rw [← h, Iso.inv_hom_id_apply]
  let f : S ≃ₐ[R] S' :=
    { (hW.fromSpec.appIso V.1).commRingCatIsoToRingEquiv with
      commutes' := hscalar }
  let t := TensorProduct.congr f.toLinearEquiv (LinearEquiv.refl R A)
  refine ⟨ell.toAddEquiv.symm.trans (t.toAddEquiv.trans β.toAddEquiv), ?_⟩
  intro r a
  change β (t (ell.symm (r • restriction F _ a))) = _
  -- Transport the pure-tensor equality directly, avoiding rewrite search through the equivalences.
  have he : ell.symm (r • restriction F _ a) = r ⊗ₜ[R] a :=
    (congrArg ell.symm (hell r a)).symm.trans (ell.symm_apply_apply _)
  exact (congrArg (fun z ↦ β (t z)) he).trans (hβ (f r) a)

private theorem section_induction {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hUW : U ≤ W)
    (P : sections F (op U) → Prop) (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (r : Γ(X, U)) (a : sections F (op W)),
      P (r • restriction F (homOfLE hUW).op a)) : ∀ x, P x := by
  classical
  let : Algebra Γ(X, W) Γ(X, U) :=
    (X.presheaf.map (homOfLE hUW).op).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_sectionTensorEquiv F hU hW hUW
  intro x
  by_cases hx : x = 0
  · subst x
    exact hzero
  clear hx
  obtain ⟨t, rfl⟩ := e.surjective x
  induction t using TensorProduct.inductionOn with
  | tmul r a => rw [he]; exact hgen r a
  | add t t' ht ht' => rw [_root_.map_add]; exact hadd _ _ ht ht'

private theorem restriction_smul {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : X.presheaf.obj U) (a : sections F U) :
    restriction F i (r • a) = X.presheaf.map i r • restriction F i a := by
  rw [Algebra.smul_def, map_mul, restriction_algebraMap, Algebra.smul_def]

private theorem restriction_comp {X : Scheme.{u}} (F : X.Modules)
    {U V Z : X.Opensᵒᵖ} (i : U ⟶ V) (j : V ⟶ Z) (a : sections F U) :
    restriction F j (restriction F i a) = restriction F (i ≫ j) a := by
  exact (CategoryTheory.congr_fun ((presheaf F).map_comp i j) a).symm

/-- The restricted sectionwise symmetric algebra maps to the tilde of its affine sections,
on the affine basis, bijectively on each affine open, with composite the unit.
Source: Stacks Project, Constructions, Lemma 01LN; Algebra, Lemma 0C6F;
Schemes, Lemma 01I8.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).

Proof: put R = O_X(W), M = F(W), A = Sym_R(M). For an affine open V of Spec R,
its image U in X is affine and contained in W. Quasi-coherent section base change identifies
F(U) with O_X(U) tensor_R M. Symmetric algebra base change identifies Sym(F(U)) with
O_X(U) tensor_R A. Apply quasi-coherent affine section base change to tilde(A) on
V contained in top, using isoTop to identify its global sections with A. The chart
structure-sheaf isomorphism then identifies this tensor product with tilde(A)(V).
These identifications send
r tensor a to r times restriction(a), hence commute with restrictions between affine opens.
They therefore give a natural transformation on the full affine basis. Each component
is the displayed composite of isomorphisms, so it is bijective. Its composite with the
affine comparison equals the unit: on 1 tensor a this is affineComparison_toOpen, and
linearity extends the equality to all tensors. This uses no finiteness or separatedness. -/
theorem exists_affineSectionComparison {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) :
    let B : (Spec Γ(X, W)).affineOpens → (Spec Γ(X, W)).Opens := Subtype.val
    ∃ γ : (inducedFunctor B).op ⋙ hW.fromSpec.opensFunctor.op ⋙ presheaf F ⋙
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}) ⟶
      (inducedFunctor B).op ⋙
        (Scheme.Modules.toPresheaf (Spec Γ(X, W))).obj
          (tilde (R := Γ(X, W)) (ModuleCat.of Γ(X, W) (sections F (op W)))),
      (∀ V : (Spec Γ(X, W)).affineOpens, Function.Bijective (γ.app (op V))) ∧
      (∀ V : (Spec Γ(X, W)).affineOpens,
        γ.app (op V) ≫
          ((Scheme.Modules.toPresheaf (Spec Γ(X, W))).map
            (affineComparison F hW)).app (op V.1) =
          (whiskerLeft hW.fromSpec.opensFunctor.op
            (whiskerRight (toSheafify (Opens.grothendieckTopology X) (presheaf F))
              (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}))).app
            (op V.1)) := by
  classical
  let B : (Spec Γ(X, W)).affineOpens → (Spec Γ(X, W)).Opens := Subtype.val
  let A := ModuleCat.of Γ(X, W) (sections F (op W))
  let T := tilde A
  choose g hg using exists_sectionEquiv F hW
  let γ : (inducedFunctor B).op ⋙ hW.fromSpec.opensFunctor.op ⋙ presheaf F ⋙
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}) ⟶
      (inducedFunctor B).op ⋙ (Scheme.Modules.toPresheaf (Spec Γ(X, W))).obj T :=
    { app V := AddCommGrpCat.ofHom (g V.unop).toAddMonoidHom
      naturality := by
        intro V V' j
        ext x
        change g V'.unop
            (restriction F (hW.fromSpec.opensFunctor.op.map ((inducedFunctor B).op.map j)) x) =
          T.presheaf.map ((inducedFunctor B).op.map j) (g V.unop x)
        refine section_induction F (V.unop.2.image_of_isOpenImmersion hW.fromSpec)
          hW (hW.fromSpec_image_le V.unop.1)
          (fun y ↦ g V'.unop
            (restriction F (hW.fromSpec.opensFunctor.op.map ((inducedFunctor B).op.map j)) y) =
            T.presheaf.map ((inducedFunctor B).op.map j) (g V.unop y)) ?_ ?_ ?_ x
        · simp only [_root_.map_zero]
        · intro x y hx hy
          simp only [_root_.map_add, hx, hy]
        · intro r a
          -- Explicit transports avoid unfolding section-module structures during rewriting.
          let i := (inducedFunctor B).op.map j
          let k := hW.fromSpec.opensFunctor.op.map i
          have hi :
              (homOfLE (hW.fromSpec_image_le V.unop.1)).op ≫
                  k =
                (homOfLE (hW.fromSpec_image_le V'.unop.1)).op := Subsingleton.elim _ _
          have hr := (restriction_comp F
            (homOfLE (hW.fromSpec_image_le V.unop.1)).op k a).trans
              (congrArg (fun l ↦ restriction F l a) hi)
          have ht := congrArg (fun f ↦ f a)
            (tilde.toOpen_res A V.unop.1 V'.unop.1 ((inducedFunctor B).map j.unop))
          change T.presheaf.map i
            (tilde.toOpen A V.unop.1 a) = tilde.toOpen A V'.unop.1 a at ht
          have hs := CategoryTheory.congr_fun (hW.fromSpec.appIso_hom_naturality i) r
          calc
            g V'.unop (restriction F k
                (r • restriction F (homOfLE (hW.fromSpec_image_le V.unop.1)).op a)) =
                g V'.unop ((show Γ(X, hW.fromSpec ''ᵁ V'.unop.1) from X.presheaf.map k r) •
                  restriction F (homOfLE (hW.fromSpec_image_le V'.unop.1)).op a) :=
              congrArg (g V'.unop) ((restriction_smul F k r _).trans
                (congrArg (fun (z : sections F (op (hW.fromSpec ''ᵁ V'.unop.1))) ↦
                  (show Γ(X, hW.fromSpec ''ᵁ V'.unop.1) from X.presheaf.map k r) • z) hr))
            _ = (hW.fromSpec.appIso V'.unop.1).hom (X.presheaf.map k r) •
                (show Γ(T, V'.unop.1) from tilde.toOpen A V'.unop.1 a) := hg V'.unop _ a
            _ = (show Γ(Spec Γ(X, W), V'.unop.1) from
                  (Spec Γ(X, W)).presheaf.map i ((hW.fromSpec.appIso V.unop.1).hom r)) •
                (show Γ(T, V'.unop.1) from
                  T.presheaf.map i (tilde.toOpen A V.unop.1 a)) :=
              congrArg₂ (fun (s : Γ(Spec Γ(X, W), V'.unop.1)) (z : Γ(T, V'.unop.1)) ↦
                s • z) hs ht.symm
            _ = T.presheaf.map i ((hW.fromSpec.appIso V.unop.1).hom r •
                (show Γ(T, V.unop.1) from tilde.toOpen A V.unop.1 a)) :=
              (T.val.map_smul i _ _).symm
            _ = T.presheaf.map i
                (g V.unop (r • restriction F (homOfLE (hW.fromSpec_image_le V.unop.1)).op a)) :=
              congrArg (T.presheaf.map i) (hg V.unop r a).symm }
  refine ⟨γ, ?_, ?_⟩
  · intro V
    exact (g V).bijective
  · intro V
    ext x
    change (affineComparison F hW).app V.1 (g V x) =
      sectionMap F (op (hW.fromSpec ''ᵁ V.1)) x
    refine section_induction F (V.2.image_of_isOpenImmersion hW.fromSpec)
      hW (hW.fromSpec_image_le V.1)
      (fun y ↦ (affineComparison F hW).app V.1 (g V y) =
        sectionMap F (op (hW.fromSpec ''ᵁ V.1)) y) ?_ ?_ ?_ x
    · simp only [_root_.map_zero]
    · intro x y hx hy
      simp only [_root_.map_add, hx, hy]
    · intro r a
      rw [hg]
      have hs := Scheme.Modules.Hom.app_smul (affineComparison F hW)
        ((hW.fromSpec.appIso V.1).hom r) (tilde.toOpen A V.1 a)
      change (affineComparison F hW).app V.1
          ((hW.fromSpec.appIso V.1).hom r • (show Γ(T, V.1) from tilde.toOpen A V.1 a)) =
        (hW.fromSpec.appIso V.1).inv ((hW.fromSpec.appIso V.1).hom r) •
          (show Γ((algebra F).toModule, hW.fromSpec ''ᵁ V.1) from
            (affineComparison F hW).app V.1 (tilde.toOpen A V.1 a)) at hs
      rw [Iso.hom_inv_id_apply] at hs
      rw [hs]
      change r • (show Γ((algebra F).toModule, hW.fromSpec ''ᵁ V.1) from
        (affineComparison F hW).app V.1 (tilde.toOpen A V.1 a)) =
        sectionLinearMap F (op (hW.fromSpec ''ᵁ V.1))
          (r • restriction F (homOfLE (hW.fromSpec_image_le V.1)).op a)
      rw [LinearMap.map_smul]
      congr 1
      rw [affineComparison_toOpen]
      change (Scheme.Modules.presheaf ((algebra F).toModule : X.Modules)).map
          (hW.fromSpec.opensFunctor.map V.1.leTop).op
          ((Scheme.Modules.presheaf ((algebra F).toModule : X.Modules)).map
            (homOfLE (hW.fromSpec_image_le ⊤)).op (sectionMap F (op W) a)) =
        sectionMap F (op (hW.fromSpec ''ᵁ V.1))
          (restriction F (homOfLE (hW.fromSpec_image_le V.1)).op a)
      rw [← Functor.map_comp_apply]
      have hi : (homOfLE (hW.fromSpec_image_le ⊤)).op ≫
          (hW.fromSpec.opensFunctor.map V.1.leTop).op =
          (homOfLE (hW.fromSpec_image_le V.1)).op := Subsingleton.elim _ _
      rw [hi]
      exact (CategoryTheory.congr_fun
        ((toSheafify (Opens.grothendieckTopology X) (presheaf F)).naturality
          (homOfLE (hW.fromSpec_image_le V.1)).op) a).symm

end AlgebraicGeometry.SymmetricAlgebraSheaf
