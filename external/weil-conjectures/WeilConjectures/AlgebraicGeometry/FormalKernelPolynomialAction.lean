/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalSystemsKernelReesFinite
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedPolynomialCover

/-! # A polynomial algebra acting on the successive formal kernels

Source: Stacks Project, Cohomology of Schemes, proofs of Lemmas 0884 and 087Z.
(blueprint: lem-weil-pbc-formal-kernel-polynomial-action).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private def gradedActHom {X : Scheme.{u}} {B K : ℕ → X.Modules}
    {G : GradedSheafAlgebra B} (M : GradedSheafModule G K)
    (k m : ℕ) (e : ∀ U : X.Opens, (B k).val.obj (op U))
    (he : ∀ U V (h : V ≤ U), (B k).val.map (homOfLE h).op (e U) = e V) :
    K m ⟶ K (k + m) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (M.act k m U.unop (e U.unop))
      naturality := by
        intro U V h
        ext x
        change M.act k m V.unop (e V.unop) ((K m).val.map h x) =
          (K (k + m)).val.map h (M.act k m U.unop (e U.unop) x)
        have hn := M.naturality k m U.unop V.unop (leOfHom h.unop) (e U.unop) x
        rw [he] at hn
        convert hn.symm using 1 <;> rfl }

private theorem transport_sections {X : Scheme.{u}} {P Q : X.Modules}
    (h : P = Q) (U : X.Opens) (x : P.val.obj (op U)) :
    HEq ((eqToHom h).val.app (op U) x) x := by
  subst Q
  rfl

private theorem hom_heq_of_app_heq {X : Scheme.{u}} {P Q R : X.Modules}
    (h : Q = R) (a : P ⟶ Q) (b : P ⟶ R)
    (hab : ∀ (U : X.Opens) (x : P.val.obj (op U)),
      HEq (a.val.app (op U) x) (b.val.app (op U) x)) : HEq a b := by
  subst R
  apply heq_of_eq
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact eq_of_heq (hab U.unop x)

private theorem act_heq {X : Scheme.{u}} {B K : ℕ → X.Modules}
    {G : GradedSheafAlgebra B} (M : GradedSheafModule G K)
    (k : ℕ) {m n : ℕ} (h : m = n) (U : X.Opens)
    (a : (B k).val.obj (op U)) (x : (K m).val.obj (op U))
    (y : (K n).val.obj (op U)) (hxy : HEq x y) :
    HEq (M.act k m U a x) (M.act k n U a y) := by
  subst n
  cases hxy
  rfl

/-- The successive kernels are locally generated in degree zero over a polynomial algebra
in finitely many degree-one variables over the base ring. This is the algebraic input to
graded Serre vanishing; it asserts no cohomological vanishing and needs no ample module.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0884, first paragraph,
and Lemma 087Z (blueprint: lem-weil-pbc-formal-kernel-polynomial-action).

Proof:
1. Apply formalSystems_kernel_rees_finite to obtain the associated graded algebra and
its graded action on the kernels, with finite local degree-zero generators.
2. Choose finitely many generators of I by Noetherianity and apply
formalAssociatedGraded_polynomial_cover to this algebra and these generators. It evaluates
homogeneous polynomials compatibly with restriction, addition, multiplication and scalars;
it locally spans any finite family of sections in one graded algebra piece.
3. Act by these evaluated sections. Restriction compatibility constructs a sheaf
morphism, followed by the identification k+m=m+k. Bilinearity proves additivity,
module associativity proves the composition identity, and linearity of the unit together
with the module unit law proves the scalar formula.
4. Write a kernel section locally as the finite sum supplied by the Rees theorem.
Shrink again so all its coefficients lie in the span of polynomial evaluations.
Restrict the finite sum using naturality. For each summand, span induction and the
linearity of the action put it in the span of polynomial actions on the original
degree-zero generators; closure under finite sums finishes the proof. -/
theorem formalKernel_polynomial_action
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of A))
    (F : CoherentFormalModule X
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) :
    ∃ r : ℕ,
      ∃ mu : ∀ (m k : ℕ), MvPolynomial.homogeneousSubmodule (Fin r) A k →
        (formalKernelPiece F m ⟶ formalKernelPiece F (m + k)),
      (∀ (m k : ℕ) (b b' : MvPolynomial.homogeneousSubmodule (Fin r) A k),
        mu m k (b + b') = mu m k b + mu m k b') ∧
      (∀ (m k l : ℕ) (b : MvPolynomial.homogeneousSubmodule (Fin r) A k)
        (b' : MvPolynomial.homogeneousSubmodule (Fin r) A l),
        HEq (mu m l b' ≫ mu (m + l) k b)
          (mu m (k + l) ⟨b.val * b'.val, b.property.mul b'.property⟩)) ∧
      (∀ (m : ℕ) (a : A) (U : X.Opens) (t : (formalKernelPiece F m).val.obj (op U)),
        HEq ((mu m 0 ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩).val.app (op U) t)
          ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t)) ∧
      (∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
        ∃ (s : ℕ) (t : Fin s → (formalKernelPiece F 0).val.obj (op U)),
          ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U)
            (v : (formalKernelPiece F m).val.obj (op V)) (y : X), y ∈ V →
            ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
              (formalKernelPiece F m).val.map (homOfLE hWV).op v ∈
                Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                  {z | ∃ (i : Fin s) (b : MvPolynomial.homogeneousSubmodule (Fin r) A m),
                    HEq z ((mu 0 m b).val.app (op W)
                      ((formalKernelPiece F 0).val.map
                        (homOfLE (hWV.trans hVU)).op (t i)))}) := by
  classical
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  obtain ⟨_, G, hunit, hmul, M, hgen, _⟩ := formalSystems_kernel_rees_finite J F
  obtain ⟨r, generators, hgenerators⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  obtain ⟨e, henat, headd, hemul, heconst, hespan⟩ :=
    formalAssociatedGraded_polynomial_cover I f generators hgenerators G hunit hmul
  let K := formalKernelPiece F
  let mu (m k : ℕ) (b : MvPolynomial.homogeneousSubmodule (Fin r) A k) :
      K m ⟶ K (m + k) :=
    gradedActHom M k m (fun U ↦ e k U b) (fun U V h ↦ henat k U V h b) ≫
      eqToHom (congrArg K (Nat.add_comm k m))
  have happ (m k : ℕ) (b : MvPolynomial.homogeneousSubmodule (Fin r) A k)
      (U : X.Opens) (t : (K m).val.obj (op U)) :
      HEq ((mu m k b).val.app (op U) t) (M.act k m U (e k U b) t) := by
    exact transport_sections (congrArg K (Nat.add_comm k m)) U
      (M.act k m U (e k U b) t)
  refine ⟨r, mu, ?_, ?_, ?_, ?_⟩
  · intro m k b b'
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext t
    change (eqToHom (congrArg K (Nat.add_comm k m))).val.app U
        (M.act k m U.unop (e k U.unop (b + b')) t) =
      (eqToHom (congrArg K (Nat.add_comm k m))).val.app U
        (M.act k m U.unop (e k U.unop b) t) +
      (eqToHom (congrArg K (Nat.add_comm k m))).val.app U
        (M.act k m U.unop (e k U.unop b') t)
    simp only [headd, map_add, LinearMap.add_apply]
  · intro m k l b b'
    apply hom_heq_of_app_heq (congrArg K (by omega))
    intro U t
    change HEq ((mu (m + l) k b).val.app (op U)
      ((mu m l b').val.app (op U) t))
        ((mu m (k + l) ⟨b.val * b'.val, b.property.mul b'.property⟩).val.app (op U) t)
    refine (happ (m + l) k b U _).trans ?_
    refine (act_heq M k (Nat.add_comm m l) U (e k U b) _ _
      (happ m l b' U t)).trans ?_
    refine (M.assoc k l m U (e k U b) (e l U b') t).symm.trans ?_
    rw [hemul]
    exact (happ m (k + l) _ U t).symm
  · intro m a U t
    refine (happ m 0 _ U t).trans ?_
    rw [heconst]
    let c : Γ(X, U) := (X.presheaf.map (homOfLE (le_top (a := U))).op).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)
    have hu : G.unit.val.app (op U) c =
        c • G.unit.val.app (op U) (1 : X.ringCatSheaf.obj.obj (op U)) := by
      simpa using (G.unit.val.app (op U)).hom.map_smul c
        (1 : X.ringCatSheaf.obj.obj (op U))
    change HEq (M.act 0 m U (G.unit.val.app (op U) c) t) (c • t)
    rw [hu, map_smul, LinearMap.smul_apply]
    have ho := M.one_act m U t
    have hs : ∀ {i j : ℕ} (h : i = j)
        (z : (K i).val.obj (op U)) (z' : (K j).val.obj (op U)),
        HEq z z' → HEq (c • z) (c • z') := by
      intro i j h z z' hz
      subst j
      cases hz
      rfl
    exact hs (Nat.zero_add m) _ _ ho
  · intro x
    obtain ⟨U, hxU, s, t, ht⟩ := hgen x
    refine ⟨U, hxU, s, t, ?_⟩
    intro m V hVU v y hyV
    obtain ⟨W, hWV, hyW, a, ha⟩ := ht V hVU m v y hyV
    obtain ⟨Z, hZW, hyZ, hspan⟩ := hespan m W s a y hyW
    refine ⟨Z, hZW.trans hWV, hyZ, ?_⟩
    have hsum : (K m).val.map (homOfLE (hZW.trans hWV)).op v =
        ∑ i : Fin s, M.act m 0 Z
          ((formalAssociatedGradedPiece J m).val.map (homOfLE hZW).op (a i))
          ((K 0).val.map (homOfLE ((hZW.trans hWV).trans hVU)).op (t i)) := by
      calc
        _ = (K m).val.map (homOfLE hZW).op
            ((K m).val.map (homOfLE hWV).op v) := by
          exact (K m).val.map_comp_apply (homOfLE hWV).op (homOfLE hZW).op v
        _ = _ := by
          rw [eq_of_heq ha, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            _ = M.act m 0 Z
                ((formalAssociatedGradedPiece J m).val.map (homOfLE hZW).op (a i))
                ((K 0).val.map (homOfLE hZW).op
                  ((K 0).val.map (homOfLE (hWV.trans hVU)).op (t i))) := by
              convert M.naturality m 0 W Z hZW (a i)
                ((K 0).val.map (homOfLE (hWV.trans hVU)).op (t i)) using 1
            _ = _ := by
              congr 1
              exact ((K 0).val.map_comp_apply (homOfLE (hWV.trans hVU)).op
                (homOfLE hZW).op (t i)).symm
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    let L := (M.act m 0 Z).flip
      ((K 0).val.map (homOfLE ((hZW.trans hWV).trans hVU)).op (t i))
    change L _ ∈ _
    refine Submodule.span_induction (p := fun z _ ↦ L z ∈ _) ?_ ?_ ?_ ?_ (hspan i)
    · rintro z ⟨b, rfl⟩
      apply Submodule.subset_span
      exact ⟨i, b, (happ 0 m b Z _).symm⟩
    · simpa only [map_zero] using Submodule.zero_mem _
    · intro a b _ _ ha hb
      simpa only [map_add] using Submodule.add_mem _ ha hb
    · intro c a _ ha
      simpa only [map_smul] using Submodule.smul_mem _ c ha

end AlgebraicGeometry
