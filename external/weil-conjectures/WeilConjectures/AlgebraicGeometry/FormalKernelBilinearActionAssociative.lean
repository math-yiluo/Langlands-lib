/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Associativity of the formal kernel action

Source: Stacks Project, Lemma 087Z, the graded module in its affine proof.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

private theorem kernel_inclusion_injective {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) (n : ℕ) (U : X.Opens) :
    Function.Injective ((formalKernelι F n).val.app (op U)) := by
  cases n with
  | zero => exact Function.injective_id
  | succ n => exact Scheme.Modules.injective_map_kernelι U _

private theorem kernel_inclusion_heq {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) {i j : ℕ} (h : i = j)
    (U : X.Opens) (s : (formalKernelPiece F i).val.obj (op U))
    (t : (formalKernelPiece F j).val.obj (op U))
    (hst : HEq ((formalKernelι F i).val.app (op U) s)
      ((formalKernelι F j).val.app (op U) t)) : HEq s t := by
  subst j
  exact heq_of_eq (kernel_inclusion_injective F i U (eq_of_heq hst))

private theorem formal_transition_epi {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) {n r : ℕ} (h : n ≤ r) :
    Epi (F.obj.map (homOfLE h).op) := by
  induction h with
  | refl =>
    rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from Subsingleton.elim _ _,
      F.obj.map_id]
    infer_instance
  | @step r h ih =>
    obtain ⟨e, he⟩ := F.property.2.2 r
    have hepi : Epi (F.obj.map (homOfLE (Nat.le_succ r)).op) := by
      rw [← he]
      unfold formalModuleQuotientπ
      infer_instance
    have hcomp : (homOfLE (Nat.le_succ r)).op ≫ (homOfLE h).op =
        (homOfLE (Nat.le_succ_of_le h)).op := Subsingleton.elim _ _
    rw [← hcomp, F.obj.map_comp]
    exact epi_comp _ _

private theorem local_lift {X : Scheme.{u}} {P Q : X.Modules}
    (f : P ⟶ Q) [Epi f] (U : X.Opens) (s : Q.val.obj (op U))
    (p : X) (hp : p ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      ∃ t : P.val.obj (op V),
        f.val.app (op V) t = Q.val.map (homOfLE hVU).op s := by
  have hepi : Epi ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) := Functor.map_epi _ _
  have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f)).mpr hepi
  obtain ⟨V, hVU, ⟨t, ht⟩, hpV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc U s p hp
  exact ⟨V, hVU, hpV, t, ht⟩

private theorem local_lifts_three {X : Scheme.{u}} {P Q P' Q' P'' Q'' : X.Modules}
    (f : P ⟶ Q) (g : P' ⟶ Q') (h : P'' ⟶ Q'') [Epi f] [Epi g] [Epi h]
    (U : X.Opens) (a : Q.val.obj (op U)) (b : Q'.val.obj (op U))
    (t : Q''.val.obj (op U)) (p : X) (hp : p ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      ∃ (a' : P.val.obj (op V)) (b' : P'.val.obj (op V)) (t' : P''.val.obj (op V)),
        f.val.app (op V) a' = Q.val.map (homOfLE hVU).op a ∧
        g.val.app (op V) b' = Q'.val.map (homOfLE hVU).op b ∧
        h.val.app (op V) t' = Q''.val.map (homOfLE hVU).op t := by
  obtain ⟨V, hVU, hpV, a', ha⟩ := local_lift f U a p hp
  obtain ⟨W, hWV, hpW, b', hb⟩ :=
    local_lift g V (Q'.val.map (homOfLE hVU).op b) p hpV
  obtain ⟨Z, hZW, hpZ, t', ht⟩ :=
    local_lift h W (Q''.val.map (homOfLE (hWV.trans hVU)).op t) p hpW
  refine ⟨Z, hZW.trans (hWV.trans hVU), hpZ,
    P.val.map (homOfLE (hZW.trans hWV)).op a',
    P'.val.map (homOfLE hZW).op b', t', ?_, ?_, ?_⟩
  · rw [PresheafOfModules.naturality_apply, ha]
    exact (Q.val.map_comp_apply (homOfLE hVU).op
      (homOfLE (hZW.trans hWV)).op a).symm
  · rw [PresheafOfModules.naturality_apply, hb]
    rw [← Q'.val.map_comp_apply, ← Q'.val.map_comp_apply]
    rfl
  · rw [ht, ← Q''.val.map_comp_apply]
    rfl

private theorem formal_transition_comp {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) {n r s : ℕ}
    (hnr : n ≤ r) (hrs : r ≤ s) (U : X.Opens)
    (t : (F.obj.obj (op s)).val.obj (op U)) :
    (F.obj.map (homOfLE hnr).op).val.app (op U)
        ((F.obj.map (homOfLE hrs).op).val.app (op U) t) =
      (F.obj.map (homOfLE (hnr.trans hrs)).op).val.app (op U) t := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  change E.map (F.obj.map (homOfLE hnr).op)
    (E.map (F.obj.map (homOfLE hrs).op) t) = _
  rw [← ConcreteCategory.comp_apply, ← E.map_comp, ← F.obj.map_comp]
  rfl

private theorem formal_transport_heq {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) {i j : ℕ} (hij : i = j)
    (U : X.Opens) (t : (F.obj.obj (op i)).val.obj (op U)) :
    HEq ((eqToHom (congrArg (fun k ↦ F.obj.obj (op k)) hij)).val.app (op U) t) t := by
  subst j
  rfl

private theorem formal_transition_transport {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : CoherentFormalModule X I) {n i j : ℕ} (hij : i = j)
    (hni : n ≤ i) (hnj : n ≤ j) (U : X.Opens)
    (t : (F.obj.obj (op i)).val.obj (op U)) :
    (F.obj.map (homOfLE hnj).op).val.app (op U)
        ((eqToHom (congrArg (fun k ↦ F.obj.obj (op k)) hij)).val.app (op U) t) =
      (F.obj.map (homOfLE hni).op).val.app (op U) t := by
  subst j
  rfl

private theorem smul_heq {X : Scheme.{u}} (K : ℕ → X.Modules) {i j : ℕ}
    (hij : i = j) (U : X.Opens) (a : Γ(X, U))
    (s : (K i).val.obj (op U)) (t : (K j).val.obj (op U)) (hst : HEq s t) :
    HEq (a • s) (a • t) := by
  subst j
  cases hst
  rfl

private theorem sections_heq_of_local {X : Scheme.{u}} (K : ℕ → X.Modules)
    {i j : ℕ} (hij : i = j) (U : X.Opens)
    (s : (K i).val.obj (op U)) (t : (K j).val.obj (op U))
    (hlocal : ∀ p : X, p ∈ U → ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      HEq ((K i).val.map (homOfLE hVU).op s)
        ((K j).val.map (homOfLE hVU).op t)) : HEq s t := by
  subst j
  apply heq_of_eq
  classical
  choose V hVU hpV heq using fun p : U ↦ hlocal p.val p.property
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨(K i).presheaf, (K i).isSheaf⟩ V U
    (fun p ↦ homOfLE (hVU p))
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩
  · intro p
    exact eq_of_heq (heq p)

/-- A natural bilinear family with the local-lift multiplication formula is associative
for any multiplication induced by ideal-power representatives.
Source: Stacks Project, Lemma 087Z and Section 0EHN;
https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-kernel-bilinear-action-associative).

Proof: Fix l,m,n,U and coefficient sections a,b and a kernel section x. Around every
point of U shrink to lift a to I^l, b to I^m and the inclusion of x to a section t
of F_(l+m+n+1). Quotient projections and transitions are sheaf epimorphisms, so these
local simultaneous lifts exist. Let t_mid be the reduction of t to F_(m+n+1).
The action formula says that the inclusion of act(b,x) is b t_mid. Linearity of the
transition therefore makes b t a lift of that inclusion at the common highest level.
Applying the action formula again makes the inclusion of act(a,act(b,x)) equal to
a (b t). The representative multiplication hypothesis supplies c in I^(l+m) whose
image is a b and whose class is A.mul(a,b). Applying the action formula to c,x,t
makes the other inclusion equal to (a b)t. Scalar associativity equates these two
sections. The kernel inclusion is monic and hence sectionwise injective; transport
the grading index along (l+m)+n=l+(m+n) to obtain the displayed HEq. Naturality of
act and A.mul identifies these local computations with the restrictions of the two
original sections, and the sheaf uniqueness axiom glues their equality on U.
Zero degrees use the identity inclusion for K_0; empty opens and zero modules have
unique sections. No unit law or existence of act is asserted in this lemma. -/
theorem formalKernel_bilinear_action_associative {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (A : GradedSheafAlgebra (formalAssociatedGradedPiece I))
    (act : ∀ (m n : ℕ) (U : X.Opens),
      (formalAssociatedGradedPiece I m).val.obj (op U) →ₗ[Γ(X, U)]
        (formalKernelPiece F n).val.obj (op U) →ₗ[Γ(X, U)]
          (formalKernelPiece F (m + n)).val.obj (op U))
    (hnat : ∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
        (a : (formalAssociatedGradedPiece I m).val.obj (op U))
        (x : (formalKernelPiece F n).val.obj (op U)),
      (formalKernelPiece F (m + n)).val.map (homOfLE h).op (act m n U a x) =
        act m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
          ((formalKernelPiece F n).val.map (homOfLE h).op x))
    (hact : ∀ (m n : ℕ) (U : X.Opens)
          (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
          (x : (formalKernelPiece F n).val.obj (op U))
          (t : (F.obj.obj (op (m + n))).val.obj (op U)),
          (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) t =
            (formalKernelι F n).val.app (op U) x →
          (formalKernelι F (m + n)).val.app (op U)
            (act m n U ((formalAssociatedGradedπ I m).val.app (op U) a) x) =
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) • t)
    (hmul : ∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) :
    ∀ (l m n : ℕ) (U : X.Opens)
      (a : (formalAssociatedGradedPiece I l).val.obj (op U))
      (b : (formalAssociatedGradedPiece I m).val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U)),
      HEq (act (l + m) n U (A.mul l m U a b) x)
        (act l (m + n) U a (act m n U b x)) := by
  have hrepresentatives (l m n : ℕ) (U : X.Opens)
      (a : (Scheme.idealSheafPower I.toModulesι l).1.val.obj (op U))
      (b : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
      (x : (formalKernelPiece F n).val.obj (op U))
      (t : (F.obj.obj (op (l + (m + n)))).val.obj (op U))
      (ht : (F.obj.map (homOfLE (by omega : n ≤ l + (m + n))).op).val.app (op U) t =
        (formalKernelι F n).val.app (op U) x) :
      HEq (act (l + m) n U
        (A.mul l m U ((formalAssociatedGradedπ I l).val.app (op U) a)
          ((formalAssociatedGradedπ I m).val.app (op U) b)) x)
        (act l (m + n) U ((formalAssociatedGradedπ I l).val.app (op U) a)
          (act m n U ((formalAssociatedGradedπ I m).val.app (op U) b) x)) := by
    let ra : Γ(X, U) := (Scheme.idealSheafPower I.toModulesι l).2.val.app (op U) a
    let rb : Γ(X, U) := (Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) b
    let tm := (F.obj.map (homOfLE (Nat.le_add_left (m + n) l)).op).val.app (op U) t
    have htm : (F.obj.map (homOfLE (Nat.le_add_left n m)).op).val.app (op U) tm =
        (formalKernelι F n).val.app (op U) x := by
      rw [formal_transition_comp]
      exact ht
    have hm := hact m n U b x tm htm
    have hbt : (F.obj.map (homOfLE (Nat.le_add_left (m + n) l)).op).val.app (op U)
        (rb • t) = (formalKernelι F (m + n)).val.app (op U)
          (act m n U ((formalAssociatedGradedπ I m).val.app (op U) b) x) := by
      rw [map_smul]
      exact hm.symm
    have hr := hact l (m + n) U a
      (act m n U ((formalAssociatedGradedπ I m).val.app (op U) b) x) (rb • t) hbt
    obtain ⟨c, hc, hmulc⟩ := hmul l m U a b
    let tl := (eqToHom (congrArg (fun k ↦ F.obj.obj (op k))
      (Nat.add_assoc l m n).symm)).val.app (op U) t
    have htl : (F.obj.map (homOfLE (Nat.le_add_left n (l + m))).op).val.app (op U)
        tl = (formalKernelι F n).val.app (op U) x := by
      exact (formal_transition_transport F (Nat.add_assoc l m n).symm
        (by omega) (Nat.le_add_left n (l + m)) U t).trans ht
    have hl := hact (l + m) n U c x tl htl
    rw [← hmulc] at hl
    have hl' : (formalKernelι F ((l + m) + n)).val.app (op U)
        (act (l + m) n U (A.mul l m U
          ((formalAssociatedGradedπ I l).val.app (op U) a)
          ((formalAssociatedGradedπ I m).val.app (op U) b)) x) = (ra * rb) • tl := by
      simpa only [id_eq, hc] using hl
    apply kernel_inclusion_heq F (Nat.add_assoc l m n)
    refine (heq_of_eq hl').trans ?_
    have htransport := smul_heq (fun k ↦ F.obj.obj (op k))
      (Nat.add_assoc l m n) U (ra * rb) tl t
      (formal_transport_heq F (Nat.add_assoc l m n).symm U t)
    refine htransport.trans ?_
    have hr' : (formalKernelι F (l + (m + n))).val.app (op U)
        (act l (m + n) U ((formalAssociatedGradedπ I l).val.app (op U) a)
          (act m n U ((formalAssociatedGradedπ I m).val.app (op U) b) x)) =
        (ra * rb) • t := by
      simpa only [id_eq, mul_smul] using hr
    exact (heq_of_eq hr').symm
  intro l m n U a b x
  apply sections_heq_of_local (formalKernelPiece F) (Nat.add_assoc l m n)
  intro p hp
  have hle : n ≤ l + (m + n) := by omega
  have hπ (d : ℕ) : Epi (formalAssociatedGradedπ I d) := by
    unfold formalAssociatedGradedπ formalModuleQuotientπ
    infer_instance
  have htrans : Epi (F.obj.map (homOfLE hle).op) :=
    formal_transition_epi F hle
  obtain ⟨V, hVU, hpV, a', b', t, ha, hb, ht⟩ := local_lifts_three
    (formalAssociatedGradedπ I l) (formalAssociatedGradedπ I m)
    (F.obj.map (homOfLE hle).op)
    U a b ((formalKernelι F n).val.app (op U) x) p hp
  refine ⟨V, hVU, hpV, ?_⟩
  have ht' : (F.obj.map (homOfLE hle).op).val.app (op V) t =
      (formalKernelι F n).val.app (op V)
        ((formalKernelPiece F n).val.map (homOfLE hVU).op x) := by
    rw [PresheafOfModules.naturality_apply]
    exact ht
  simp only [hnat, A.naturality, ← ha, ← hb]
  exact hrepresentatives l m n V a' b'
    ((formalKernelPiece F n).val.map (homOfLE hVU).op x) t ht'

end AlgebraicGeometry
