/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! # Existence of factorization through the shifted image quotients

Source: Stacks Project, Lemma 087X, claim (d), factorization-existence paragraph.
(blueprint: lem-weil-pbc-formal-kernel-factorization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every transition of a coherent formal module is an epimorphism.
Source: Stacks Project, Lemma 087X, transition-surjectivity argument.
Proof: Successive transitions are quotient projections followed by isomorphisms.
Induction on the index inequality expresses any transition as a composite of these.
(blueprint: lem-weil-pbc-formal-kernel-factorization). -/
theorem formalTransition_epi {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (T : CoherentFormalModule X I) {n m : ℕ} (h : n ≤ m) :
    Epi (T.obj.map (homOfLE h).op) := by
  have hs (k : ℕ) : Epi (T.obj.map (homOfLE (Nat.le_succ k)).op) := by
    obtain ⟨e, he⟩ := T.property.2.2 k
    rw [← he]
    dsimp only [formalModuleQuotientπ]
    infer_instance
  induction h with
  | refl =>
    have he : (homOfLE (show n ≤ n from le_rfl)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [he, T.obj.map_id]
    infer_instance
  | @step m h ih =>
    have := hs m
    have he : (homOfLE (show n ≤ m + 1 from Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, T.obj.map_comp]
    infer_instance

private theorem formalDescent {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (T : CoherentFormalModule X I) {n m : ℕ} (h : n ≤ m)
    {Q : X.Modules} (f : T.obj.obj (op m) ⟶ Q)
    (hf : Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
      (T.obj.obj (op m)) ≫ f = 0) :
    ∃ g : T.obj.obj (op n) ⟶ Q, T.obj.map (homOfLE h).op ≫ g = f := by
  induction h with
  | refl =>
    refine ⟨f, ?_⟩
    have he : (homOfLE (show n ≤ n from le_rfl)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [he, T.obj.map_id, Category.id_comp]
  | @step m h ih =>
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor I (𝟙 (T.obj.obj (op (m + 1))))
      (Nat.add_le_add_right h 1)
    have hbig : Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (m + 1)).2
        (T.obj.obj (op (m + 1))) ≫ f = 0 := by
      simpa only [Category.comp_id] using
        (congrArg (· ≫ f) hk).trans (by rw [Category.assoc, hf, comp_zero])
    obtain ⟨e, he⟩ := T.property.2.2 m
    let d := cokernel.desc (Scheme.idealModuleProductι
      (Scheme.idealSheafPower I.toModulesι (m + 1)).2
      (T.obj.obj (op (m + 1)))) f hbig
    let g := e.inv ≫ d
    have hg : T.obj.map (homOfLE (Nat.le_succ m)).op ≫ g = f := by
      rw [← he]
      simp [g, d, Category.assoc, formalModuleQuotientπ]
    have hgf : Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (T.obj.obj (op m)) ≫ g = 0 := by
      have := formalTransition_epi T (Nat.le_succ m)
      apply (idealModuleProduct_quotient_comp_zero_iff
        (Scheme.idealSheafPower I.toModulesι (n + 1)).2
        (T.obj.map (homOfLE (Nat.le_succ m)).op) g).mpr
      rw [hg, hf]
    obtain ⟨v, hv⟩ := ih g hgf
    refine ⟨v, ?_⟩
    have heq : (homOfLE (show n ≤ m + 1 from Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [heq, T.obj.map_comp, Category.assoc, hv, hg]


/-- Every annihilated map factors through a coherent system presented by the shifted
quotients of the images of later levelwise kernels. No uniqueness is asserted and no
componentwise injectivity of ι is required.

Source: Stacks Project, Lemma 087X, claim (d), factorization-existence paragraph.
(blueprint: lem-weil-pbc-formal-kernel-factorization).

Proof: All transitions of T are epimorphisms and identify the earlier term with the
quotient of the later term by the earlier ideal power, by induction from the defining
successive quotient conditions. At level m+c, γ factors through ker α_(m+c).
Naturality and epimorphy of T_(m+c) → T_m show that γ_m has image contained in the
image of that kernel in F_m. Via hS it therefore factors uniquely through j_m,
giving β_m : T_m → S_m. The maps j_m are monomorphisms, so canceling them in the
naturality squares of γ and j proves that β is compatible with all transitions.
Compose β_(n+c) with the projection S_(n+c) → S_(n+c)/I^(n+1) S_(n+c) and e_n.
Naturality of ideal multiplication shows that this composite kills I^(n+1) T_(n+c).
It thus descends to T_n using the transition quotient identification. Define δ_n by
this descent. Precompose the successive naturality square for δ with the epimorphism
T_(n+1+c) → T_(n+1). Compatibility of β and htrans identify both composites, so the
δ_n form a natural transformation, hence a morphism of the full subcategory. To check
δ_n followed by ι_n equals γ_n, precompose with the epimorphism T_(n+c) → T_n:
hcomp and β_(n+c) followed by j_(n+c) = γ_(n+c), together with naturality of γ,
give the equality. Cancel that epimorphism, and then use componentwise equality.
For c=0 the same descent uses the identity transition; zero ideals and the unit ideal
also satisfy the quotient argument, without any additional hypothesis.
-/
theorem coherentFormalModule_kernel_factorization {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hS : ∀ m : ℕ, ∃ a : S.obj (op m) ≅
        Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      a.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m))
    (K : CoherentFormalModule X I) (ι : K ⟶ F)
    (e : ∀ n : ℕ, formalModuleQuotient I (n + 1) (S.obj (op (n + c))) ≅
      K.obj.obj (op n))
    (htrans : ∀ n : ℕ,
      formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + c))) ≫
          (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op =
        S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
          formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom)
    (hcomp : ∀ n : ℕ,
      formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫
          (e n).hom ≫ ι.hom.app (op n) =
        j.app (op (n + c)) ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op)
    (T : CoherentFormalModule X I) (γ : T ⟶ F) (hγ : γ ≫ α = 0) :
    ∃ δ : T ⟶ K, δ ≫ ι = γ := by
  classical
  have hjmono (m : ℕ) : Mono (j.app (op m)) := by
    obtain ⟨a, ha⟩ := hS m
    rw [← ha]
    infer_instance
  have hb (m : ℕ) : ∃ b : T.obj.obj (op m) ⟶ S.obj (op m),
      b ≫ j.app (op m) = γ.hom.app (op m) := by
    obtain ⟨a, ha⟩ := hS m
    let f := kernel.ι (α.hom.app (op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have hα : γ.hom.app (op (m + c)) ≫ α.hom.app (op (m + c)) = 0 :=
      congrArg (fun v => v.hom.app (op (m + c))) hγ
    let k := kernel.lift (α.hom.app (op (m + c))) (γ.hom.app (op (m + c))) hα
    have hkill : γ.hom.app (op m) ≫ cokernel.π f = 0 := by
      have := formalTransition_epi T (Nat.le_add_right m c)
      apply (cancel_epi (T.obj.map (homOfLE (Nat.le_add_right m c)).op)).mp
      rw [← Category.assoc, γ.hom.naturality]
      have hk : γ.hom.app (op (m + c)) ≫
          F.obj.map (homOfLE (Nat.le_add_right m c)).op = k ≫ f := by
        simp [k, f, ← Category.assoc]
      rw [hk, Category.assoc, cokernel.condition, comp_zero, comp_zero]
    let b := kernel.lift (cokernel.π f) (γ.hom.app (op m)) hkill ≫ a.inv
    refine ⟨b, ?_⟩
    rw [← ha]
    simp only [b, Category.assoc, Iso.inv_hom_id_assoc]
    exact kernel.lift_ι _ _ _
  choose b hb using hb
  let β : T.obj ⟶ S :=
    { app := fun a => b a.unop
      naturality := by
        intro a d f
        obtain ⟨a⟩ := a
        obtain ⟨d⟩ := d
        have := hjmono d
        apply (cancel_mono (j.app (op d))).mp
        dsimp only
        rw [Category.assoc, hb, Category.assoc, j.naturality,
          ← Category.assoc, hb, γ.hom.naturality] }
  have hβ (m : ℕ) : β.app (op m) ≫ j.app (op m) = γ.hom.app (op m) := hb m
  have hd (n : ℕ) : ∃ d : T.obj.obj (op n) ⟶ K.obj.obj (op n),
      T.obj.map (homOfLE (Nat.le_add_right n c)).op ≫ d =
        β.app (op (n + c)) ≫
          formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom := by
    apply formalDescent T (Nat.le_add_right n c)
    rw [← Category.assoc _ _ (e n).hom]
    exact (congrArg (· ≫ (e n).hom)
      (formalModuleQuotient_map_zero I (β.app (op (n + c))) (Nat.le_refl (n + 1)))).trans
        zero_comp
  choose d hd using hd
  have hsucc (n : ℕ) :
      T.obj.map (homOfLE (Nat.le_succ n)).op ≫ d n =
        d (n + 1) ≫ K.obj.map (homOfLE (Nat.le_succ n)).op := by
    have := formalTransition_epi T (Nat.le_add_right (n + 1) c)
    apply (cancel_epi (T.obj.map (homOfLE (Nat.le_add_right (n + 1) c)).op)).mp
    calc
      _ = T.obj.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
          T.obj.map (homOfLE (Nat.le_add_right n c)).op ≫ d n := by
        simp only [← Category.assoc, ← Functor.map_comp]
        congr 2
      _ = T.obj.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
          β.app (op (n + c)) ≫
            formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom := by
        rw [hd n]
      _ = β.app (op (n + 1 + c)) ≫
          S.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) c)).op ≫
            formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))) ≫ (e n).hom := by
        rw [← Category.assoc, β.naturality, Category.assoc]
      _ = β.app (op (n + 1 + c)) ≫
          formalModuleQuotientπ I (n + 2) (S.obj (op (n + 1 + c))) ≫
            (e (n + 1)).hom ≫ K.obj.map (homOfLE (Nat.le_succ n)).op := by
        rw [htrans n]
      _ = T.obj.map (homOfLE (Nat.le_add_right (n + 1) c)).op ≫
          d (n + 1) ≫ K.obj.map (homOfLE (Nat.le_succ n)).op := by
        simpa only [Category.assoc] using
          congrArg (· ≫ K.obj.map (homOfLE (Nat.le_succ n)).op) (hd (n + 1)).symm
  have hnat {n m : ℕ} (h : n ≤ m) :
      T.obj.map (homOfLE h).op ≫ d n = d m ≫ K.obj.map (homOfLE h).op := by
    induction h with
    | refl =>
      have he : (homOfLE (show n ≤ n from le_rfl)).op = 𝟙 (op n) :=
        Subsingleton.elim _ _
      rw [he, T.obj.map_id, K.obj.map_id, Category.id_comp, Category.comp_id]
    | @step m h ih =>
      have he : (homOfLE (show n ≤ m + 1 from Nat.le_succ_of_le h)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, T.obj.map_comp, K.obj.map_comp, Category.assoc, ih,
        ← Category.assoc, hsucc m, Category.assoc]
  let δ : T ⟶ K := ObjectProperty.homMk
    { app := fun a => d a.unop
      naturality := by
        intro a b f
        obtain ⟨a⟩ := a
        obtain ⟨b⟩ := b
        have he : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [he]
        exact hnat (leOfHom f.unop) }
  refine ⟨δ, ?_⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext a
  obtain ⟨n⟩ := a
  change d n ≫ ι.hom.app (op n) = γ.hom.app (op n)
  have := formalTransition_epi T (Nat.le_add_right n c)
  apply (cancel_epi (T.obj.map (homOfLE (Nat.le_add_right n c)).op)).mp
  rw [← Category.assoc, hd n, Category.assoc, Category.assoc, hcomp n,
    ← Category.assoc, hβ, γ.hom.naturality]

end AlgebraicGeometry
