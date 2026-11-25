/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem mapped_le {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] (P Q : Subobject F) (h : P ≤ Q) :
    Subobject.mk (P.arrow ≫ f) ≤ Subobject.mk (Q.arrow ≫ f) :=
  Subobject.mk_le_mk_of_comm (Subobject.ofLE P Q h) (by simp)

private noncomputable def mapped_quotient_iso {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] (P Q : Subobject F) (h : P ≤ Q) :
    cokernel (Subobject.ofLE _ _ (mapped_le f P Q h)) ≅
      cokernel (Subobject.ofLE P Q h) :=
  cokernel.mapIso _ _ (Subobject.underlyingIso (P.arrow ≫ f))
    (Subobject.underlyingIso (Q.arrow ≫ f)) (by
      apply (cancel_mono (Q.arrow ≫ f)).1
      simp)

private noncomputable def quotient_iso_of_eq {X : Scheme.{u}} {G : X.Modules}
    (P Q P' Q' : Subobject G) (h : P ≤ Q) (h' : P' ≤ Q')
    (hP : P = P') (hQ : Q = Q') :
    cokernel (Subobject.ofLE P Q h) ≅ cokernel (Subobject.ofLE P' Q' h') := by
  subst P' Q'
  exact Iso.refl _

private noncomputable def final_quotient_iso {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] :
    cokernel (Subobject.ofLE (Subobject.mk f) ⊤ le_top) ≅ cokernel f :=
  cokernel.mapIso _ _ (Subobject.underlyingIso f)
    (asIso (⊤ : Subobject G).arrow) (by simp)

/-- A coherent filtration extends across a coherent split biproduct, with the
new summand supplying the final integral-ideal quotient witness.
Source: Stacks Project, Tag 01YF, final paragraph of `lemma-coherent-filter`.
(blueprint: new-coherent-integral-filtration-biproduct-succ)
-/
theorem hasCoherentIntegralFiltration_of_biproduct
    {X : Scheme.{u}} (F A G : X.Modules)
    (hF : HasCoherentIntegralFiltration F)
    (hA : RingedSpace.IsCoherent X.toRingedSpace A)
    (hAw : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z ∧
      ∃ I : Z.IdealSheafData, I ≠ ⊥ ∧
        RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
        Nonempty (A ≅ (pushforward i).obj I.toModules))
    (e : G ≅ F ⊞ A) :
    HasCoherentIntegralFiltration G := by
  obtain ⟨m, c, hc, hbot, htop, hcc, hquot⟩ := hF
  let f : F ⟶ G := biprod.inl ≫ e.inv
  let b : Fin (m + 1) → Subobject G := fun k ↦ Subobject.mk ((c k).arrow ≫ f)
  have hb : Monotone b := fun i j h ↦ mapped_le f (c i) (c j) (hc h)
  let d : Fin (m + 1 + 1) → Subobject G := Fin.lastCases ⊤ b
  have hd : Monotone d := by
    intro i j hij
    cases j using Fin.lastCases with
    | last =>
      simp only [d, Fin.lastCases_last]
      exact le_top
    | cast j =>
      cases i using Fin.lastCases with
      | last => exact ((not_le_of_gt (Fin.castSucc_lt_last j)) hij).elim
      | cast i =>
        simp only [d, Fin.lastCases_castSucc]
        exact hb (Fin.castSucc_le_castSucc_iff.mp hij)
  have dbot : d 0 = ⊥ := by
    change d (Fin.castSucc (0 : Fin (m + 1))) = ⊥
    simp only [d, Fin.lastCases_castSucc]
    change Subobject.mk ((c 0).arrow ≫ f) = ⊥
    rw [← Subobject.map_mk, Subobject.mk_arrow, hbot, Subobject.map_bot]
  have hcoh := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  have hFcoh : RingedSpace.IsCoherent X.toRingedSpace F := by
    have ht := hcc (Fin.last m)
    rw [htop] at ht
    exact hcoh.2.2.2.2 _ _ (asIso (⊤ : Subobject F).arrow) ht
  have hGcoh : RingedSpace.IsCoherent X.toRingedSpace G := by
    let S := ShortComplex.mk (biprod.inl : F ⟶ F ⊞ A) biprod.snd biprod.inl_snd
    have hS : S.ShortExact := by
      exact ⟨(ShortComplex.Splitting.ofHasBinaryBiproduct F A).exact⟩
    exact hcoh.2.2.2.2 _ _ e.symm ((hcoh.2.1 S hS).2.1 hFcoh hA)
  refine ⟨m + 1, d, hd, dbot, ?_, ?_, ?_⟩
  · simp [d]
  · intro k
    cases k using Fin.lastCases with
    | last =>
      simp only [d, Fin.lastCases_last]
      exact hcoh.2.2.2.2 _ _ (asIso (⊤ : Subobject G).arrow).symm hGcoh
    | cast k =>
      simp only [d, Fin.lastCases_castSucc]
      exact hcoh.2.2.2.2 _ _ (Subobject.underlyingIso ((c k).arrow ≫ f)).symm (hcc k)
  · intro j
    cases j using Fin.lastCases with
    | last =>
      obtain ⟨Z, i, hi, hZ, I, hne, hI, ⟨a⟩⟩ := hAw
      refine ⟨Z, i, hi, hZ, I, hne, hI, ?_⟩
      have heq : d (Fin.last m).castSucc = Subobject.mk f := by
        simp only [d, Fin.lastCases_castSucc]
        change Subobject.mk ((c (Fin.last m)).arrow ≫ f) = Subobject.mk f
        rw [← Subobject.map_mk, Subobject.mk_arrow, htop, Subobject.map_top]
      have heq' : d (Fin.last m).succ = ⊤ := by
        simp [d, Fin.succ_last]
      exact ⟨quotient_iso_of_eq _ _ _ _ _ le_top heq heq' ≪≫ final_quotient_iso f ≪≫
        cokernelCompIsIso biprod.inl e.inv ≪≫ cokernelBiprodInlIso ≪≫ a⟩
    | cast j =>
      obtain ⟨Z, i, hi, hZ, I, hne, hI, ⟨a⟩⟩ := hquot j
      refine ⟨Z, i, hi, hZ, I, hne, hI, ?_⟩
      have heq : d j.castSucc.castSucc = b j.castSucc := by simp [d]
      have heq' : d j.castSucc.succ = b j.succ := by
        change d j.succ.castSucc = b j.succ
        exact Fin.lastCases_castSucc _
      exact ⟨quotient_iso_of_eq _ _ _ _ _ (mapped_le f _ _ (hc j.castSucc_le_succ))
        heq heq' ≪≫ mapped_quotient_iso f (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ) ≪≫ a⟩

end AlgebraicGeometry.Scheme.Modules
