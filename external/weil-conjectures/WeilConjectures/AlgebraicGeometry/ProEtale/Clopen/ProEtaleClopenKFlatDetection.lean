/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenStructuralData
import Mathlib.CategoryTheory.Adjunction.Additive

/-! K-flatness detection for finite clopen pro-etale partitions.

K-flatness is tested against arbitrary unbounded acyclic complexes, using componentwise
acyclicity and zero insertion.

## References

* Stacks Project, Tags 06YN and 0FPQ
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory

private theorem clopen_kflat_detection_small
    (X : Scheme.{t}) (I : Type) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ↔
      ∀ i, CochainComplex.IsKFlatIndependentCoefficients
        (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
        ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P) := by
  classical
  let r := fun i ↦ ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R
  let T := coefficientTotalTensor.{u, t + 1, t} (topology X) R
  let Ti := fun i ↦ coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
    ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
  obtain ⟨G, η, ε, _, _, _, _, _, _, _, _, _, _, ⟨e, he, hezero, _⟩,
    _, _, hexact, _, _⟩ :=
    clopen_ringed_module_gluing.{t, max u (t + 1), u, 0, u, u, 0, 0}
      X I Y j hd hc
      ((sheafCompose (topology X) (forget₂ CommRingCat.{max u (t + 1)}
        RingCat.{max u (t + 1)})).obj R)
      (by
        intro U a b
        change (a : R.obj.obj U) * b = b * a
        exact @mul_comm (R.obj.obj U) inferInstance a b)
  have ha (K : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ) :
      K.Acyclic ↔ ∀ i, ((r i).obj K).Acyclic := by
    constructor
    · intro h i n
      exact (hexact (K.sc n)).mp (h n) i
    · intro h n
      exact (hexact (K.sc n)).mpr (fun i ↦ h i n)
  obtain ⟨hb, _, hadj⟩ := clopen_structural_data X I Y j hd hc R
  constructor
  · intro hP i
    change ∀ F, F.Acyclic → ((Ti i).obj (F, (r i).obj P)).Acyclic
    intro F hF
    have adj := (hadj i (e i) (he i) (fun k hki N ↦ hezero k i hki N)).some
    have : (e i).Additive := adj.right_adjoint_additive
    let E := (e i).mapHomologicalComplex (.up ℤ)
    let a : E ⋙ r i ≅ 𝟭 _ :=
      Functor.mapHomologicalComplexCompIso (he i).some (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    have hE : (E.obj F).Acyclic := by
      apply (ha _).mpr
      intro k n
      by_cases hki : k = i
      · subst k
        exact (hF n).of_iso (a.app F).symm
      · exact HomologicalComplex.ExactAt.of_isZero (hezero k i hki (F.X n))
    change ∀ A, A.Acyclic → (T.obj (A, P)).Acyclic at hP
    have h := (ha _).mp (hP (E.obj F) hE) i
    obtain ⟨_, b, _⟩ := hb i
    let c := b.app (E.obj F, P) ≪≫
      (Ti i).mapIso ((a.app F).prod (Iso.refl ((r i).obj P)))
    intro n
    exact (h n).of_iso c
  · intro hP
    change ∀ F, F.Acyclic → (T.obj (F, P)).Acyclic
    intro F hF
    apply (ha _).mpr
    intro i
    have hi := hP i
    change ∀ A, A.Acyclic → ((Ti i).obj (A, (r i).obj P)).Acyclic at hi
    have h := hi ((r i).obj F) ((ha F).mp hF i)
    obtain ⟨_, b, _⟩ := hb i
    intro n
    exact (h n).of_iso (b.app (F, P)).symm

/-- K-flatness is detected componentwise by restriction along a finite disjoint
open-and-closed covering. -/
theorem clopen_kflat_detection
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ P : CochainComplex (ClopenData.clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P ↔
        ∀ i, CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (ClopenData.clopenTensorRings.{t, u} (j i)).obj R)
          ((ClopenData.clopenTensorComplexRestriction.{t, u} (j i) R).obj P) := by
  classical
  intro P
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hd : Pairwise (fun a b : Fin n ↦
      Disjoint (Set.range (j (e.symm a))) (Set.range (j (e.symm b)))) := by
    intro a b hab
    exact hdisjoint (fun h ↦ hab (e.symm.injective h))
  have hc : ∀ x : X, ∃ a : Fin n, x ∈ Set.range (j (e.symm a)) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨e i, by rw [e.symm_apply_apply]; exact hi⟩
  have h := clopen_kflat_detection_small X (Fin n) (fun a ↦ Y (e.symm a))
    (fun a ↦ j (e.symm a)) hd hc R P
  constructor
  · intro hP i
    have hi := h.mp hP (e i)
    rw [e.symm_apply_apply] at hi
    exact hi
  · intro hP
    exact h.mpr (fun a ↦ hP (e.symm a))

end AlgebraicGeometry.Scheme.ProEt
