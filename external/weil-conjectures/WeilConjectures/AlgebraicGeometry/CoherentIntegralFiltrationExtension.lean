/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import all WeilConjectures.CategoryTheory.FiniteFiltrationRefinement

/-! # Concatenating coherent integral-ideal filtrations

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, induced-filtration step.
(blueprint: lem-weil-pbc-coherent-integral-filtration-extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Coherent integral-ideal filtrations are closed under coherent extensions.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, proof, the induced
filtration in the reducible-support paragraph and the last sentence.
(blueprint: lem-weil-pbc-coherent-integral-filtration-extension)

Proof: take a filtration A_0 <= ... <= A_a of S.X₁ and a filtration B_0 <= ... <= B_b
of S.X₃. Map the first chain into S.X₂ along the monomorphism S.f. Append the inverse
images of B_k under the epimorphism S.g. The two chains meet at ker S.g = im S.f.
The inverse image of B_k is the kernel of S.X₂ -> S.X₃ -> S.X₃/B_k, so is coherent
by coherent kernels and cokernels on a locally Noetherian scheme. The mapped first
chain is isomorphic to the original chain and hence coherent. Monotonicity is inherited
from the two chains; the endpoints are zero and S.X₂. Quotients in the first part are
isomorphic to A_{j+1}/A_j. Quotients in the second part are isomorphic to B_{k+1}/B_k:
the induced map is injective on stalks by the kernel description and surjective on
stalks because S.g is an epimorphism. Stalk exactness and detection of isomorphisms
identify these quotients. Compose with the given integral-ideal quotient isomorphisms.
This also works if either filtration has length zero. -/
theorem coherentIntegralFiltration_of_shortExact
    (X : Scheme.{u}) [IsLocallyNoetherian X] (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (h₁ : RingedSpace.IsCoherent X.toRingedSpace S.X₁)
    (h₂ : RingedSpace.IsCoherent X.toRingedSpace S.X₂)
    (h₃ : RingedSpace.IsCoherent X.toRingedSpace S.X₃)
    (hA : HasCoherentIntegralFiltration S.X₁)
    (hB : HasCoherentIntegralFiltration S.X₃) :
    HasCoherentIntegralFiltration S.X₂ := by
  classical
  have _ := h₁
  have _ := h₂
  have _ := h₃
  have hcoh := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  let P : ObjectProperty X.Modules := fun F ↦
    RingedSpace.IsCoherent X.toRingedSpace F ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          I ≠ ⊥ ∧ RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
          Nonempty (F ≅ (pushforward i).obj I.toModules)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    obtain ⟨hF, Z, i, hi, hZ, I, hI, hIc, ⟨eI⟩⟩ := h
    exact ⟨hcoh.2.2.2.2 _ _ e hF, Z, i, hi, hZ, I, hI, hIc, ⟨e.symm ≪≫ eI⟩⟩⟩
  have toClosure (F : X.Modules) (hF : HasCoherentIntegralFiltration F) :
      P.filtrationClosure F := by
    obtain ⟨n, c, hc, hbot, htop, hcc, hquot⟩ := hF
    apply ObjectProperty.filtrationClosure_iff.mpr
    refine ⟨n, fun j ↦ (c j : X.Modules),
      fun j ↦ Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ),
      ?_, ?_, fun j ↦ inferInstance, fun j ↦ ?_⟩
    · dsimp only
      rw [hbot]
      exact (isZero_zero X.Modules).of_iso Subobject.botCoeIsoZero
    · dsimp only
      rw [htop]
      exact ⟨Subobject.underlyingIso (𝟙 F)⟩
    · exact ⟨(hcoh.1 _ _ _ (hcc j.castSucc) (hcc j.succ)).2, hquot j⟩
  have hmid := P.filtrationClosure.prop_X₂_of_shortExact hS
    (toClosure S.X₁ hA) (toClosure S.X₃ hB)
  obtain ⟨n, c, hc, hbot, htop, hquot⟩ := CategoryTheory.subobject_filtration_of_closure P hmid
  refine ⟨n, c, hc, hbot, htop, ?_, fun j ↦ (hquot j).2⟩
  have hstep : ∀ (j : ℕ) (hj : j < n + 1),
      RingedSpace.IsCoherent X.toRingedSpace (c ⟨j, hj⟩ : X.Modules) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [show (⟨0, hj⟩ : Fin (n + 1)) = 0 from rfl, hbot]
      exact hcoh.2.2.2.2 _ _ Subobject.botCoeIsoZero.symm hcoh.2.2.2.1
    | succ j ih =>
      intro hj
      let k : Fin n := ⟨j, by omega⟩
      let f := Subobject.ofLE (c k.castSucc) (c k.succ) (hc k.castSucc_le_succ)
      have hs : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)⟩
      exact (hcoh.2.1 _ hs).2.1 (ih (by omega)) (hquot k).1
  exact fun k ↦ hstep k.val k.isLt

end AlgebraicGeometry.Scheme.Modules
