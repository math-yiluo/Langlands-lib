/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.TorsionControlledAffineCandidate
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoInvariant
import WeilConjectures.AlgebraicGeometry.CoherentOfFormalQuotientsAndTorsionKernel

/-! # The affine part of torsion-controlled algebraization

Source: Stacks Project, Tag 0889(1), affine paragraph, using Tags 087W, 0ALK and 05EU.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraization on a single affine scheme. Descent to a nonaffine scheme is not
part of this assertion.

Source: Stacks Project, Tag 0889(1), affine paragraph, using Tags 087W, 0ALK and 05EU.
(blueprint: lem-weil-pbc-torsion-controlled-affine-algebraization).

Proof: Identify X with Spec A via its canonical affine isomorphism. Coherent sheaves
correspond to finite A-modules. The affine formal-module equivalence identifies N
with a finite completed module M' and completion H with completion of the finite
module P of sections of H. Remark 0888 transfers the componentwise bound to the
kernel and cokernel of the map M' to completion P. Completion of P is its tensor
product with the completed ring. The completion ring map is flat and induces an
isomorphism modulo J, so apply the map-to part of formal-gluing Lemma 0ALK.
It yields a module T, a map T to P, and a compatible completed isomorphism, with
ideal-power-torsion kernel and cokernel. At each generator f of J, localization
kills that kernel and cokernel, so T_f is isomorphic to the finite module P_f.
Its completed scalar extension is M', also finite. The finiteness criterion of
Remark 05EU therefore makes T finite. Over the Noetherian ring A the
kernel and cokernel are finite. Choose finitely many generators of each and take
the maximum of their annihilating exponents and 1. This gives one positive bound.
Sheafify T and the map, and transport the completed isomorphism back through the
affine equivalence; compatibility gives the displayed factorization. If J is the
unit ideal, take T=P and the identity map; if J is zero, completion is the identity
and the original map provides the triple. The zero ring causes no exception. -/
theorem torsionControlled_affine_algebraization
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) := by
  obtain ⟨F, hqc, a, β, hδ, s, hs, hk, hc⟩ :=
    torsionControlled_affine_candidate J H N δ htorsion
  have : F.IsQuasicoherent := hqc
  have hquot : RingedSpace.IsCoherent X.toRingedSpace
      (((formalCompletionFunctor J).obj F).obj (op (s - 1))) :=
    (coherentFormalModules_of_iso X J β N.property).1 (s - 1)
  have hF := coherent_of_formalQuotients_and_torsionKernel J F H a s hs hquot hk
  let Fc : CoherentModules X := ⟨F, hF⟩
  let ac : Fc ⟶ H := ObjectProperty.homMk a
  let βc : N ≅ (completion X J).obj Fc :=
    (IsCoherentFormalModule J).isoMk β
  refine ⟨Fc, ac, βc, ?_, s, hs, hk, hc⟩
  apply (ObjectProperty.ι (IsCoherentFormalModule J)).map_injective
  exact hδ

end AlgebraicGeometry
