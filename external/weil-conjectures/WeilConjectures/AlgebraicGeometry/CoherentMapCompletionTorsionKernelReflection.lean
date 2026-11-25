/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit
import WeilConjectures.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero
import WeilConjectures.AlgebraicGeometry.SupportedCoherentCompletionReflectsZero

/-! # Reflecting kernel torsion from completion on a closed thickening

Source: Stacks Project, Tags 088A and 0888, the second torsion estimate.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Reflect a componentwise torsion bound for the completion of a coherent map whose
source and target are annihilated by the ideal of a fixed closed thickening.
Source: Stacks Project, Tag 088A, lemma-existence-tricky, second application of
Remark 0888, remark-inverse-systems-kernel-cokernel-annihilated-by.
https://stacks.math.columbia.edu/tag/088A
https://stacks.math.columbia.edu/tag/0888
(blueprint: lem-weil-pbc-coherent-map-completion-torsion-kernel-reflection).

Proof:
1. Put Z = V(K^q). The closed-immersion coherent equivalence descends F, G and a
   to coherent modules and a map on Z, because K^q kills both modules. Its natural
   completion comparison identifies the pushed completion of this map with the
   I-completion of a. Closed pushforward identifies products by the extended ideal
   K O_Z with products by K on X.
2. On every affine of Z the uniform bounds on the reduced kernels and cokernels
   supply the scalar reverse maps of Remark 0888: for f,g in the s-th ideal power,
   lift f*y through the reduced map and multiply the lift by g. Kernel annihilation
   makes this independent of the lift; the lifting formula proves compatibility
   with transition maps. Taking inverse limits gives both scalar composite identities.
   Products f*g generate the 2s-th ideal power, which therefore kills the kernel of
   the affine limit map. The affine formal-module equivalence identifies this with
   the kernel of the completed map.
3. Completion on finite modules over a Noetherian affine is tensoring with the flat
   completed ring. It preserves kernels and images of ideal-action maps. Thus the
   completion of the 2s-th ideal product with the coherent kernel on Z is zero on
   every affine, hence is the zero formal object. The assumed global completion
   equivalence reflects zero, so this coherent ideal product is zero on Z.
4. Exact closed pushforward identifies the pushed kernel with kernel(a), and its
   ideal-product comparison identifies the product just shown zero with the stated
   K^(2s) product on X. This proves the conclusion.
No local faithfulness of affine completion is assumed; reflection occurs globally on Z.
-/
theorem coherentMap_completion_torsion_kernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcompletion : ∀ (hZ : IsNoetherian (K ^ q).subscheme),
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (kernel a.hom)) := by
  have _ := hG
  have ha := coherentFormalModule_annihilated_affine_limit X I K
    ((completion X I).obj F) ((completion X I).obj G) ((completion X I).map a) s hs h
  obtain ⟨hcoh, hzero⟩ := coherentKernel_idealProduct_completion_zero I K F G a (2 * s)
    (fun U ↦ (ha U).1)
  let H : CoherentModules X := ⟨_, hcoh⟩
  let j : H.obj ⟶ F.obj :=
    Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (kernel a.hom) ≫ kernel.ι a.hom
  have : Mono j := by
    dsimp [j, Scheme.idealModuleProductι]
    infer_instance
  exact supportedCoherent_completion_reflects_zero I K q hq hcompletion F H j hF hzero

end AlgebraicGeometry
