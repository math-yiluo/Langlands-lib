/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionAssembly
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionObjectwise

/-! # CoherentFormalModulesAffineReconstruction

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Surjective projections with ideal-power kernels reconstruct the formal sheaf system.
This is the formal-system half of the equivalence; no equivalence is assumed.
Source: Stacks Project, Lemma 087W, final quotient computation and the affine
sheaf/module correspondence, Schemes 01I7/01IB.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-reconstruction).

Proof: For each F and n, the first isomorphism theorem applied to p(F)_n identifies
restricted L(F)/I^(n+1)L(F) with Gamma(F_n), using precisely hquotient. The affine
ideal-product/cokernel comparison identifies the nth component of Q(L(F)) with the
tilde of that module quotient. Coherence makes F_n quasi-coherent, so the tilde/Gamma
counit is an isomorphism onto F_n. Compose these two isomorphisms at each n. The
transition diagrams commute: after precomposing with the surjective quotient projection,
this is the cone naturality equation for p(F). Thus they assemble to an isomorphism
of inverse systems. For a map F -> G, precompose the component naturality square with
the same quotient projection and apply hnatural and the tilde/Gamma naturality equation.
Cancel the projection to prove the square. The resulting natural isomorphism lifts to
the full subcategory of coherent formal systems, since its objects are F and Q(L(F)). -/
theorem coherentFormalModules_affine_reconstruction (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N))
    (p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
    (hnatural : (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))))
    (hquotient : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj)))) :
    Nonempty (L ⋙ (coherentFormalModules_affine_quotientFunctor A I J hJ) ≅ 𝟭 _) := by
  apply coherentFormalModules_affine_reconstruction_assembly A I J hJ L p hnatural hquotient
  exact coherentFormalModules_affine_reconstruction_objectwise A I J hJ L p hquotient

end AlgebraicGeometry
