/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernel

/-! # Levels of a short exact sequence of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV, remarks (a) and (b),
and proof of Lemma 087X (blueprint: lem-weil-pbc-coherent-formal-short-exact-levels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A short exact sequence in Coh(X,I) is right exact at every positive level, and
its first term at each level is a quotient of the kernel of a later component.
Here `op n` denotes positive level `n + 1`. No componentwise monomorphism is asserted.

Source: Stacks, proof of Lemma 0CYV, first paragraph, remarks (a) and (b), referring
back to the proof of Lemma 087X
(blueprint: lem-weil-pbc-coherent-formal-short-exact-levels).

Proof:
1. Use the abelian structure and termwise cokernel clause of
   coherentFormalModule_abelian. The given limiting cokernel cofork and its image
   show that evaluation preserves the cokernel of S.f. Mathlib then maps the exact
   complex to an exact complex, and the evaluated cokernel projection is epi.
2. Apply coherentFormalModule_kernel to S.g. Its universal factorization property
   gives a limiting kernel fork. Compare it with hS.fIsKernel to obtain K ≅ S.X₁.
3. For index n, use the kernel construction's image comparison at n+c. The abelian
   image corestriction from Ker(S.g at n+c+c), the inverse image comparison,
   the quotient projection, the quotient comparison, and the component of K ≅ S.X₁
   compose to the required epimorphism. The index n+c+c is at least n.
4. No monomorphism assertion for the first arrow at a level is needed.
-/
theorem coherentFormalModule_shortExact_levels (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (S : ShortComplex (CoherentFormalModule X I))
    (hS : S.ShortExact) :
    (∀ n : ℕ,
      (S.map ((IsCoherentFormalModule I).ι ⋙
        (evaluation ℕᵒᵖ X.Modules).obj (op n))).Exact ∧ Epi (S.g.hom.app (op n))) ∧
    (∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧
      ∃ q : kernel (S.g.hom.app (op m)) ⟶ S.X₁.obj.obj (op n), Epi q) := by
  classical
  obtain ⟨hAb, hCok⟩ := coherentFormalModule_abelian X I
  let : Abelian (CoherentFormalModule X I) := hAb.some
  have : Balanced (CoherentFormalModule X I) := by
    let : Preadditive (CoherentFormalModule X I) := hAb.some.toPreadditive
    let : HasZeroMorphisms (CoherentFormalModule X I) :=
      Preadditive.preadditiveHasZeroMorphisms
    have : IsNormalEpiCategory (CoherentFormalModule X I) :=
      Abelian.toIsNormalEpiCategory (C := CoherentFormalModule X I)
    infer_instance
  constructor
  · intro n
    let E := (IsCoherentFormalModule I).ι ⋙
      (evaluation ℕᵒᵖ X.Modules).obj (op n)
    obtain ⟨c, hc, hn⟩ := hCok S.X₁ S.X₂ S.f
    have : PreservesColimit (parallelPair S.f 0) E :=
      preservesColimit_of_preserves_colimit_cocone hc.some (hn n).some
    have hg := CokernelCofork.mapIsColimit _ hS.gIsCokernel E
    refine ⟨hS.exact.map_of_epi_of_preservesCokernel E hS.epi_g inferInstance, ?_⟩
    exact Cofork.IsColimit.epi hg
  · intro n
    obtain ⟨c, hstab, T, j, hj, K, ι, e, htrans, hcomp, hz, huni⟩ :=
      coherentFormalModule_kernel I S.X₂ S.X₃ S.g
    let hk : IsLimit (KernelFork.ofι ι hz) := KernelFork.IsLimit.ofι ι hz
      (fun γ hγ => (huni _ γ hγ).choose)
      (fun γ hγ => (huni _ γ hγ).choose_spec.1)
      (fun γ hγ δ hδ => (huni _ γ hγ).choose_spec.2 δ hδ)
    let ψ : K ≅ S.X₁ := hk.conePointUniqueUpToIso hS.fIsKernel
    obtain ⟨a, ha⟩ := hj (n + c)
    let f := kernel.ι (S.g.hom.app (op (n + c + c))) ≫
      S.X₂.obj.map (homOfLE (Nat.le_add_right (n + c) c)).op
    let q : kernel (S.g.hom.app (op (n + c + c))) ⟶ S.X₁.obj.obj (op n) :=
      Abelian.factorThruImage f ≫ a.inv ≫
        formalModuleQuotientπ I (n + 1) (T.obj (op (n + c))) ≫ (e n).hom ≫
          ((IsCoherentFormalModule I).ι.mapIso ψ).hom.app (op n)
    refine ⟨n + c + c, by omega, q, ?_⟩
    dsimp only [q, formalModuleQuotientπ]
    infer_instance

end AlgebraicGeometry
