/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalKernelGradedPieces
import WeilConjectures.AlgebraicGeometry.AffineBilinearExtension
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Bilinear multiplication on associated graded ideal sheaves

Source: Stacks Project, Lemma 087Z, the algebra in its statement; Schemes Lemmas
01I8 and 01IC for affine tensor products and quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem lift_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (hinj : ∀ V : X.Opens, Function.Injective (f.app V))
    (U : X.Opens) (s : Γ(N, U))
    (hlocal : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      ∃ t : Γ(M, V.1), f.app V.1 t = N.presheaf.map (homOfLE hVU).op s) :
    ∃ t : Γ(M, U), f.app U t = s := by
  classical
  let A := {V : X.affineOpens // V.1 ≤ U}
  have hl (i : A) := hlocal i.1 i.2
  choose t ht using hl
  have hcover : U ≤ ⨆ i : A, i.1.1 := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf (fun i : A ↦ i.1.1) t := by
    intro i j
    apply hinj (i.1.1 ⊓ j.1.1)
    erw [PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply,
      ht i, ht j]
    change N.presheaf.map (TopologicalSpace.Opens.infLELeft _ _).op
        (N.presheaf.map (homOfLE i.2).op s) =
      N.presheaf.map (TopologicalSpace.Opens.infLERight _ _).op
        (N.presheaf.map (homOfLE j.2).op s)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨c, hc, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    (fun i : A ↦ i.1.1) U (fun i ↦ homOfLE i.2) hcover t hcompat
  refine ⟨c, ?_⟩
  apply sections_eq_of_affine N U
  intro V hVU
  erw [← PresheafOfModules.naturality_apply]
  erw [hc ⟨V, hVU⟩, ht ⟨V, hVU⟩]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication descends to successive ideal-power quotients and commutes with
restriction. No associativity, commutativity or unit law is asserted here.
Source: Stacks Project, Lemma 087Z and Schemes Lemmas 01I8, 01IC.
(blueprint: lem-weil-pbc-formal-associated-graded-multiplication).

Proof: On an affine open U, identify the power inclusions with I(U)^r and the
quotient projection with I(U)^r / I(U)^(r+1). For degree zero use the identity
inclusion of the structure sheaf. Multiply representatives. The product lies in
I(U)^(m+n); changing either representative changes it by I(U)^(m+n+1), so the
operation is well defined and bilinear. This construction commutes with restriction
between affine opens, since inclusions, projections and ring multiplication do.
For an arbitrary open, lift the two quotient sections on an affine cover. On an
affine refinement of any overlap the results agree by independence of lifts. Glue
using the sheaf condition. The same argument proves bilinearity and restriction
compatibility. For actual sections of the power ideals, their product belongs
locally to the range of the (m+n)-th power inclusion. This inclusion is monic;
hence the local lifts agree and glue to c, and the local definition of the quotient
operation gives the displayed identity. The argument includes empty opens,
the zero and unit ideals, and zero degrees. -/
theorem formalAssociatedGraded_multiplication_exists {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    ∃ mu : ∀ (m n : ℕ) (U : X.Opens),
      (formalAssociatedGradedPiece I m).val.obj (op U) →ₗ[Γ(X, U)]
        (formalAssociatedGradedPiece I n).val.obj (op U) →ₗ[Γ(X, U)]
          (formalAssociatedGradedPiece I (m + n)).val.obj (op U),
      (∀ (m n : ℕ) (U V : X.Opens) (h : V ≤ U)
        (a : (formalAssociatedGradedPiece I m).val.obj (op U))
        (b : (formalAssociatedGradedPiece I n).val.obj (op U)),
        (formalAssociatedGradedPiece I (m + n)).val.map (homOfLE h).op (mu m n U a b) =
          mu m n V ((formalAssociatedGradedPiece I m).val.map (homOfLE h).op a)
            ((formalAssociatedGradedPiece I n).val.map (homOfLE h).op b)) ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          mu m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) := by
  classical
  have hpair (m n : ℕ) := formalAssociatedGraded_affine_multiplication_exists I m n
  choose beta hbeta hrep using hpair
  have hext (m n : ℕ) := affineBilinear_extension
    (formalAssociatedGradedPiece I m) (formalAssociatedGradedPiece I n)
    (formalAssociatedGradedPiece I (m + n)) (beta m n) (hbeta m n)
  choose mu hnat haff using hext
  refine ⟨mu, hnat, ?_⟩
  intro m n U a b
  let M := (Scheme.idealSheafPower I.toModulesι m).1
  let N := (Scheme.idealSheafPower I.toModulesι n).1
  let P := (Scheme.idealSheafPower I.toModulesι (m + n)).1
  let im := (Scheme.idealSheafPower I.toModulesι m).2
  let jn := (Scheme.idealSheafPower I.toModulesι n).2
  let k := (Scheme.idealSheafPower I.toModulesι (m + n)).2
  let s : Γ(X, U) := (@id Γ(X, U) (im.app U a)) * (@id Γ(X, U) (jn.app U b))
  obtain ⟨c, hc⟩ := lift_of_affine k (formalPolynomial_power_injective I.toModulesι (m + n)) U s (by
    intro V hVU
    obtain ⟨c, hc⟩ := power_affine_product I m n V
      (M.presheaf.map (homOfLE hVU).op a) (N.presheaf.map (homOfLE hVU).op b)
    refine ⟨c, ?_⟩
    change k.app V.1 c = (X.presheaf.map (homOfLE hVU).op).hom s
    rw [hc]
    change (@id Γ(X, V.1) (im.app V.1 _)) * (@id Γ(X, V.1) (jn.app V.1 _)) = _
    erw [PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply]
    exact (map_mul (X.presheaf.map (homOfLE hVU).op).hom _ _).symm)
  refine ⟨c, hc, ?_⟩
  apply sections_eq_of_affine (formalAssociatedGradedPiece I (m + n)) U
  intro V hVU
  change (formalAssociatedGradedPiece I (m + n)).val.map (homOfLE hVU).op
    (mu m n U _ _) = _
  rw [hnat]
  change mu m n V.1
      ((formalAssociatedGradedPiece I m).presheaf.map (homOfLE hVU).op
        ((formalAssociatedGradedπ I m).app U a))
      ((formalAssociatedGradedPiece I n).presheaf.map (homOfLE hVU).op
        ((formalAssociatedGradedπ I n).app U b)) =
    (formalAssociatedGradedPiece I (m + n)).presheaf.map (homOfLE hVU).op
      ((formalAssociatedGradedπ I (m + n)).app U c)
  erw [← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply]
  rw [haff]
  apply hrep m n V
  change k.app V.1 (P.presheaf.map (homOfLE hVU).op c) =
    (@id Γ(X, V.1) (im.app V.1 (M.presheaf.map (homOfLE hVU).op a))) *
      (@id Γ(X, V.1) (jn.app V.1 (N.presheaf.map (homOfLE hVU).op b)))
  erw [PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply,
    PresheafOfModules.naturality_apply, hc]
  exact map_mul (X.presheaf.map (homOfLE hVU).op).hom _ _

end AlgebraicGeometry
