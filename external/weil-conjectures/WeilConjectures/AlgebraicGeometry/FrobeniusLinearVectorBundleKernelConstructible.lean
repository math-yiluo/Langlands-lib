/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearVectorBundleAffineCoordinates
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearFreeKernelStratification
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearKernelEtalePullback
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant
import WeilConjectures.ConstructibleSheaf.OfForget
import WeilConjectures.ConstructibleSheaf.OpenCover

/-!
# Constructibility of Frobenius-fixed points of a vector bundle

Source: Stacks Project, Tag 0GKU, lemma-frobenius-linear-on-vb.

Let `S` be a Noetherian scheme on which the prime `p` vanishes, `E` a finite locally free
`𝒪_S`-module and `F` a Frobenius-linear endomorphism of the étale sheaf of `E`. The kernel of
`F - 1` is a constructible étale sheaf. We state this for a sheaf of `𝔽_p`-modules whose
underlying abelian sheaf is the (universe lifted) kernel, which is the form in which it is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Modules

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

/-- Finite local freeness supplies, around every point, an affine open on which the tensor
pullback is free of finite rank. -/
private theorem exists_affine_open_tensorPullback_iso_free (S : Scheme.{u}) (E : S.Modules)
    [E.IsFiniteLocallyFree] (x : S) :
    ∃ B : S.Opens, IsAffine B ∧ x ∈ B ∧ ∃ n : ℕ,
      Nonempty ((Modules.tensorPullback B.ι).obj E ≅
        SheafOfModules.free (R := B.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) := by
  classical
  obtain ⟨A, κ, hκ, hxA, ⟨α⟩⟩ := Modules.exists_restrict_iso_free_of_isFiniteLocallyFree E x
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨B, hB, hxB, hBA⟩ := exists_isAffineOpen_mem_and_subset (X := S) (x := x) (U := A) hxA
  refine ⟨B, hB, hxB, Fintype.card κ, ⟨?_⟩⟩
  let k := S.homOfLE hBA
  have hk : k ≫ A.ι = B.ι := by simp [k]
  let eqκ : κ ≃ ULift.{u} (Fin (Fintype.card κ)) :=
    (Fintype.equivFin κ).trans Equiv.ulift.symm
  exact (Modules.tensorSectionsPullbackComparison B.ι).app E ≪≫
    (Modules.restrictFunctorIsoPullback B.ι).symm.app E ≪≫
    Modules.restrictCompIso E A.ι k B.ι hk ≪≫
    (Modules.restrictFunctor k).mapIso α ≪≫
    Modules.restrictFreeIso k κ ≪≫
    SheafOfModules.freeFunctor.mapIso eqκ.toIso

/-- The underlying sheaf of sets of a sheaf of modules is the underlying sheaf of sets of its
underlying abelian sheaf. -/
private noncomputable def sheafComposeForgetIso {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G ≅
      (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) :=
  Iso.refl _

/-- **Frobenius-fixed points of a vector bundle are constructible.** Let `S` be a Noetherian
scheme on which the prime `p` vanishes, `E` a finite locally free `𝒪_S`-module and `F` an
endomorphism of the étale sheaf of `E` which is Frobenius-linear: `F (a e) = aᵖ F e`. A sheaf of
`𝔽_p`-modules whose underlying abelian sheaf is the universe lift of `ker (F - 1)` is
constructible.

Source: Stacks Project, Tag 0GKU, lemma-frobenius-linear-on-vb.

Proof: cover `S` by affine opens on which `E` is free. Restriction to such an open transports
`F` and its kernel (`frobenius_linear_kernel_etale_pullback`), and over an affine base with a
free frame the kernel has a finite stratification with finite locally constant underlying set
sheaves (`frobenius_linear_free_kernel_stratification`). Inverse image commutes with
forgetting the module structure, and a sheaf of modules over a finite ring with finite locally
constant underlying set sheaf is finite locally constant. Constructibility glues along finite
open covers of a Noetherian scheme. -/
theorem isConstructibleSheaf_of_forget₂_iso_frobeniusLinear_kernel
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [IsNoetherian S] (hp : (p : Γ(S, ⊤)) = 0)
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteLocallyFree]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))))
    (eN : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1})).obj N ≅
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (kernel (F - 𝟙 _))) :
    IsConstructibleSheaf N := by
  classical
  let Λ := ULift.{u + 1} (ZMod p)
  choose B hB hxB n α using exists_affine_open_tensorPullback_iso_free S E
  refine IsConstructibleSheaf.of_iSup_eq_top B (eq_top_iff.mpr fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxB x⟩) N fun x ↦ ?_
  have : IsAffine (B x) := hB x
  let V : S.Etale := Scheme.Etale.mk (B x).ι
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion (B x).ι)
  obtain ⟨-, F', -, hF', ⟨β⟩⟩ := frobenius_linear_kernel_etale_pullback p S E F hF V _
    (α x).some
  have : Nontrivial Γ(B x, ⊤) :=
    ((B x).toScheme.presheaf.germ ⊤ ⟨x, hxB x⟩ trivial).hom.domain_nontrivial
  have : CharP Γ(B x, ⊤) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (B x).ι.appTop.hom, hp, map_zero])
  obtain ⟨T, hT⟩ := frobenius_linear_free_kernel_stratification p (B x) _ F' hF' (n x)
    (Iso.refl _)
  obtain ⟨eB⟩ := Etale.exists_upperStar_forget₂_natIso Λ (B x).ι
  refine ⟨T, fun k ↦ ?_⟩
  obtain ⟨eT⟩ := Etale.exists_upperStar_forget₂_natIso Λ (T.immersion k)
  refine IsFiniteLocallyConstantSheaf.of_forget _ (IsFiniteLocallyConstantSheafOfTypes.of_iso ?_
    (hT k))
  refine ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso ?_) ≪≫
    (sheafComposeForgetIso Λ _).symm
  exact (Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion k)).mapIso
      (β.symm ≪≫ (Etale.upperStar AddCommGrpCat.{u + 1} V.hom).mapIso eN.symm ≪≫
        (eB.app N).symm) ≪≫ (eT.app _).symm

end AlgebraicGeometry.Scheme
