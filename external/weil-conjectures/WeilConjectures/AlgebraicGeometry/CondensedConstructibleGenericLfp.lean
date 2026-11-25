/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.Topology.StratificationDense

/-! # A locally finitely presented open piece of a constructible module -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A constructible module is locally finitely presented everywhere, or on some nonempty open.
Source: Hemo--Richarz--Scholbach, proof of Lemma 5.3(2), finite-stratum induction;
Bhatt--Scholze, Definition 6.8.10 and proof of Lemma 6.8.12.
(auxiliary; not a blueprint node)

Proof: choose the finite locally closed stratification in constructibility. The union of
its stratum interiors is dense. If the ambient scheme is nonempty, one interior U is
nonempty. The restriction of the corresponding stratum to U is a surjective closed
immersion. Pro-étale sheaves and the coefficient ring are invariant under this immersion:
topological invariance on the affine ind-etale basis transports covering
presentations and makes both adjunction maps invertible. Pull back the finite
presentations on the stratum to its inverse image over U,
and transport them along this equivalence, which preserves the free modules and cokernels
in a presentation. This gives local finite presentation on U. If the ambient scheme is
empty, the empty pro-étale cover witnesses local finite presentation of every module,
so the first alternative holds. No nonempty point, reduced structure, or coefficient field
is used in the empty case or in the transport. -/
theorem condensed_constructible_generic_lfp
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ T) M ∨
    ∃ U : T.Opens, (U : Set T).Nonempty ∧
      IsLocallyFinitelyPresented (condensedRingObj Λ U.toScheme)
        ((CondensedRing.upperStar Λ U.ι).obj M) := by
  classical
  by_cases hT : Nonempty T
  · let := hT
    obtain ⟨S, hS⟩ := hM
    obtain ⟨x, hx⟩ := S.dense_iUnion_interior_stratum.nonempty
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    let U : T.Opens := ⟨interior (S.stratum a), isOpen_interior⟩
    right
    refine ⟨U, ⟨x, ha⟩, ?_⟩
    have hp := localFinitePresentation_upperStar_of_range_subset (S.immersion a) U.ι
      (by rw [Scheme.Opens.range_ι, S.range_immersion]; exact interior_subset)
      (condensedRingObj Λ T) M (hS a)
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ U.ι)).app
        (((upperStar Ab.{u + 1} U.ι).mapMod (condensedRingObj Λ T)).obj M)).symm
    exact localFinitePresentation_comap (inv (condensedPullbackHom Λ U.ι)) hp
  · have : IsEmpty T := not_nonempty_iff.mp hT
    have hz : IsZero M.X := by
      apply Sheaf.isZero_of_isZero_obj
      rintro ⟨V⟩
      have : IsEmpty V.left := ⟨fun x ↦ hT ⟨V.hom x⟩⟩
      exact (isZero_zero Ab.{u + 1}).of_iso
        ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V).uniqueUpToIso
          HasZeroObject.zeroIsTerminal)
    have hzM : IsZero M := by
      apply (IsZero.iff_id_eq_zero _).2
      apply (Mod.forget _).map_injective
      exact hz.eq_of_src _ _
    exact Or.inl (localFinitePresentation_of_isZero _ M hzM)

end AlgebraicGeometry.ProEtale
