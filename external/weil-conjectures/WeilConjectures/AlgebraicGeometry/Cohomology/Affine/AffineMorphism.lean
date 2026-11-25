/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero
public import WeilConjectures.Topology.Sheaves.PushforwardCohomology

/-!
# Cohomology along an affine morphism

The cohomology of a quasi-coherent sheaf is unchanged by pushforward along an affine morphism
(`AlgebraicGeometry.Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Cohomology along an affine morphism, for abelian sheaves.** Let `g : X ⟶ Y` be an affine
morphism. Then `H^q(X, F) ≅ H^q(Y, g_* F)`, naturally in the abelian sheaves `F` on `X` which are
Čech-acyclic on affine opens. Indeed `g_*` is exact on short exact sequences starting in such a
sheaf, since these are surjective on the sections over the affine opens `g ⁻¹ᵁ V`. -/
theorem nonempty_functorH_iso_pushforwardAb_of_isAffineHom {Y : Scheme.{u}} (g : X ⟶ Y)
    [IsAffineHom g] (q : ℕ) :
    Nonempty ((cechAcyclicOnAffines X).ι ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology X) q ≅
      (cechAcyclicOnAffines X).ι ⋙ TopCat.Sheaf.pushforwardAb g.base ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology Y) q) :=
  TopCat.Sheaf.nonempty_functorH_iso_pushforwardAb g.base (cechAcyclicOnAffines X)
    (fun _ h ↦ cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h ↦ TopCat.Sheaf.shortExact_map_pushforward hS Y.isBasis_affineOpens
      fun _ hV ↦ surjective_app_of_cechAcyclicOnAffines hS h (IsAffineOpen.preimage hV g)) q

section AffineMorphism

variable (k : Type u) [Field k] {Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- **Cohomology along an affine morphism.** Let `g : X ⟶ Y` be an affine morphism of
`k`-schemes. Then `H^q(X, ℱ) ≅ H^q(Y, g_* ℱ)`, `k`-linearly and naturally in the quasi-coherent
`𝒪_X`-module `ℱ`. The higher direct images `R^p g_* ℱ` vanish, since on an affine open `V` of `Y`
they are computed by the cohomology of `ℱ` on the affine scheme `g ⁻¹ᵁ V`, which vanishes by
`subsingleton_H_succ_of_isAffine`; the Leray spectral sequence then degenerates.

For a closed immersion this is the cohomology clause of the blueprint lemma.

(blueprint: `lem-pc-closed-immersion-coherent-cohomology`) -/
theorem nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom (g : X ⟶ Y)
    [g.IsOver (Spec (.of k))] [IsAffineHom g] (q : ℕ) :
    Nonempty ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ cohomologyFunctor k q ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ pushforward g ⋙
        cohomologyFunctor k q) := by
  obtain ⟨e⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom g q
  let Q := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let F (ℱ : Q.FullSubcategory) : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ.obj,
      have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ.obj := ℱ.property
      cechAcyclicOnAffines_of_isQuasicoherent ℱ.obj⟩
  have hE {ℱ ℱ' : Q.FullSubcategory} (φ : ℱ ⟶ ℱ')
      (x : Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ.obj) q) :
      e.hom.app (F ℱ') (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ.hom) q x) =
        Sheaf.H.map ((TopCat.Sheaf.pushforwardAb g.base).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ.hom)) q (e.hom.app (F ℱ) x) := by
    -- Elaborating the naturality square before unifying it with the goal avoids a timeout.
    have h := NatTrans.naturality_apply e.hom (ObjectProperty.homMk
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ.hom) : F ℱ ⟶ F ℱ') x
    exact h
  have hsmul (ℱ : Q.FullSubcategory) (c : k)
      (x : Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ.obj) q) :
      e.hom.app (F ℱ) (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (smulHom ℱ.obj (globalSectionsRingHom k c))) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        (smulHom ((pushforward g).obj ℱ.obj) (globalSectionsRingHom k c))) q
          (e.hom.app (F ℱ) x) := by
    rw [← Hom.appTop_globalSectionsRingHom k g c, ← pushforward_map_smulHom]
    exact hE (ObjectProperty.homMk (smulHom ℱ.obj (g.appTop (globalSectionsRingHom k c)))) x
  -- The components are `k`-linear: multiplication by `c` on `H^q(Y, g_* ℱ)` is induced by
  -- multiplication by `g^♯ c` on `ℱ`.
  refine ⟨NatIso.ofComponents (fun ℱ ↦ LinearEquiv.toModuleIso
    ({ toAddEquiv := (e.app (F ℱ)).addCommGroupIsoToAddEquiv
       map_smul' := fun c x ↦ ?_ } : (Q.ι ⋙ cohomologyFunctor k q).obj ℱ ≃ₗ[k]
        (Q.ι ⋙ pushforward g ⋙ cohomologyFunctor k q).obj ℱ)) fun {ℱ ℱ'} φ ↦ ?_⟩
  · exact hsmul ℱ c x
  · ext x
    exact hE φ x

/-- **Cohomology along an affine morphism.** Let `g : X ⟶ Y` be an affine morphism of
`k`-schemes. For every quasi-coherent `𝒪_X`-module `ℱ` and every `q` we have
`H^q(Y, g_* ℱ) ≅ H^q(X, ℱ)` (`nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`), so the
two have the same dimension over `k`. -/
theorem finrankH_pushforward_of_isAffineHom (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    [IsAffineHom g] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    (q : ℕ) : ((pushforward g).obj ℱ).finrankH k q = ℱ.finrankH k q := by
  obtain ⟨e⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k g q
  exact ((e.app ⟨ℱ, inferInstance⟩).toLinearEquiv.finrank_eq).symm

/-- `h^q` is invariant under pullback along an isomorphism of `k`-schemes. -/
theorem finrankH_pullback_of_isIso {k : Type u} [Field k] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] (e : Y ⟶ Z) [IsIso e]
    [e.IsOver (Spec (.of k))] (M : Z.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((Modules.pullback e).obj M).finrankH k q = M.finrankH k q := by
  have : (inv e).IsOver (Spec (.of k)) := by
    rw [Scheme.Hom.isOver_iff, IsIso.inv_comp_eq, (Scheme.Hom.isOver_iff _).1 ‹e.IsOver _›]
  rw [finrankH_congr k ((pullbackIsoPushforwardInv e).app M) q,
    finrankH_pushforward_of_isAffineHom k (inv e) M q]

/-- The Euler characteristic is invariant under pushforward along an affine morphism:
`χ(Y, g_* ℱ) = χ(X, ℱ)` for a quasi-coherent `𝒪_X`-module `ℱ`. -/
theorem eulerChar_pushforward_of_isAffineHom (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    [IsAffineHom g] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((pushforward g).obj ℱ).eulerChar k = ℱ.eulerChar k := by
  simp only [eulerChar, finrankH_pushforward_of_isAffineHom k g ℱ]

end AffineMorphism

end AlgebraicGeometry.Scheme.Modules
