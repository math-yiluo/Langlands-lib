/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkHomLift
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkHomEquality

/-! # A stalk inverse extends to a vector bundle neighbourhood

Source: Stacks Project, Tags 05GF and 00O0, Lemmas 10.79.2 and 10.79.4(3).
(blueprint: lem-sc-finite-locally-free-stalk-iso-neighborhood)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free map invertible at one stalk is invertible on an open
neighbourhood of that point.
Source: Stacks Project, Tags 05GF and 00O0, Lemmas 10.79.2 and 10.79.4(3).
(blueprint: lem-sc-finite-locally-free-stalk-iso-neighborhood)

Proof: Intersect finite free trivializing neighbourhoods for M and N at x. In
these frames φ is a finite rectangular matrix of sections. Its stalk inverse
is a finite matrix of germs. Represent its finitely many entries by sections
and intersect their domains with the trivializing neighbourhood. The identities
AB = 1 and BA = 1 hold as germs. There are finitely many entries in the two
matrix identities; for each entry the germ equality criterion supplies a smaller
neighbourhood where the equality holds. Intersect all of them. The resulting
matrix of sections defines a morphism N to M on that open, and the two matrix
identities give a two-sided inverse to the restricted map. For an open immersion,
the restriction functor is naturally isomorphic to tensor pullback: both are
left adjoints of the same pushforward. Naturality transports the inverse to the
map written here. Zero ranks cause no difficulty: the corresponding finite
families and identity matrices are empty. No noetherian hypothesis is needed. -/
theorem exists_isIso_tensorPullback_of_isIso_moduleStalkMap
    {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N) (x : W)
    (hφ : IsIso ((RingedSpace.moduleStalkFunctor W.toRingedSpace x).map φ)) :
    ∃ U : W.Opens, x ∈ U ∧ IsIso ((tensorPullback U.ι).map φ) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  let S := RingedSpace.moduleStalkFunctor W.toRingedSpace x
  let : IsIso (S.map φ) := hφ
  obtain ⟨U, hxU, ψ, hψ⟩ := exists_restrict_stalk_hom_lift N M x (inv (S.map φ))
  let R := restrictFunctor U.ι
  have germ_map (V : U.toScheme.Opens) (hxV : (⟨x, hxU⟩ : U.toScheme) ∈ V)
      (m : Γ(R.obj M, V)) :
      S.map φ (M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ m) =
        N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
          (Hom.app (R.map φ) V m) := by
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _
      (Hom.mapPresheaf φ) m
  have hleft : ∀ (V : U.toScheme.Opens) (hxV : (⟨x, hxU⟩ : U.toScheme) ∈ V)
      (m : Γ(R.obj M, V)),
      M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
          (Hom.app (R.map φ ≫ ψ) V m) =
        M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
          (Hom.app (𝟙 (R.obj M)) V m) := by
    intro V hxV m
    change M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
        (Hom.app ψ V (Hom.app (R.map φ) V m)) =
      M.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ m
    rw [hψ V hxV, ← germ_map V hxV m]
    exact ConcreteCategory.congr_hom (IsIso.hom_inv_id (S.map φ)) _
  have hright : ∀ (V : U.toScheme.Opens) (hxV : (⟨x, hxU⟩ : U.toScheme) ∈ V)
      (m : Γ(R.obj N, V)),
      N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
          (Hom.app (ψ ≫ R.map φ) V m) =
        N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
          (Hom.app (𝟙 (R.obj N)) V m) := by
    intro V hxV m
    change N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩
        (Hom.app (R.map φ) V (Hom.app ψ V m)) =
      N.presheaf.germ (U.ι ''ᵁ V) x ⟨⟨x, hxU⟩, hxV, rfl⟩ m
    rw [← germ_map V hxV, hψ V hxV]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (S.map φ)) _
  obtain ⟨V, hxV, hVU, hV⟩ :=
    exists_shrink_restrict_hom_eq_of_germs M M x U hxU (R.map φ ≫ ψ) (𝟙 _) hleft
  obtain ⟨Z, hxZ, hZU, hZ⟩ :=
    exists_shrink_restrict_hom_eq_of_germs N N x U hxU (ψ ≫ R.map φ) (𝟙 _) hright
  let T := V ⊓ Z
  have hxT : x ∈ T := ⟨hxV, hxZ⟩
  have hTU : T ≤ U := inf_le_left.trans hVU
  let Q := restrictFunctor (W.homOfLE hTU)
  have shrink_eq {A B : U.toScheme.Modules} (f g : A ⟶ B)
      (P : W.Opens) (hPU : P ≤ U) (hTP : T ≤ P)
      (h : (restrictFunctor (W.homOfLE hPU)).map f =
        (restrictFunctor (W.homOfLE hPU)).map g) : Q.map f = Q.map g := by
    let e := restrictFunctorCongr (W.homOfLE_homOfLE hTP hPU).symm ≪≫
      restrictFunctorComp (W.homOfLE hTP) (W.homOfLE hPU)
    apply (cancel_mono (e.hom.app B)).mp
    rw [e.hom.naturality f, e.hom.naturality g]
    change e.hom.app A ≫ (restrictFunctor (W.homOfLE hTP)).map
      ((restrictFunctor (W.homOfLE hPU)).map f) = _
    rw [h]
    rfl
  have hL := shrink_eq _ _ V hVU inf_le_left hV
  have hR := shrink_eq _ _ Z hZU inf_le_right hZ
  change Q.map (R.map φ ≫ ψ) = Q.map (𝟙 (R.obj M)) at hL
  change Q.map (ψ ≫ R.map φ) = Q.map (𝟙 (R.obj N)) at hR
  have : IsIso (Q.map (R.map φ)) := by
    refine ⟨⟨Q.map ψ, ?_, ?_⟩⟩
    · exact (Q.map_comp (R.map φ) ψ).symm.trans (hL.trans (Q.map_id (R.obj M)))
    · exact (Q.map_comp ψ (R.map φ)).symm.trans (hR.trans (Q.map_id (R.obj N)))
  let e := restrictFunctorCongr (W.homOfLE_ι hTU).symm ≪≫
    restrictFunctorComp (W.homOfLE hTU) U.ι
  have : IsIso ((restrictFunctor T.ι).map φ) :=
    (NatIso.isIso_map_iff e φ).mpr (by
      change IsIso (Q.map (R.map φ))
      infer_instance)
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction T.ι
  let d := (restrictAdjunction T.ι).leftAdjointUniq adj
  exact ⟨T, hxT, (NatIso.isIso_map_iff d φ).mp inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
