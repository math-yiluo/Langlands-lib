/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Flat bottom homology and its truncation arrow
Source: Stacks Project, Tag 0BDL, zero-matrix chart argument.
(blueprint: lem-sc-local-zero-bottom-truncation). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The bottom homology of local zero-differential models is flat and admits a
bottom truncation arrow inducing an isomorphism on bottom homology.
Source: Stacks Project, Tag 0BDL, zero-matrix chart argument, and standard truncation.
(blueprint: lem-sc-local-zero-bottom-truncation).

Proof: Exact restriction identifies H^i(D)|U with H^i(K). For i<a this is zero.
At a, both adjacent differentials vanish, so H^a(K) is canonically K.X a.
Thus H^a(D) is locally finite free, hence flat. Vanishing of H^i(D) for i<a
is local, so D lies in D^{>=a}. The canonical truncation tau_{<=a}D -> D
has an isomorphism on H^a. Its source has cohomology in degree a only,
so the single-cohomology identification gives H^a(D)[-a] -> D.
Restriction preserves this arrow and its homology map. The construction works
also on the empty scheme, for the zero sheaf, and for every integer a. -/
theorem localZeroBottomModel_truncation
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (hmodel :
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧ K.d a (a + 1) = 0 ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        Nonempty ((derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K))
:
    SheafOfModules.IsFlat ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj D) ∧
    ∃ f : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj D) ⟶ D,
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).map f)  := by
  classical
  let C := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let H := DerivedCategory.homologyFunctor C a
  let M := H.obj D
  have hlocal : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ n : ℕ,
      Nonempty ((Modules.restrictFunctor U.ι).obj M ≅ SheafOfModules.free
        (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n))) := by
    intro t
    obtain ⟨U, htU, K, hb, hn, hz, hfree, ⟨e⟩⟩ := hmodel t
    obtain ⟨n, ⟨en⟩⟩ := hfree a
    obtain ⟨er⟩ := Modules.nonempty_homology_derivedOpenPullback_iso_restrict U D a
    have hf : (K.sc a).f = 0 := by
      change K.d ((ComplexShape.up ℤ).prev a) a = 0
      rw [(ComplexShape.up ℤ).prev_eq' (by omega : (a - 1) + 1 = a)]
      exact (hn (a - 1) (by omega)).eq_of_src _ _
    have hg : (K.sc a).g = 0 := by
      change K.d a ((ComplexShape.up ℤ).next a) = 0
      rw [(ComplexShape.up ℤ).next_eq' (by rfl : a + 1 = a + 1)]
      exact hz
    exact ⟨U, htU, n, ⟨er.symm ≪≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) a).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) a).app K ≪≫
      (ShortComplex.HomologyData.ofZeros (K.sc a) hf hg).left.homologyIso ≪≫ en⟩⟩
  choose U hU n eU using hlocal
  have hcover : ⨆ t, U t = ⊤ := by
    ext t
    change t ∈ (⨆ t, U t : T.Opens) ↔ t ∈ (⊤ : T.Opens)
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hU t⟩
  have : M.IsFiniteLocallyFree :=
    Modules.isFiniteLocallyFree_of_restrict_iso_free M (fun t ↦ (U t).ι)
      (by simpa using hcover) (fun t ↦ ULift.{u} (Fin (n t))) eU
  let := SheafOfModules.monoidalCategory T.sheaf
  let := SheafOfModules.symmetricCategory T.sheaf
  have hex := Modules.finiteLocallyFree_tensorLeft_exact M
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft M) := hex.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft M) := hex.2
  have hflat : SheafOfModules.IsFlat M := by
    exact ⟨preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight M),
      preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)⟩
  have hneg (i : ℤ) (hi : i < a) :
      IsZero ((DerivedCategory.homologyFunctor C i).obj D) := by
    let N := (DerivedCategory.homologyFunctor C i).obj D
    have hloc : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧
        IsZero ((Modules.restrictFunctor W.ι).obj N) := by
      intro t
      obtain ⟨W, htW, K, hb, hn, hz, hfree, ⟨e⟩⟩ := hmodel t
      obtain ⟨er⟩ := Modules.nonempty_homology_derivedOpenPullback_iso_restrict W D i
      have hzero : IsZero (K.homology i) :=
        ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i) (hn i hi)
      exact ⟨W, htW, hzero.of_iso
        (er.symm ≪≫ (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).mapIso e ≪≫
          (DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).app K)⟩
    choose W hW hzero using hloc
    have hc : ⨆ t, W t = ⊤ := by
      ext t
      change t ∈ (⨆ t, W t : T.Opens) ↔ t ∈ (⊤ : T.Opens)
      constructor
      · intro _
        trivial
      · intro _
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hW t⟩
    exact Modules.isZero_of_iSup_eq_top N W hc hzero
  have : D.IsGE a := (DerivedCategory.isGE_iff D a).mpr hneg
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE D a
  let P := K.truncLE a
  let b : DerivedCategory.Q.obj P ⟶ D :=
    DerivedCategory.Q.map (K.ιTruncLE a) ≫ e.inv
  have hb : IsIso (H.map b) := by
    have hq : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE a) a) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
    have : IsIso (H.map (DerivedCategory.Q.map (K.ιTruncLE a))) :=
      (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C a) _).2 hq
    dsimp [b]
    rw [Functor.map_comp]
    infer_instance
  have : (DerivedCategory.Q.obj P).IsGE a := by infer_instance
  have : (DerivedCategory.Q.obj P).IsLE a := by infer_instance
  obtain ⟨N, ⟨eN⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj P) a
  let eM : N ≅ M :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C a).app N).symm ≪≫
      H.mapIso eN.symm ≪≫ asIso (H.map b)
  let f : (DerivedCategory.singleFunctor C a).obj M ⟶ D :=
    (DerivedCategory.singleFunctor C a).map eM.inv ≫ eN.inv ≫ b
  refine ⟨hflat, f, ?_⟩
  dsimp [f]
  simp only [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme
