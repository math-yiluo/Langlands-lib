/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChangeBoundary

/-! # Dense-open field-extension comparison ingredients -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- After algebraically closed field extension the inverse image of the dense-open
counit induces bijections in degrees above one.
Source: Stacks Project, Tag 0GJA, proof (higher-degree isomorphisms and remark (c)).
(blueprint: lem-pbc-x2-dense-open-pulled-counit-high)

Proof: Form the reduced closed complement Z. It is zero-dimensional, finite and discrete,
with residue fields k, by density and the dimension bound on the Noetherian curve.
The open-closed short exact sequence has first arrow the counit and last term i_*i^*F.
Forgetting coefficients and inverse image are exact. Finite exact direct image and Leray
identify the last term's cohomology after base change with that on Z times_k k'. This
scheme is a finite union of spectra of k', so all its positive cohomology vanishes.
The long exact sequence makes the pulled-back counit bijective in degrees above one.
The map is the inverse image of the original counit itself; no chosen identification
with a different extension-by-zero object occurs in the conclusion. -/
theorem dense_open_pulled_counit_high (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    ∀ q : ℕ, 1 < q → Function.Bijective
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map ε) q) := by
  dsimp only
  let εΛ := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) U.ι).counit.app F
  let ε := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map εΛ
  let V := ι' ⁻¹ᵁ U
  obtain ⟨hfin, hcl, hsep⟩ := dense_open_baseChange_boundary f h U hU
  have hε : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map ε) := by
    obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ U.ι
    exact (NatIso.isIso_map_iff e εΛ).mp (by
      change IsIso ((sheafCompose (U : Scheme.{u}).smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((U.ι)^*[ModuleCat.{u + 1} Λ].map εΛ))
      infer_instance)
  have hε' : IsIso ((V.ι)^*[AddCommGrpCat.{u + 1}].map
      (((ι')^*[AddCommGrpCat.{u + 1}]).map ε)) := by
    let e := (upperStarComp AddCommGrpCat.{u + 1} V.ι ι').symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} (ι' ∣_ U) U.ι (V.ι ≫ ι')
        (morphismRestrict_ι ι' U).symm
    exact (NatIso.isIso_map_iff e ε).mpr (by
      change IsIso (((ι' ∣_ U)^*[AddCommGrpCat.{u + 1}]).map
        ((U.ι)^*[AddCommGrpCat.{u + 1}].map ε))
      infer_instance)
  intro q hq
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  exact bijective_H_map_of_isIso_upperStar_map V hfin hcl hsep
    (((ι')^*[AddCommGrpCat.{u + 1}]).map ε) hε' n

end AlgebraicGeometry.IsCurve
