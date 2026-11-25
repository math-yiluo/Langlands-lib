/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.EtaleEdgeMapBaseChange
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangeGeometricPoints
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.Gabber
import Mathlib.Order.CompletePartialOrder

/-! # Acyclic closed term for a dense-open counit -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

private theorem bijective_finite_pushforward_comparison
    {Z Z' X X' : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'}
    {i : Z ⟶ X} {v : X' ⟶ X} (sq : IsPullback g i' i v) [IsFinite i]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (hG : Function.Bijective (cohomologyMap g G n)) :
    Function.Bijective (cohomologyMap v ((i)_*[AddCommGrpCat.{u + 1}].obj G) n) := by
  have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
  obtain ⟨hleft, hright⟩ := bijective_edgeMap_baseChange sq G n inferInstance
  have hb : Function.Bijective
      ((cohomologyMap g G n).comp
        ((Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit.app G) n)
          |>.comp (cohomologyMap i ((i)_*[AddCommGrpCat.{u + 1}].obj G) n))) :=
    hG.comp hleft
  rw [cohomology_edgeMap_baseChange sq G n] at hb
  exact (Function.Bijective.of_comp_iff' hright _).mp hb

/-- The dense-open counit has a short exact cokernel with acyclic degree-one
cohomology on both sides of the field extension and bijective degree-zero comparison.
Source: Stacks Project, Tag 0GJA, proof (five-term exact sequence and remark (c)).
(blueprint: lem-pbc-k2-dense-open-closed-term)

Proof: take the reduced induced closed complement i:Z → X and let B be the underlying
abelian sheaf of i_*i^*F. The open-closed exact sequence, followed by the exact forgetful
functor, gives the asserted short complex. Density excludes the generic points of the
Noetherian curve, so Z is zero dimensional and finite. Its closed points have residue
field k. Finite direct image is exact, so Leray identifies the cohomology of B with
that of i^*F on Z. The latter is a finite product of stalks in degree zero and vanishes
in positive degrees. Closed-immersion base change identifies the inverse image of B
with the analogous closed direct image over k'. The complement after base change is
again a finite union of algebraically closed points. The canonical degree-zero
comparison is the product of the inverse-image stalk identifications, hence bijective.
Empty schemes and the full open give zero closed terms and satisfy the same assertions.
-/
theorem dense_open_closed_term (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let A := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    ∃ (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (b : A ⟶ B)
      (w : ε ≫ b = 0),
      (ShortComplex.mk ε b w).ShortExact ∧
      Function.Bijective (cohomologyMap ι' B 0) ∧
      Subsingleton (Sheaf.H B 1) ∧
      Subsingleton (Sheaf.H (((ι')^*[AddCommGrpCat.{u + 1}]).obj B) 1) := by
  let E := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hij : Set.range U.closedComplement.base = (Set.range U.ι.base)ᶜ := by
    rw [U.range_closedComplement, Scheme.Opens.range_ι]
  let S := openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι U.closedComplement
    (disjoint_range_of_range_eq_compl _ _ hij) F
  have hS : (S.map E).ShortExact := shortExact_map_forget₂ Λ
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι U.closedComplement F hij)
  let B := (S.map E).X₃
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ X := U.closedComplement
  have hdim : topologicalKrullDim Z ≤ 0 := by
    obtain ⟨n, V, hVU, _, _, _, hVdim, _⟩ := exists_dense_irreducible_opens f U hU
    let b : Z → ↥(⋃ a, (V a : Set X))ᶜ := fun z ↦ ⟨i.base z, by
      have hz : i.base z ∈ (U : Set X)ᶜ := U.range_closedComplement ▸ ⟨z, rfl⟩
      intro hv
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
      exact hz (hVU a ha)⟩
    have hb : Topology.IsInducing b :=
      (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp
        i.isClosedEmbedding.isInducing
    exact hb.topologicalKrullDim_le.trans hVdim
  let G := (sheafCompose Z.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((i)^*[ModuleCat.{u + 1} Λ].obj F)
  have hB : Subsingleton (Sheaf.H B 1) := by
    have hG := (zero_dimensional_etale_cohomology k Z (i ≫ f) hdim G
      (fun z ↦ AlgebraicClosure (Z.residueField z)) Z.algClosurePoint
      (fun z ↦ Z.algClosurePoint_base z default)).2.1 1 (by decide)
    let e := (Scheme.nonempty_sheafH_extDerivedIso Z 1).some.app G
    have : Subsingleton (Sheaf.H G 1) := by
      constructor
      intro x y
      exact e.addCommGroupIsoToAddEquiv.injective (hG.elim _ _)
    have : Subsingleton (Sheaf.H
        ((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).obj G) 1) :=
      inferInstanceAs (Subsingleton (Sheaf.H G 1))
    change Subsingleton (Sheaf.H ((i)_*[AddCommGrpCat.{u + 1}].obj G) 1)
    exact (bijective_edgeMap_of_isFinite i G 1).injective.subsingleton
  let Z' := CategoryTheory.Limits.pullback i ι'
  let i' : Z' ⟶ X' := CategoryTheory.Limits.pullback.snd i ι'
  let g : Z' ⟶ Z := CategoryTheory.Limits.pullback.fst i ι'
  have sq : IsPullback g i' i ι' := IsPullback.of_hasPullback i ι'
  have sqk : IsPullback g (i' ≫ f') (i ≫ f) ι := sq.paste_vert h
  let : IsCurve (i ≫ f) := ⟨hdim.trans (by norm_num)⟩
  obtain ⟨hf', hdim', _⟩ := zeroDimensional_baseChange_geometric_points (i ≫ f) hdim sqk
  let : IsCurve (i' ≫ f') := hf'
  have hB' : Subsingleton (Sheaf.H ((ι')^*[AddCommGrpCat.{u + 1}].obj B) 1) := by
    let G' := (g)^*[AddCommGrpCat.{u + 1}].obj G
    have hG' := (zero_dimensional_etale_cohomology k' Z' (i' ≫ f') hdim' G'
      (fun z ↦ AlgebraicClosure (Z'.residueField z)) Z'.algClosurePoint
      (fun z ↦ Z'.algClosurePoint_base z default)).2.1 1 (by decide)
    let e := (Scheme.nonempty_sheafH_extDerivedIso Z' 1).some.app G'
    have : Subsingleton (Sheaf.H G' 1) := by
      constructor
      intro x y
      exact e.addCommGroupIsoToAddEquiv.injective (hG'.elim _ _)
    have : IsFinite i' := isFinite_of_isPullback sq
    have : Subsingleton (Sheaf.H
        ((𝟭 (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1})).obj G') 1) :=
      inferInstanceAs (Subsingleton (Sheaf.H G' 1))
    have hpush : Subsingleton (Sheaf.H ((i')_*[AddCommGrpCat.{u + 1}].obj G') 1) :=
      (bijective_edgeMap_of_isFinite i' G' 1).injective.subsingleton
    have := isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
    let c := (asIso (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app G
    change Subsingleton (Sheaf.H ((ι')^*[AddCommGrpCat.{u + 1}].obj
      ((i)_*[AddCommGrpCat.{u + 1}].obj G)) 1)
    let : Subsingleton (Sheaf.H (((g)^*[AddCommGrpCat.{u + 1}] ⋙
      (i')_*[AddCommGrpCat.{u + 1}]).obj G) 1) := hpush
    exact (Function.LeftInverse.injective (f := Sheaf.H.map c.hom 1)
      (g := Sheaf.H.map c.inv 1) fun x ↦ by
        rw [← Sheaf.H.map_comp_apply, c.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton
  refine ⟨B, (S.map E).g, (S.map E).zero, hS, ?_, hB, hB'⟩
  change Function.Bijective (cohomologyMap ι' ((i)_*[AddCommGrpCat.{u + 1}].obj G) 0)
  apply bijective_finite_pushforward_comparison sq G 0
  let G' := (g)^*[AddCommGrpCat.{u + 1}].obj G
  let e : Sheaf.H G 0 ≃+ (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G :=
    (Sheaf.H.equiv₀ G CategoryTheory.Limits.terminalIsTerminal).trans
      (((Sheaf.ΓNatIsoSheafSections _ _ CategoryTheory.Limits.terminalIsTerminal).symm.app G)
        |>.addCommGroupIsoToAddEquiv)
  let e' : Sheaf.H G' 0 ≃+ (Sheaf.Γ Z'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G' :=
    (Sheaf.H.equiv₀ G' CategoryTheory.Limits.terminalIsTerminal).trans
      (((Sheaf.ΓNatIsoSheafSections _ _ CategoryTheory.Limits.terminalIsTerminal).symm.app G')
        |>.addCommGroupIsoToAddEquiv)
  have hΓ := bijective_globalSectionsUpperStarMap_of_dim_zero (i ≫ f) hdim sqk G
  have he (x : Sheaf.H G 0) : cohomologyMap g G 0 x =
      e'.symm (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g G (e x)) := by
    have hh := cohomologyMap_zero_eq_globalSectionsUpperStarMap g G (e x)
    change cohomologyMap g G 0 (e.symm (e x)) =
      e'.symm (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g G (e x)) at hh
    simpa only [AddEquiv.symm_apply_apply] using hh
  have heq : ⇑(cohomologyMap g G 0) =
      e'.symm ∘ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g G ∘ e := funext he
  rw [heq]
  exact e'.symm.bijective.comp (hΓ.comp e.bijective)

end AlgebraicGeometry.IsCurve
