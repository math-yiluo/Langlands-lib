import Langlands.GroupScheme.IntegralModel.UnramifiedTorusPowerIntegrality
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.Torus.LocalRootSupportComparison
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism
import Langlands.GroupScheme.Rational.TorusSplitPart
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Integrality from a power for models with a torus special fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- A split torus in a commutative affine group of finite type over a field has no roots. -/
theorem roots_eq_empty_of_isCommMonObj {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsCommMonObj G.X]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : roots i = ∅ := by
  classical
  have hc : IsCentral i :=
    isCentral_to_commGroupScheme (H := { toGrp := G, comm := inferInstance }) i
  ext χ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hχ, hne⟩
  have hd := (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSupIndep
    |>.pairwiseDisjoint hχ
  change Disjoint (weightSpace i χ) (weightSpace i 0) at hd
  rw [weightSpace_zero_eq_top_of_isCentral _ hc, disjoint_top] at hd
  exact hne hd

namespace IntegralModel

section Generic

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {H : GroupScheme (Spec (CommRingCat.of K))}
  (N : IntegralModel R K H)

/-- If the generic fibre of a split torus of the model is an isomorphism onto the generic group,
every rational point is a generic split-torus value. -/
theorem exists_genericSplitTorusValue_eq_of_isIso {I : Type u} [Finite I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ N.group)
    [IsIso (N.genericSplitTorusHom i)] (y : rationalPoints H) :
    ∃ t : I → Kˣ, N.genericSplitTorusValue i t = y := by
  let x : rationalPoints (splitTorus (Spec (CommRingCat.of K)) I) :=
    y ≫ (inv (N.genericSplitTorusHom i)).hom.hom
  refine ⟨fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom
    (splitTorus.pointsEquiv I (Over.mk (𝟙 _)) x j), ?_⟩
  have hs : (fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom
        (splitTorus.pointsEquiv I (Over.mk (𝟙 _)) x j))) =
      splitTorus.pointsEquiv I (Over.mk (𝟙 _)) x := by
    funext j
    ext
    exact (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _
  rw [genericSplitTorusValue, hs, MulEquiv.symm_apply_apply]
  change (y ≫ (inv (N.genericSplitTorusHom i)).hom.hom) ≫ (N.genericSplitTorusHom i).hom.hom = y
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

end Generic

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {L : GroupScheme (Spec (CommRingCat.of F))}
  (Z : IntegralModel ↥𝒪[F] F L)

local instance torusModelPowerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance torusModelPowerResidueAlgebra :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- The base points of the residue fibre of the unramified base change factor through the
special fibre. -/
theorem unramifiedResidue_specMap_comp :
    Spec.algebraMap (fixedFieldIntegers F) (IsLocalRing.ResidueField (fixedFieldIntegers F)) ≫
        Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) =
      Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) ≫
        Spec.algebraMap ↥𝒪[F] 𝓀[F] := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The residue fibre of the unramified base change of `Z` is the base change of the special
fibre of `Z` along the residue extension. -/
def unramifiedResidueIso :
    (GroupScheme.baseChange (Spec.algebraMap (fixedFieldIntegers F)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj Z.baseChangeUnramified.group ≅
      (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj
          ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj Z.group) :=
  (baseChangeCompIso (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      (Spec.algebraMap (fixedFieldIntegers F) (IsLocalRing.ResidueField (fixedFieldIntegers F)))
      Z.group).symm ≪≫
    eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj Z.group)
      unramifiedResidue_specMap_comp) ≪≫
    baseChangeCompIso (Spec.algebraMap ↥𝒪[F] 𝓀[F])
      (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))) Z.group

variable (hL : IsConnectedReductive L)
  (hspecial : IsTorus ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj Z.group))

include hL hspecial in
/-- **A split torus filling the unramified generic fibre.** If the generic group `L` is
connected reductive and the special fibre of `Z` is a torus, the unramified base change of `Z`
has a closed split torus whose generic fibre is an isomorphism onto the generic group. -/
theorem exists_isIso_genericSplitTorusHom_baseChangeUnramified :
    ∃ (I : Type u) (_ : Finite I)
      (j : splitTorus (Spec (CommRingCat.of (fixedFieldIntegers F))) I ⟶
        Z.baseChangeUnramified.group),
      IsClosedSubgroup j ∧ IsIso (Z.baseChangeUnramified.genericSplitTorusHom j) := by
  classical
  have hSpecialCR := hspecial.isConnectedReductive_of_fieldSplitting
  obtain ⟨T, i, ⟨I, hI, ⟨e⟩⟩, hic, hmax, -⟩ :=
    Z.exists_isMaximalSplitTorus_baseChangeUnramified hL hSpecialCR
  let := Fintype.ofFinite I
  have hZ' : IsReductive Z.baseChangeUnramified.group :=
    Z.isReductive_baseChangeUnramified hL hSpecialCR
  let := hZ'.smooth
  let := hZ'.isAffineHom
  let j : splitTorus (Spec (CommRingCat.of (fixedFieldIntegers F))) I ⟶
      Z.baseChangeUnramified.group := e.inv ≫ i
  have hj : IsClosedSubgroup j := IsClosedSubgroup.iso_comp e.symm hic
  refine ⟨I, hI, j, hj, ?_⟩
  have hsplit (k : Type u) [Field k] :
      IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp :=
    ⟨I, hI, ⟨Iso.refl _⟩⟩
  -- The residue fibre of the unramified model is a torus, hence commutative.
  let κ := IsLocalRing.ResidueField (fixedFieldIntegers F)
  have hκtorus : IsTorus ((GroupScheme.baseChange
      (algebraBaseMap (fixedFieldIntegers F) κ)).obj Z.baseChangeUnramified.group) :=
    IsTorus.of_iso Z.unramifiedResidueIso (hspecial.baseChange (K := κ))
  let := hκtorus.isCommMonObj
  let : IsAffineHom ((GroupScheme.baseChange
      (algebraBaseMap (fixedFieldIntegers F) κ)).obj Z.baseChangeUnramified.group).X.hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let : LocallyOfFiniteType ((GroupScheme.baseChange
      (algebraBaseMap (fixedFieldIntegers F) κ)).obj Z.baseChangeUnramified.group).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  -- So the torus has no roots there, and hence none on the generic fibre.
  have hκ : roots (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := κ) Z.baseChangeUnramified.group I j) = ∅ :=
    roots_eq_empty_of_isCommMonObj (hsplit κ) _
  have hF' : roots (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := inertiaFixedField F)
        Z.baseChangeUnramified.group I j) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro α hα
    exact Set.eq_empty_iff_forall_notMem.mp hκ _
      (splitTorus.fieldRootsEquiv (k := inertiaFixedField F) (l := κ) I
        Z.baseChangeUnramified.group j ⟨α, hα⟩).2
  -- The generic fibre is connected reductive and the torus is maximal there.
  have hCR : IsConnectedReductive ((GroupScheme.baseChange
      (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj
        Z.baseChangeUnramified.group) :=
    fieldReductive_of_residueReductive _ Set.univ
      (fun t _ => hZ'.isConnectedReductive_residueFiber t) _ (Set.mem_univ _)
  have hmax' : IsMaximalTorus (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := inertiaFixedField F)
        Z.baseChangeUnramified.group I j) :=
    IsMaximalTorus.of_eq_iso_comp_comp_iso hmax
      ((splitTorus.baseChangeIso
          (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) I).symm ≪≫
        (GroupScheme.baseChange
          (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).mapIso e.symm)
      Z.baseChangeUnramified.genericIso.symm
      (by simp [genericTorusMap, splitTorus.baseChangeHom, j])
  have := hCR.isIso_of_roots_eq_empty (hsplit _) hmax' hF'
  change IsIso (splitTorus.baseChangeHom (K := inertiaFixedField F)
    Z.baseChangeUnramified.group I j ≫ Z.baseChangeUnramified.genericIso.hom)
  infer_instance

include hL hspecial in
/-- **Integrality from a power for a model with torus special fibre.** Let `Z` be a model over
`𝒪[F]` of a connected reductive group `L` whose special fibre is a torus. If a positive power
of a rational point of `L` is integral, the point is integral. -/
theorem mem_integralPoints_of_pow_mem_of_isTorus_special {g : rationalPoints L} {n : ℕ}
    (hn : n ≠ 0) (hgn : g ^ n ∈ Z.integralPoints) : g ∈ Z.integralPoints := by
  obtain ⟨I, hI, j, hj, hiso⟩ :=
    Z.exists_isIso_genericSplitTorusHom_baseChangeUnramified hL hspecial
  obtain ⟨t, ht⟩ := Z.baseChangeUnramified.exists_genericSplitTorusValue_eq_of_isIso j
    (rationalExtend F (inertiaFixedField F) L g)
  exact Z.mem_integralPoints_of_pow_mem_of_unramifiedSplitTorus j hj ht.symm hn hgn

end IntegralModel

end Langlands.GroupScheme
