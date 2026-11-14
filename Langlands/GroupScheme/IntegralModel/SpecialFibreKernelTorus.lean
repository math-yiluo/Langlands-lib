import Langlands.GroupScheme.Absolute.KernelMaximalTorusIdentityComponent
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.Torus.HenselianSplitRank
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Unipotent special-fibre kernels from a common closed split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SplitTorusClosure

open GaloisPointComparison Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **The standard split torus of the model from bounded points, for a fixed splitting.** Let
`R` be a noetherian valuation ring with infinite residue field and fraction field `K`, and `v`
a valuation of `K` that is one on the units of `R`. Let `iT : T → G` be a closed subgroup and
`e : T ≅ 𝔾_m^I` a splitting. If the image of the character valuation kernel of `T` lies in the
integral points of `M`, then `iT` extends to a closed subgroup `D_R(ℤ^I) → M` whose generic
fibre is `iT` precomposed with the generic identification determined by `e`. -/
theorem exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded
    [ValuationRing R] [Infinite (IsLocalRing.ResidueField R)]
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {I : Type u} [Fintype I] [DecidableEq I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (iT : T.toGrp ⟶ G) (hiT : IsClosedSubgroup iT)
    (hb : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      M.integralPoints) :
    ∃ j : (torus R I).toGrp ⟶ M.group, IsClosedSubgroup j ∧
      M.genericTorusMap (torus R I) j = (genericSplitIso R K I).hom ≫ e.inv ≫ iT :=
  exists_isClosedSubgroup_genericTorusMap_eq M R K e iT hiT
    (fun t => by
      rw [mem_baseChange_self_coefficientIntegralPoints_iff]
      apply hb
      refine ⟨rationalPoints.map e.inv
        ((rationalCoeffEquiv K _).symm
          ((splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I K).symm
            (fun i => Units.map (algebraMap R K : R →* K) (t i)))), ?_, ?_⟩
      · exact map_characterValuationKernel_le v _
          ⟨_, rationalCoeffEquiv_symm_mem_characterValuationKernel K I v _
            (fun i => hv (t i)), rfl⟩
      · apply (rationalCoeffEquiv K G).injective
        rw [MulEquiv.apply_symm_apply]
        change rationalCoeffEquiv K G
          (rationalPoints.map iT (rationalPoints.map e.inv _)) = _
        rw [rationalCoeffEquiv_map, rationalCoeffEquiv_map, MulEquiv.apply_symm_apply,
          affinePointsTarget_apply, affinePointsTarget_apply, Category.assoc])
    (fun x hx => hx)

end Langlands.GroupScheme.IntegralModel.SplitTorusClosure

namespace Langlands.GroupScheme.IntegralModel

open Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- **Rigidity of torus maps under a model morphism.** If `ψ : M → N` is a model morphism with
identity generic fibre and `j' : 𝒮 → M`, `j : 𝒮 → N` are homomorphisms from a flat group
scheme over `R` with the same generic fibre in `G`, then `j' ≫ ψ = j`. -/
theorem Hom.comp_eq_of_genericTorusMap_eq {M N : IntegralModel R K G} (ψ : M.Hom N (𝟙 G))
    {𝒮 : CommGroupScheme (Spec (CommRingCat.of R))} [Flat 𝒮.toGrp.X.hom]
    {j' : 𝒮.toGrp ⟶ M.group} {j : 𝒮.toGrp ⟶ N.group}
    (h : M.genericTorusMap 𝒮 j' = N.genericTorusMap 𝒮 j) : j' ≫ ψ.hom = j := by
  have hK : (GroupScheme.baseChange (Spec.algebraMap R K)).map (j' ≫ ψ.hom) =
      (GroupScheme.baseChange (Spec.algebraMap R K)).map j := by
    apply (cancel_mono N.genericIso.hom).mp
    rw [Functor.map_comp, Category.assoc, ψ.generic_comm, Category.comp_id]
    exact h
  apply Grp.hom_ext
  exact Langlands.AbelianScheme.genericFibre_map_injective K
    (congrArg (fun f => f.hom.hom) hK)

private theorem isMaximalSplitTorus_iso_comp {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (e : T.toGrp ≅ T'.toGrp) {i : T'.toGrp ⟶ H}
    (hi : IsMaximalSplitTorus i) : IsMaximalSplitTorus (e.hom ≫ i) := by
  refine ⟨⟨IsSplitTorus.of_iso e hi.1.1, hi.1.2.iso_comp e⟩, ?_⟩
  intro A a ha f hf
  have hfac : (e.inv ≫ f) ≫ a = i := by
    rw [Category.assoc, hf, Iso.inv_hom_id_assoc]
  have h := hi.2 A a ha (e.inv ≫ f) hfac
  exact (isIso_comp_left_iff e.inv f).mp h

section Residue

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- **A maximal torus of the special fibre.** Over a Henselian local domain with algebraically
closed residue field, let `M` be a smooth model of a connected reductive group `G`. A closed
split torus `j : 𝒮 → M` whose generic fibre is a maximal split torus of `G` has a maximal torus
of the special fibre as its special fibre. -/
theorem isMaximalTorus_specialFibre_of_generic (hG : IsConnectedReductive G)
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    {𝒮 : CommGroupScheme (Spec (CommRingCat.of R))} (h𝒮 : IsSplitTorus 𝒮.toGrp)
    {j : 𝒮.toGrp ⟶ M.group} (hj : IsClosedSubgroup j)
    (hmax : IsMaximalSplitTorus (M.genericTorusMap 𝒮 j)) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj 𝒮)
      ((GroupScheme.baseChange (residueBaseMap R)).map j) := by
  have hjK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j) :=
    (IsMaximalSplitTorus.comp_iso_iff _ M.genericIso).mp hmax
  have hres := isMaximalSplitTorus_residue_of_generic
    (IsLocalRing.residue_surjective : Function.Surjective
      (algebraMap R (IsLocalRing.ResidueField R)))
    M.group (hG.of_iso M.genericIso) 𝒮 h𝒮 j hj hjK
  exact hres.isMaximalTorus fun T hT =>
    hT.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting

/-- **Unipotent special-fibre kernel from a common closed split torus.** Over a Henselian local
domain with algebraically closed residue field, let `ψ : M → N` be a model morphism with
identity generic fibre between models of a connected reductive group `G`, with `M` smooth. Let
`j' : 𝒮 → M` and `j : 𝒮 → N` be closed subgroups from a flat split torus over `R` with the same
generic fibre, a maximal split torus of `G`. If the kernel of the special-fibre map of `ψ` is
smooth and connected, it is unipotent. -/
theorem isUnipotent_kernel_specialFibreMap_of_splitTorus (hG : IsConnectedReductive G)
    {M N : IntegralModel R K G} [Smooth M.group.X.hom] (ψ : M.Hom N (𝟙 G))
    {𝒮 : CommGroupScheme (Spec (CommRingCat.of R))} [Flat 𝒮.toGrp.X.hom]
    (h𝒮 : IsSplitTorus 𝒮.toGrp)
    {j' : 𝒮.toGrp ⟶ M.group} (hj' : IsClosedSubgroup j')
    {j : 𝒮.toGrp ⟶ N.group} (hj : IsClosedSubgroup j)
    (hgen : M.genericTorusMap 𝒮 j' = N.genericTorusMap 𝒮 j)
    (hmax : IsMaximalSplitTorus (M.genericTorusMap 𝒮 j'))
    [Smooth (kernel ψ.specialFibreMap).X.hom]
    [ConnectedSpace (kernel ψ.specialFibreMap).X.left] :
    IsUnipotent (kernel ψ.specialFibreMap) := by
  have hcomp : (GroupScheme.baseChange (residueBaseMap R)).map j' ≫ ψ.specialFibreMap =
      (GroupScheme.baseChange (residueBaseMap R)).map j := by
    rw [Hom.specialFibreMap, ← Functor.map_comp, ψ.comp_eq_of_genericTorusMap_eq hgen]
  have hs := isMaximalTorus_specialFibre_of_generic hG M h𝒮 hj' hmax
  have hjk : IsClosedSubgroup ((GroupScheme.baseChange (residueBaseMap R)).map j) :=
    hj.baseChange _
  have : IsClosedImmersion
      ((GroupScheme.baseChange (residueBaseMap R)).map j).hom.hom.left := hjk
  have : Mono ((GroupScheme.baseChange (residueBaseMap R)).map j).hom.hom :=
    Over.mono_of_mono_left _
  have : Mono ((GroupScheme.baseChange (residueBaseMap R)).map j' ≫
      ψ.specialFibreMap).hom.hom := by
    rw [hcomp]
    infer_instance
  have : IsAffineHom (kernel ψ.specialFibreMap).X.hom := by
    rw [← Over.w (kernelι ψ.specialFibreMap).hom.hom]
    infer_instance
  exact isUnipotent_kernel_of_isMaximalTorus_of_smooth ψ.specialFibreMap hs
    (fun w hw => cocharacter_injective_of_mono ψ.specialFibreMap w hw)

variable [IsNoetherianRing R] [ValuationRing R]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Unipotent special-fibre kernel from bounded torus points.** Over a Henselian noetherian
valuation ring with algebraically closed residue field, let `ψ : M → N` be a model morphism
with identity generic fibre between models of a connected reductive group `G`, with `M`
smooth. Let `v` be a valuation of `K` that is one on the units of `R`, and `iT : T → G` a
maximal split torus whose character valuation kernel maps into the integral points of both
`M` and `N`. If the kernel of the special-fibre map of `ψ` is smooth and connected, it is
unipotent. -/
theorem isUnipotent_kernel_specialFibreMap_of_bounded (hG : IsConnectedReductive G)
    {M N : IntegralModel R K G} [Smooth M.group.X.hom] (ψ : M.Hom N (𝟙 G))
    (v : Valuation K Γ₀) (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} {iT : T.toGrp ⟶ G}
    (hiT : IsMaximalSplitTorus iT)
    (hbM : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      M.integralPoints)
    (hbN : (characterValuationKernel v T.toGrp).map (rationalPoints.map iT) ≤
      N.integralPoints)
    [Smooth (kernel ψ.specialFibreMap).X.hom]
    [ConnectedSpace (kernel ψ.specialFibreMap).X.left] :
    IsUnipotent (kernel ψ.specialFibreMap) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hiT.1.1
  let : Fintype I := Fintype.ofFinite I
  classical
  obtain ⟨j', hj', hgen'⟩ :=
    SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded
      M v hv e iT hiT.1.2 hbM
  obtain ⟨j, hj, hgen⟩ :=
    SplitTorusClosure.exists_isClosedSubgroup_torus_genericTorusMap_eq_of_bounded
      N v hv e iT hiT.1.2 hbN
  have : Flat (SplitTorusClosure.torus R I).toGrp.X.hom := SplitTorusClosure.flat_torus R I
  refine isUnipotent_kernel_specialFibreMap_of_splitTorus hG ψ
    (SplitTorusClosure.isSplitTorus_torus I) hj' hj (hgen'.trans hgen.symm) ?_
  rw [hgen', ← Category.assoc]
  exact isMaximalSplitTorus_iso_comp (SplitTorusClosure.genericSplitIso R K I ≪≫ e.symm) hiT

end Residue

end Langlands.GroupScheme.IntegralModel
