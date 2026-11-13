import Langlands.Representation.Plancherel.RationalSourceGammaChoice
import Langlands.Representation.Plancherel.RationalSourceGammaAmbientHaar
import Langlands.GroupScheme.Rational.StandardLeviAnnihilatorTransport
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # The constant `c(G|M)` of Waldspurger I.1 on actual rational points

Waldspurger 2003, I.1 (p.241): for `P = MU` semi-standard and `α ∈ Σ_red(P)`, `A_α` is the
neutral component of `ker α` in `A_M`, `M_α = Z_G(A_α)`, and
`c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)`.

Here `P = P_G(χ)` and `M = Z_G(χ)` for the cocharacter `χ = ζ ≫ i` of a cocharacter `ζ` of a
torus `i : T → G`. The submodule `X_*(A_α)` of cocharacters of `T` is described by roots
(`rankOneCocharacters`), `M_α` is the centralizer of all its cocharacters
(`cocharacterSubmoduleCentralizer`), and `γ(M_α|M)` is the common-compact open-cell constant of
`P ∩ M_α` and `Ū ∩ M_α` (`leviGamma`, `rankOneGamma`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

/-! ### The lower bound `1 ≤ γ` for common-compact source constants -/

section Generic

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [LocallyCompactSpace A] [SecondCountableTopology A]
  {P V : Subgroup A} (hP : IsClosed (P : Set A)) (hV : IsClosed (V : Set A))
  (K : OpenSubgroup A) (hK : IsCompact (K : Set A))

local instance genericSubgroupSecondCountable (H : Subgroup A) : SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set A)

omit [LocallyCompactSpace A] [SecondCountableTopology A] in
/-- Every common-compact open-cell constant is at least `1`: the points `v ∈ V ∩ K` contribute
`mes(P ∩ K) = 1` each, and `mes(V ∩ K) = 1`. -/
theorem one_le_compactNormalizedSourceGamma :
    1 ≤ compactNormalizedSourceGamma hP K hK V hV := by
  set μP := subgroupCompactOpenHaar K hK P hP
  set μV := subgroupCompactOpenHaar K hK V hV
  have hSP : MeasurableSet {p : P | (p : A) ∈ K} :=
    (K.isOpen.preimage continuous_subtype_val).measurableSet
  have hSV : MeasurableSet {v : V | (v : A) ∈ K} :=
    (K.isOpen.preimage continuous_subtype_val).measurableSet
  have hmP : μP {p : P | (p : A) ∈ K} = 1 := subgroupCompactOpenHaar_mass K hK P hP
  have hmV : μV {v : V | (v : A) ∈ K} = 1 := subgroupCompactOpenHaar_mass K hK V hV
  calc (1 : ℝ≥0∞) = ∫⁻ v, {v : V | (v : A) ∈ K}.indicator (fun _ => (1 : ℝ≥0∞)) v ∂μV := by
        rw [lintegral_indicator_const hSV, hmV, one_mul]
    _ ≤ ∫⁻ v, ∫⁻ p, ((K : Subgroup A) : Set A).indicator 1 ((p : A) * (v : A)⁻¹) ∂μP ∂μV := by
        refine lintegral_mono fun v => ?_
        by_cases hv : (v : A) ∈ K
        · rw [Set.indicator_of_mem (show v ∈ {v : V | (v : A) ∈ K} from hv)]
          calc (1 : ℝ≥0∞) = ∫⁻ p, {p : P | (p : A) ∈ K}.indicator 1 p ∂μP := by
                rw [lintegral_indicator_one hSP, hmP]
            _ ≤ _ := by
                refine lintegral_mono fun p => ?_
                by_cases hp : (p : A) ∈ K
                · have hpv : (p : A) * (v : A)⁻¹ ∈ ((K : Subgroup A) : Set A) :=
                    mul_mem hp (inv_mem hv)
                  rw [Set.indicator_of_mem (show p ∈ {p : P | (p : A) ∈ K} from hp),
                    Set.indicator_of_mem hpv]
                  exact le_rfl
                · rw [Set.indicator_of_notMem (show p ∉ {p : P | (p : A) ∈ K} from hp)]
                  exact bot_le
        · rw [Set.indicator_of_notMem (show v ∉ {v : V | (v : A) ∈ K} from hv)]
          exact bot_le
    _ = compactNormalizedSourceGamma hP K hK V hV := rfl

end Generic

/-! ### Annihilators, centralizers and the rank-one cocharacter submodules -/

section Algebraic

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The subgroup functor of points centralizing the image of every cocharacter in `N`: the
centralizer of the subtorus of `T` with cocharacter module `N`. -/
def cocharacterSubmoduleCentralizer (i : T.toGrp ⟶ G)
    (N : Submodule ℤ (cocharacterLattice T)) : SubgroupFunctor G where
  carrier U := ⨅ (ν : cocharacterLattice T) (_ : ν ∈ N),
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier U
  comp_mem a _ hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro ν hν
    exact (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).comp_mem a (hx ν hν)

theorem mem_cocharacterSubmoduleCentralizer (i : T.toGrp ⟶ G)
    (N : Submodule ℤ (cocharacterLattice T)) {U : Over (Spec (CommRingCat.of k))}
    {g : U ⟶ G.X} :
    g ∈ (cocharacterSubmoduleCentralizer i N).carrier U ↔
      ∀ ν ∈ N, g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier U := by
  simp only [cocharacterSubmoduleCentralizer, Subgroup.mem_iInf]

/-- On an annihilator, the submodule centralizer is the Library's annihilator centralizer. -/
theorem cocharacterSubmoduleCentralizer_cocharacterAnnihilator (i : T.toGrp ⟶ G)
    (J : Set (characterLattice T)) :
    cocharacterSubmoduleCentralizer i (cocharacterAnnihilator T J) =
      cocharacterAnnihilatorCentralizer i J := by
  ext U g
  rw [mem_cocharacterSubmoduleCentralizer, mem_cocharacterAnnihilatorCentralizer]
  simp only [mem_cocharacterAnnihilator]

/-- A positive multiple of a cocharacter, followed by `i`, is the corresponding power of the
cocharacter of `G`. -/
theorem groupHom_zsmul_comp (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T) (n : ℤ) :
    CommGroupScheme.groupHom (n • ζ) ≫ i =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) n) ≫
        (CommGroupScheme.groupHom ζ ≫ i) := by
  have hν : CommGroupScheme.groupHom (n • ζ) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) n) ≫
        CommGroupScheme.groupHom ζ := by
    change CommGroupScheme.groupHom (n • ζ) =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) n ≫ ζ)
    rw [Gm.powerHom_apply, Preadditive.zsmul_comp, Category.id_comp]
  rw [hν, Category.assoc]

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T)

/-- The relative roots vanishing on `ζ`: the roots of `T` in the Levi `M = Z_G(ζ)`. -/
def leviRelativeRoots : Set (characterLattice T) :=
  {α | α ∈ relativeRoots i ∧ latticePairing T α ζ = 0}

/-- For a relative root `β` positive on `ζ`, the cocharacters of `T` annihilated by `β` and by
the roots of `M`: for `T` a maximal split torus this is `X_*(A_α)` for the restriction `α` of
`β` to `A_M`. -/
def rankOneCocharacters (β : characterLattice T) : Submodule ℤ (cocharacterLattice T) :=
  cocharacterAnnihilator T (insert β (leviRelativeRoots i ζ))

/-- The index set of the product in `c(G|M)`: one submodule `X_*(A_α)` for each
`α ∈ Σ_red(P)`. -/
def rankOneCocharacterSet : Set (Submodule ℤ (cocharacterLattice T)) :=
  rankOneCocharacters i ζ '' positiveRelativeRoots i ζ

/-- The Levi `M_α` attached to `β` is the Library's annihilator centralizer of the roots of `M`
together with `β`. -/
theorem cocharacterSubmoduleCentralizer_rankOneCocharacters (β : characterLattice T) :
    cocharacterSubmoduleCentralizer i (rankOneCocharacters i ζ β) =
      cocharacterAnnihilatorCentralizer i (insert β (leviRelativeRoots i ζ)) :=
  cocharacterSubmoduleCentralizer_cocharacterAnnihilator i _

theorem finite_rankOneCocharacterSet (hfin : (relativeRoots i).Finite) :
    (rankOneCocharacterSet i ζ).Finite :=
  (hfin.subset (positiveRelativeRoots_subset_relativeRoots i ζ)).image _

/-- For a split torus `T` the relative roots are finite, so the index set of `c(G|M)` is finite. -/
theorem finite_rankOneCocharacterSet_of_isSplitTorus [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) : (rankOneCocharacterSet i ζ).Finite :=
  finite_rankOneCocharacterSet i ζ (hT.finite_relativeRoots i)

theorem leviRelativeRoots_zsmul {n : ℤ} (hn : 0 < n) :
    leviRelativeRoots i (n • ζ) = leviRelativeRoots i ζ := by
  ext α
  simp only [leviRelativeRoots, Set.mem_ofPred_eq, map_zsmul, smul_eq_mul, mul_eq_zero,
    hn.ne', false_or]

theorem positiveRelativeRoots_zsmul {n : ℤ} (hn : 0 < n) :
    positiveRelativeRoots i (n • ζ) = positiveRelativeRoots i ζ := by
  ext α
  simp only [positiveRelativeRoots, Set.mem_ofPred_eq, map_zsmul, smul_eq_mul,
    mul_pos_iff_of_pos_left hn]

/-- The index set depends on `ζ` only up to positive multiples. -/
theorem rankOneCocharacterSet_zsmul {n : ℤ} (hn : 0 < n) :
    rankOneCocharacterSet i (n • ζ) = rankOneCocharacterSet i ζ := by
  unfold rankOneCocharacterSet rankOneCocharacters
  rw [leviRelativeRoots_zsmul i ζ hn, positiveRelativeRoots_zsmul i ζ hn]

end Algebraic

/-! ### Actual rational points -/

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance plancherelConstantPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance plancherelConstantPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance plancherelConstantPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance plancherelConstantFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance plancherelConstantPointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
local instance plancherelConstantPointLocallyCompact :
    LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G
local instance plancherelConstantFieldSecondCountable : SecondCountableTopology F :=
  localField_secondCountableTopology F
local instance plancherelConstantPointSecondCountable :
    SecondCountableTopology (RationalPoint F G.X) := rationalPoint_secondCountableTopology F G
local instance plancherelConstantSubgroupSecondCountable (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

section Levi

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (L : Subgroup (RationalPoint F G.X)) (hL : IsClosed (L : Set (RationalPoint F G.X)))

local notation "Pχ" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "Vχ" => unipotentPoints (oppositeCocharacter χ)

omit [LocallyOfFiniteType G.X.hom] in
include hL in
theorem isClosed_parabolic_inf : IsClosed ((Pχ ⊓ L : Subgroup (RationalPoint F G.X)) :
    Set (RationalPoint F G.X)) := by
  rw [Subgroup.coe_inf]
  exact (isClosed_dynamic_parabolic F G χ).inter hL

omit [LocallyOfFiniteType G.X.hom] in
include hL in
theorem isClosed_oppositeRadical_inf : IsClosed ((Vχ ⊓ L : Subgroup (RationalPoint F G.X)) :
    Set (RationalPoint F G.X)) := by
  rw [Subgroup.coe_inf]
  exact (isClosed_unipotentPoints (oppositeCocharacter χ)).inter hL

/-- The source constant `γ^L(P_G(χ) ∩ L)` of the closed subgroup `L` of `G(F)`: the open-cell
constant of `P_G(χ)(F) ∩ L` and `U_G(χ⁻¹)(F) ∩ L`, with the Haar measures giving mass one to
their intersections with `K`. For a Levi subgroup `L ⊇ M = Z_G(χ)` this is `γ(L|M)`. -/
def leviGamma : ℝ≥0∞ :=
  compactNormalizedSourceGamma (isClosed_parabolic_inf χ L hL) K hK (Vχ ⊓ L)
    (isClosed_oppositeRadical_inf χ L hL)

/-- If `L` contains the parabolic and the opposite radical, `γ^L` is the Library's `γ(P)` of
`G` itself. -/
theorem leviGamma_eq_gamma_of_le (hPL : Pχ ≤ L) (hVL : Vχ ≤ L) :
    leviGamma χ K hK L hL = gamma χ K hK :=
  compactNormalizedSourceGamma_eq_of_transport (ContinuousMulEquiv.refl _) K K hK hK
    (isClosed_dynamic_parabolic F G χ) (isClosed_unipotentPoints (oppositeCocharacter χ))
    (isClosed_parabolic_inf χ L hL) (isClosed_oppositeRadical_inf χ L hL)
    (fun x => by
      change x ∈ Pχ ⊓ L ↔ x ∈ Pχ
      exact ⟨fun h => (Subgroup.mem_inf.mp h).1, fun h => Subgroup.mem_inf.mpr ⟨h, hPL h⟩⟩)
    (fun x => by
      change x ∈ Vχ ⊓ L ↔ x ∈ Vχ
      exact ⟨fun h => (Subgroup.mem_inf.mp h).1, fun h => Subgroup.mem_inf.mpr ⟨h, hVL h⟩⟩)
    (fun _ => Iff.rfl)

theorem leviGamma_top : leviGamma χ K hK ⊤ isClosed_univ = gamma χ K hK :=
  leviGamma_eq_gamma_of_le χ K hK ⊤ isClosed_univ le_top le_top

theorem one_le_leviGamma : 1 ≤ leviGamma χ K hK L hL :=
  one_le_compactNormalizedSourceGamma _ _ K hK

theorem one_le_gamma : 1 ≤ gamma χ K hK := by
  rw [← leviGamma_top χ K hK]
  exact one_le_leviGamma χ K hK ⊤ isClosed_univ

/-- `γ^L` does not change when `χ` is replaced by a positive power. -/
theorem leviGamma_precomp_power {n : ℤ} (hn : 0 < n) :
    leviGamma (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ χ)
        K hK L hL = leviGamma χ K hK L hL :=
  compactNormalizedSourceGamma_eq_of_transport (ContinuousMulEquiv.refl _) K K hK hK
    (isClosed_parabolic_inf χ L hL) (isClosed_oppositeRadical_inf χ L hL)
    (isClosed_parabolic_inf _ L hL) (isClosed_oppositeRadical_inf _ L hL)
    (fun x => by
      change x ∈ SubgroupFunctor.carrier (Dynamic.parabolic
          (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ χ)) X₀ ⊓ L ↔
        x ∈ Pχ ⊓ L
      rw [Dynamic.parabolic_precomp_power χ hn])
    (fun x => by
      change x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter
          (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) n) ≫ χ))) X₀ ⊓ L ↔
        x ∈ SubgroupFunctor.carrier (Dynamic.unipotent (oppositeCocharacter χ)) X₀ ⊓ L
      rw [oppositeCocharacter_precomp_power,
        Dynamic.unipotent_precomp_power (oppositeCocharacter χ) hn])
    (fun _ => Iff.rfl)

end Levi

section RankOne

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))

omit [LocallyOfFiniteType G.X.hom] in
/-- The rational points of a submodule centralizer form a closed subgroup. -/
theorem isClosed_cocharacterSubmoduleCentralizer (N : Submodule ℤ (cocharacterLattice T)) :
    IsClosed (((cocharacterSubmoduleCentralizer i N).carrier X₀ :
      Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) := by
  have h : (((cocharacterSubmoduleCentralizer i N).carrier X₀ :
      Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) =
        ⋂ (ν : cocharacterLattice T) (_ : ν ∈ N),
          ((Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier X₀ :
            Set (RationalPoint F G.X)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, mem_cocharacterSubmoduleCentralizer]
  rw [h]
  exact isClosed_iInter fun ν => isClosed_iInter fun _ => isClosed_levi _

/-- Waldspurger's `γ(M_α|M)`, for `N = X_*(A_α)`: the source constant of
`P ∩ M_α` and `Ū ∩ M_α` in `M_α = Z_G(A_α)`, for `P = P_G(ζ)`. -/
def rankOneGamma (N : Submodule ℤ (cocharacterLattice T)) : ℝ≥0∞ :=
  leviGamma (CommGroupScheme.groupHom ζ ≫ i) K hK
    ((cocharacterSubmoduleCentralizer i N).carrier X₀)
    (isClosed_cocharacterSubmoduleCentralizer i N)

/-- The product `∏_{α ∈ Σ_red(P)} γ(M_α|M)`, indexed by the submodules `X_*(A_α)`. -/
def rankOneGammaProduct : ℝ≥0∞ :=
  ∏ᶠ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N

/-- **Waldspurger's constant** `c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)` (I.1, p.241), for
`P = P_G(ζ)`, `M = Z_G(ζ)` and the common compact open `K`. -/
def plancherelConstant : ℝ≥0∞ :=
  (gamma (CommGroupScheme.groupHom ζ ≫ i) K hK)⁻¹ * rankOneGammaProduct i ζ K hK

/-- The real value of `c(G|M)`. -/
def plancherelConstantReal : ℝ :=
  (plancherelConstant i ζ K hK).toReal

theorem one_le_rankOneGamma (N : Submodule ℤ (cocharacterLattice T)) :
    1 ≤ rankOneGamma i ζ K hK N :=
  one_le_leviGamma _ K hK _ _

theorem one_le_rankOneGammaProduct : 1 ≤ rankOneGammaProduct i ζ K hK :=
  finprod_mem_induction (fun x : ℝ≥0∞ => 1 ≤ x) le_rfl
    (fun x y hx hy => by
      calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
        _ ≤ x * y := mul_le_mul' hx hy)
    (fun N _ => one_le_rankOneGamma i ζ K hK N)

theorem rankOneGammaProduct_ne_top
    (h : ∀ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N ≠ ⊤) :
    rankOneGammaProduct i ζ K hK ≠ ⊤ :=
  finprod_mem_induction (fun x : ℝ≥0∞ => x ≠ ⊤) ENNReal.one_ne_top
    (fun _ _ hx hy => ENNReal.mul_ne_top hx hy) h

/-- With finitely many relative roots, the product is a finite product. -/
theorem rankOneGammaProduct_eq_prod (hfin : (relativeRoots i).Finite) :
    rankOneGammaProduct i ζ K hK =
      ∏ N ∈ (finite_rankOneCocharacterSet i ζ hfin).toFinset, rankOneGamma i ζ K hK N :=
  finprod_mem_eq_finite_toFinset_prod _ _

/-- For a split torus `T`, the product in `c(G|M)` is a finite product over its index set. -/
theorem rankOneGammaProduct_eq_prod_of_isSplitTorus (hT : IsSplitTorus T.toGrp) :
    rankOneGammaProduct i ζ K hK =
      ∏ N ∈ (finite_rankOneCocharacterSet_of_isSplitTorus i ζ hT).toFinset,
        rankOneGamma i ζ K hK N :=
  finprod_mem_eq_finite_toFinset_prod _ _

theorem plancherelConstant_ne_zero (h : gamma (CommGroupScheme.groupHom ζ ≫ i) K hK ≠ ⊤) :
    plancherelConstant i ζ K hK ≠ 0 :=
  mul_ne_zero (ENNReal.inv_ne_zero.mpr h)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_rankOneGammaProduct i ζ K hK)))

theorem plancherelConstant_ne_top
    (h : ∀ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N ≠ ⊤) :
    plancherelConstant i ζ K hK ≠ ⊤ :=
  ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_gamma _ K hK))))
    (rankOneGammaProduct_ne_top i ζ K hK h)

/-- `c(G|M) ≤ ∏ γ(M_α|M)`, since `γ(G|M) ≥ 1`. -/
theorem plancherelConstant_le_rankOneGammaProduct :
    plancherelConstant i ζ K hK ≤ rankOneGammaProduct i ζ K hK := by
  unfold plancherelConstant
  calc (gamma (CommGroupScheme.groupHom ζ ≫ i) K hK)⁻¹ * rankOneGammaProduct i ζ K hK
      ≤ 1 * rankOneGammaProduct i ζ K hK := by
        gcongr
        exact ENNReal.inv_le_one.mpr (one_le_gamma _ K hK)
    _ = rankOneGammaProduct i ζ K hK := one_mul _

section Smooth

variable [Smooth G.X.hom]

theorem plancherelConstant_ne_zero_of_smooth : plancherelConstant i ζ K hK ≠ 0 :=
  plancherelConstant_ne_zero i ζ K hK (gamma_ne_zero_ne_top_of_smooth K hK _).2

theorem plancherelConstantReal_pos_of_smooth
    (h : ∀ N ∈ rankOneCocharacterSet i ζ, rankOneGamma i ζ K hK N ≠ ⊤) :
    0 < plancherelConstantReal i ζ K hK :=
  ENNReal.toReal_pos (plancherelConstant_ne_zero_of_smooth i ζ K hK)
    (plancherelConstant_ne_top i ζ K hK h)

end Smooth

/-! #### Independence of positive multiples of `ζ` -/

theorem rankOneGamma_zsmul {n : ℤ} (hn : 0 < n) (N : Submodule ℤ (cocharacterLattice T)) :
    rankOneGamma i (n • ζ) K hK N = rankOneGamma i ζ K hK N := by
  unfold rankOneGamma
  rw [groupHom_zsmul_comp]
  exact leviGamma_precomp_power _ K hK _ _ hn

theorem rankOneGammaProduct_zsmul {n : ℤ} (hn : 0 < n) :
    rankOneGammaProduct i (n • ζ) K hK = rankOneGammaProduct i ζ K hK := by
  unfold rankOneGammaProduct
  rw [rankOneCocharacterSet_zsmul i ζ hn]
  simp only [rankOneGamma_zsmul i ζ K hK hn]

/-- `c(G|M)` is unchanged when `ζ` is replaced by a positive multiple. -/
theorem plancherelConstant_zsmul {n : ℤ} (hn : 0 < n) :
    plancherelConstant i (n • ζ) K hK = plancherelConstant i ζ K hK := by
  unfold plancherelConstant
  rw [rankOneGammaProduct_zsmul i ζ K hK hn, groupHom_zsmul_comp,
    gamma_precomp_power _ K hK hn]

end RankOne

end Local

end Langlands.Plancherel.RationalDynamicSource
