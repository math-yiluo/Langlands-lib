import Langlands.Global.AdelicPositiveImageClosed
import Langlands.Global.AdelicSiegelFiniteVolume
import Langlands.Global.AdelicDerivedNormOne
import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.TriangularRationalQuotientCompact
import Langlands.Analysis.Local.SiegelSetMeasure
import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs

/-! # Finite Haar measure of adelic Siegel sets from the modulus formula -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology Opposite
open scoped CategoryTheory.MonObj ENNReal NNReal Pointwise

namespace Langlands.Aubert.General.IsSemidirectDecomposition

variable {G : Type*} [Group G]

/-- A homomorphism on `Q` that takes values in `M`, is the identity on `M` and has kernel `U`
exhibits `Q = M ⋉ U`. -/
theorem of_retraction {Q M U : Subgroup G} (hMQ : M ≤ Q) (hUQ : U ≤ Q) (f : Q →* G)
    (hfM : ∀ q, f q ∈ M) (hfid : ∀ m (hm : m ∈ M), f ⟨m, hMQ hm⟩ = m)
    (hfker : ∀ q, f q = 1 ↔ (q : G) ∈ U) : IsSemidirectDecomposition Q M U := by
  have hconj : ∀ q : Q, ∀ u (hu : u ∈ U), ((q * ⟨u, hUQ hu⟩ * q⁻¹ : Q) : G) ∈ U := by
    intro q u hu
    apply (hfker _).mp
    rw [map_mul, map_mul, map_inv, (hfker ⟨u, hUQ hu⟩).mpr hu, mul_one, mul_inv_cancel]
  refine ⟨hMQ, hUQ, fun q hq => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      simpa using hconj ⟨q, hq⟩ n hn
    · intro hn
      have h := hconj (⟨q, hq⟩ : Q)⁻¹ _ hn
      simpa [mul_assoc] using h
  · refine Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr fun q => ?_
    have hmem : (⟨f q, hMQ (hfM q)⟩ : Q) ∈ M.subgroupOf Q := hfM q
    refine ⟨⟨⟨f q, hMQ (hfM q)⟩, hmem⟩, ?_, ?_⟩
    · change ((⟨f q, hMQ (hfM q)⟩ : Q)⁻¹ * q : Q) ∈ U.subgroupOf Q
      rw [Subgroup.mem_subgroupOf]
      apply (hfker _).mp
      rw [map_mul, map_inv, hfid (f q) (hfM q), inv_mul_cancel]
    · rintro ⟨s, hs⟩ hsq
      change ((s : Q)⁻¹ * q : Q) ∈ U.subgroupOf Q at hsq
      rw [Subgroup.mem_subgroupOf] at hsq
      have h1 := (hfker _).mpr hsq
      have hs' : ((s : Q) : G) ∈ M := hs
      have hsid : f s = (s : G) := hfid (s : G) hs'
      rw [map_mul, map_inv, hsid, inv_mul_eq_one] at h1
      apply Subtype.ext
      apply Subtype.ext
      exact h1

/-- The Levi projection of `of_retraction` is the given homomorphism. -/
theorem of_retraction_projection {Q M U : Subgroup G} (hMQ : M ≤ Q) (hUQ : U ≤ Q) (f : Q →* G)
    (hfM : ∀ q, f q ∈ M) (hfid : ∀ m (hm : m ∈ M), f ⟨m, hMQ hm⟩ = m)
    (hfker : ∀ q, f q = 1 ↔ (q : G) ∈ U) (q : Q) :
    ((of_retraction hMQ hUQ f hfM hfid hfker).projection q : G) = f q := by
  have h := ((of_retraction hMQ hUQ f hfM hfid hfker).projection_eq_iff q ⟨f q, hfM q⟩).mpr (by
    apply (hfker ((⟨f q, hMQ (hfM q)⟩ : Q)⁻¹ * q)).mp
    rw [map_mul, map_inv, hfid (f q) (hfM q), inv_mul_cancel])
  rw [h]

/-- The Levi projection of `of_retraction` is continuous when the homomorphism is. -/
theorem continuous_of_retraction_projection [TopologicalSpace G] {Q M U : Subgroup G}
    (hMQ : M ≤ Q) (hUQ : U ≤ Q) (f : Q →* G)
    (hfM : ∀ q, f q ∈ M) (hfid : ∀ m (hm : m ∈ M), f ⟨m, hMQ hm⟩ = m)
    (hfker : ∀ q, f q = 1 ↔ (q : G) ∈ U) (hf : Continuous f) :
    Continuous (of_retraction hMQ hUQ f hfM hfid hfker).projection := by
  have h : ((of_retraction hMQ hUQ f hfM hfid hfker).projection : Q → M) =
      fun q => ⟨f q, hfM q⟩ := by
    funext q
    exact Subtype.ext (of_retraction_projection hMQ hUQ f hfM hfid hfker q)
  rw [h]
  exact hf.subtype_mk _

end Langlands.Aubert.General.IsSemidirectDecomposition

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology NumberField IsDedekindDomain
open scoped RestrictedProduct

variable (F : Type u) [Field F] [NumberField F]

/-- A closed subgroup of an affine group scheme has closed adelic image, and the adelic
topology of the subgroup is the subspace topology. -/
theorem isClosedEmbedding_map_of_isClosedSubgroup {H G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] [IsAffine G.X.left] (f : H ⟶ G) (hf : IsClosedSubgroup f) :
    IsClosedEmbedding (map F H G f) := by
  letI : IsClosedImmersion f.hom.hom.left := hf
  exact isClosedEmbedding_map F H G f

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

section Images

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The adelic points `P(𝔸_F)` of the standard minimal parabolic, inside `G(𝔸_F)`. -/
def standardParabolicImage : Subgroup (AdelicGroupPoints F G) :=
  (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)).toMonoidHom.range

/-- The adelic points `M(𝔸_F)` of the standard Levi, inside `G(𝔸_F)`. -/
def standardLeviImage : Subgroup (AdelicGroupPoints F G) :=
  (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).toMonoidHom.range

/-- The adelic points `N(𝔸_F)` of the standard unipotent subgroup, inside `G(𝔸_F)`. -/
def standardUnipotentImage : Subgroup (AdelicGroupPoints F G) :=
  (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)).toMonoidHom.range

theorem standardLeviImage_eq :
    standardLeviImage F G T i ν =
      (standardLevi i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) :=
  congrArg (fun H : SubgroupFunctor G =>
    H.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))))
    (Standard.isRepresentedBy_leviHom i ν ∅).2

theorem standardUnipotentImage_eq :
    standardUnipotentImage F G T i ν =
      (standardUnipotent i ν ∅).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) :=
  congrArg (fun H : SubgroupFunctor G =>
    H.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))))
    (Standard.isRepresentedBy_unipotentHom i ν ∅).2

theorem standardLeviImage_le_parabolic :
    standardLeviImage F G T i ν ≤ standardParabolicImage F G T i ν := by
  rw [standardLeviImage_eq, standardParabolicImage, standardParabolic_adelic_range]
  exact standardLevi_le_standardParabolic i ν ∅ _

theorem standardUnipotentImage_le_parabolic :
    standardUnipotentImage F G T i ν ≤ standardParabolicImage F G T i ν := by
  rw [standardUnipotentImage_eq, standardParabolicImage, standardParabolic_adelic_range]
  exact standardUnipotent_le_standardParabolic i ν ∅ _

/-- `P(𝔸_F)` normalizes `N(𝔸_F)`. -/
theorem standardParabolicImage_le_normalizer :
    standardParabolicImage F G T i ν ≤
      Subgroup.normalizer (standardUnipotentImage F G T i ν : Set (AdelicGroupPoints F G)) := by
  have key : ∀ g ∈ standardParabolicImage F G T i ν, ∀ u ∈ standardUnipotentImage F G T i ν,
      g * u * g⁻¹ ∈ standardUnipotentImage F G T i ν := by
    intro g hg u hu
    rw [standardParabolicImage, standardParabolic_adelic_range] at hg
    rw [standardUnipotentImage_eq] at hu ⊢
    rw [mem_standardUnipotent] at hu ⊢
    intro ζ hζ
    exact Dynamic.conj_mem_unipotent _ ((mem_standardParabolic i ν).1 hg ζ hζ) (hu ζ hζ)
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact key p hp n
  · intro hn
    have h := key p⁻¹ (inv_mem hp) _ hn
    simpa [mul_assoc] using h

variable (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

theorem positiveMap_mem_standardLeviImage (x : PositiveRealTorus.intrinsicSubgroup F T₀) :
    positiveMap F G T i T₀ j x ∈ standardLeviImage F G T i ν := by
  rw [standardLeviImage_eq]
  exact positiveMap_mem_standardLevi F G T i ν T₀ j x

/-- The positive torus normalizes `N(𝔸_F)`. -/
theorem positiveMap_mem_normalizer (x : PositiveRealTorus.intrinsicSubgroup F T₀) :
    positiveMap F G T i T₀ j x ∈
      Subgroup.normalizer (standardUnipotentImage F G T i ν : Set (AdelicGroupPoints F G)) :=
  standardParabolicImage_le_normalizer F G T i ν
    (standardLeviImage_le_parabolic F G T i ν (positiveMap_mem_standardLeviImage F G T i ν T₀ j x))

omit [NumberField F] in
theorem isAffine_of_isClosedSubgroup {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsClosedSubgroup f) : IsAffine H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion f.hom.hom.left := hf
  exact isAffine_of_isAffineHom f.hom.hom.left

/-- The adelic image of a closed subgroup is closed. -/
theorem isClosed_range_map {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (hf : IsClosedSubgroup f) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsClosed ((map F H G f).toMonoidHom.range : Set (AdelicGroupPoints F G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isClosedSubgroup F G f hf
  rw [MonoidHom.coe_range]
  exact (isClosedEmbedding_map_of_isClosedSubgroup F f hf).isClosed_range

/-- `P(𝔸_F)` is closed in `G(𝔸_F)`. -/
theorem isClosed_standardParabolicImage :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsClosed (standardParabolicImage F G T i ν : Set (AdelicGroupPoints F G)) :=
  isClosed_range_map F G _ (Standard.isClosedSubgroup_parabolicHom i ν ∅)

/-- `M(𝔸_F)` is closed in `G(𝔸_F)`. -/
theorem isClosed_standardLeviImage :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsClosed (standardLeviImage F G T i ν : Set (AdelicGroupPoints F G)) :=
  isClosed_range_map F G _ (Standard.isClosedSubgroup_leviHom i ν ∅)

/-- `N(𝔸_F)` is closed in `G(𝔸_F)`. -/
theorem isClosed_standardUnipotentImage :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsClosed (standardUnipotentImage F G T i ν : Set (AdelicGroupPoints F G)) :=
  isClosed_range_map F G _ (Standard.isClosedSubgroup_unipotentHom i ν ∅)

end Images

/-- **Modulus of the positive torus on the unipotent radical.** For every number field `F`,
connected reductive `G` and actual algebraic Siegel setup, the Haar modulus of conjugation by
a point `a` of the positive torus `A_{T₀}` on the closed subgroup `N(𝔸_F)` of `G(𝔸_F)` is
`∏_{β > 0} |β(a)|^{m_β}`, the product over the positive relative roots of the normalized adelic
norms, with `m_β` the dimension of the `β`-weight space of `T` in the Lie algebra of `G`. -/
def PositiveTorusUnipotentModulusStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
          ∀ x : PositiveRealTorus.intrinsicSubgroup F T₀,
            ((HaarModulus.closedNormalizerCharacter (standardUnipotentImage F G T i ν)
                (isClosed_standardUnipotentImage F G T i ν)
                ⟨positiveMap F G T i T₀ j x,
                  positiveMap_mem_normalizer F G T i ν T₀ j x⟩ : ℝ≥0ˣ) : ℝ≥0) =
              ∏ᶠ (β : characterLattice T) (_ : β ∈ positiveRelativeRoots i ν),
                (PositiveRealTorus.normCharacter F T₀ (j ≫ β) x : ℝ≥0) ^
                  Module.finrank F (weightSpace i β)

/-- **Compact simple-root boxes.** For every number field `F`, connected reductive `G` and
actual algebraic Siegel setup, every box `s⁻¹ ≤ |α(a)| ≤ s` (`α` simple) in the positive
torus `A_{T₀}` is compact. -/
def SimpleRootBoxCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          ∀ s : ℝ≥0, IsCompact {x : PositiveRealTorus.intrinsicSubgroup F T₀ |
            ∀ α ∈ simpleRelativeRoots i ν,
              s⁻¹ ≤ (PositiveRealTorus.normCharacter F T₀ (j ≫ α) x : ℝ≥0) ∧
                (PositiveRealTorus.normCharacter F T₀ (j ≫ α) x : ℝ≥0) ≤ s}

section Levi

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

omit [NumberField F] in
/-- Under an actual algebraic Siegel setup the standard parabolic retracts onto the standard
Levi, with kernel the standard unipotent subgroup on every test scheme. -/
theorem exists_standardLeviRetraction (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ q : Standard.parabolicScheme i ν ∅ ⟶ Standard.leviScheme i ν ∅,
      Standard.leviToParabolic i ν ∅ ≫ q = 𝟙 _ ∧
        ∀ (V : Over (Spec (CommRingCat.of F))) (x : V ⟶ (Standard.parabolicScheme i ν ∅).X),
          x ≫ q.hom.hom = 1 ↔
            x ∈ (SubgroupFunctor.range (Standard.unipotentToParabolic i ν ∅)).carrier V := by
  obtain ⟨-, -, -, hL, hN, -⟩ := hsetup
  obtain ⟨U, r, q, hr, -, hlq, hker⟩ := hL.exists_unipotentRadical_retraction
  have hrange : SubgroupFunctor.range r =
      SubgroupFunctor.range (Standard.unipotentToParabolic i ν ∅) :=
    le_antisymm
      (hN.1.greatest _ r hr.1.isClosedSubgroup hr.1.smooth hr.1.connectedSpace
        hr.1.isUnipotent hr.1.isNormal)
      (hr.1.greatest _ _ hN.1.isClosedSubgroup hN.1.smooth hN.1.connectedSpace
        hN.1.isUnipotent hN.1.isNormal)
  refine ⟨q, hlq, fun V x => ?_⟩
  rw [hker V x, hrange]

/-- The adelic Levi projection `P(𝔸_F) → M(𝔸_F) ⊆ G(𝔸_F)`: a continuous homomorphism with
values in `M(𝔸_F)`, the identity on `M(𝔸_F)` and with kernel `N(𝔸_F)`. -/
theorem exists_standardLeviPart (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ f : standardParabolicImage F G T i ν →* AdelicGroupPoints F G,
      (haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom; Continuous f) ∧
      (∀ p, f p ∈ standardLeviImage F G T i ν) ∧
      (∀ m (hm : m ∈ standardLeviImage F G T i ν),
        f ⟨m, standardLeviImage_le_parabolic F G T i ν hm⟩ = m) ∧
      (∀ p, f p = 1 ↔ (p : AdelicGroupPoints F G) ∈ standardUnipotentImage F G T i ν) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨q, hlq, hker⟩ := exists_standardLeviRetraction F G T i ν T₀ j hsetup
  have : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
    isAffine_of_isClosedSubgroup F G _ (Standard.isClosedSubgroup_parabolicHom i ν ∅)
  have hincl := isClosedEmbedding_map_of_isClosedSubgroup F (Standard.parabolicHom i ν ∅)
    (Standard.isClosedSubgroup_parabolicHom i ν ∅)
  set incl := map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)
  let e : AdelicGroupPoints F (Standard.parabolicScheme i ν ∅) ≃* standardParabolicImage F G T i ν :=
    MonoidHom.ofInjective (f := incl.toMonoidHom) hincl.injective
  have hincle : ∀ p, incl (e.symm p) = (p : AdelicGroupPoints F G) := fun p => by
    have h : ((e (e.symm p) : standardParabolicImage F G T i ν) : AdelicGroupPoints F G) =
        incl (e.symm p) :=
      MonoidHom.ofInjective_apply (f := incl.toMonoidHom) hincl.injective (x := e.symm p)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  let r := map F (Standard.parabolicScheme i ν ∅) (Standard.parabolicScheme i ν ∅)
    (q ≫ Standard.leviToParabolic i ν ∅)
  refine ⟨incl.toMonoidHom.comp (r.toMonoidHom.comp e.symm.toMonoidHom), ?_, ?_, ?_, ?_⟩
  · have he : Continuous (fun p : standardParabolicImage F G T i ν => e.symm p) := by
      rw [hincl.isInducing.continuous_iff]
      have : (incl ∘ fun p : standardParabolicImage F G T i ν => e.symm p) = Subtype.val :=
        funext hincle
      rw [this]
      exact continuous_subtype_val
    exact incl.continuous.comp (r.continuous.comp he)
  · intro p
    refine ⟨e.symm p ≫ q.hom.hom, ?_⟩
    change (e.symm p ≫ q.hom.hom) ≫ (Standard.leviHom i ν ∅).hom.hom =
      (e.symm p ≫ (q ≫ Standard.leviToParabolic i ν ∅).hom.hom) ≫ (Standard.parabolicHom i ν ∅).hom.hom
    rw [← Standard.leviToParabolic_comp i ν ∅]
    simp only [Grp.comp_hom_hom, Category.assoc]
  · intro m hm
    obtain ⟨y, hy⟩ := hm
    have hlq' : (Standard.leviToParabolic i ν ∅).hom.hom ≫ q.hom.hom = 𝟙 _ := by
      have := congrArg
        (fun f : Standard.leviScheme i ν ∅ ⟶ Standard.leviScheme i ν ∅ => f.hom.hom) hlq
      simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using this
    have hy' : y ≫ (Standard.leviHom i ν ∅).hom.hom = m := hy
    have hx : e.symm ⟨m, standardLeviImage_le_parabolic F G T i ν ⟨y, hy⟩⟩ =
        y ≫ (Standard.leviToParabolic i ν ∅).hom.hom := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change m = (y ≫ (Standard.leviToParabolic i ν ∅).hom.hom) ≫
        (Standard.parabolicHom i ν ∅).hom.hom
      rw [← hy', ← Standard.leviToParabolic_comp i ν ∅]
      simp only [Grp.comp_hom_hom, Category.assoc]
    change incl (r (e.symm _)) = m
    rw [hx]
    change ((y ≫ (Standard.leviToParabolic i ν ∅).hom.hom) ≫
      (q ≫ Standard.leviToParabolic i ν ∅).hom.hom) ≫ (Standard.parabolicHom i ν ∅).hom.hom = m
    rw [← hy', ← Standard.leviToParabolic_comp i ν ∅]
    simp only [Grp.comp_hom_hom, Category.assoc]
    rw [← Category.assoc (Standard.leviToParabolic i ν ∅).hom.hom, hlq', Category.id_comp]
  · intro p
    set x := e.symm p
    have hp : (p : AdelicGroupPoints F G) = incl x := (hincle p).symm
    have hlinj : ∀ y : AdelicGroupPoints F (Standard.leviScheme i ν ∅), y ≫ (Standard.leviToParabolic i ν ∅).hom.hom = 1 → y = 1 := by
      intro y hy
      have hlq' : (Standard.leviToParabolic i ν ∅).hom.hom ≫ q.hom.hom = 𝟙 _ := by
        have := congrArg (fun f : Standard.leviScheme i ν ∅ ⟶ Standard.leviScheme i ν ∅ => f.hom.hom) hlq
        simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using this
      have h := congrArg (fun z => z ≫ q.hom.hom) hy
      simp only [Category.assoc, hlq', Category.comp_id, MonObj.one_comp] at h
      exact h
    change incl (r x) = 1 ↔ _
    constructor
    · intro h
      have h1 : r x = 1 := hincl.injective (by rw [h, map_one])
      have h2 : x ≫ q.hom.hom = 1 := by
        apply hlinj
        change (x ≫ (q ≫ Standard.leviToParabolic i ν ∅).hom.hom) = 1 at h1
        simpa only [Grp.comp_hom_hom, Category.assoc] using h1
      obtain ⟨n, hn⟩ := (hker _ x).mp h2
      have hn' : n ≫ (Standard.unipotentToParabolic i ν ∅).hom.hom = x := hn
      refine ⟨n, ?_⟩
      rw [hp]
      change n ≫ (Standard.unipotentHom i ν ∅).hom.hom = x ≫ (Standard.parabolicHom i ν ∅).hom.hom
      rw [← hn', ← Standard.unipotentToParabolic_comp i ν ∅]
      simp only [Grp.comp_hom_hom]
      exact (Category.assoc _ _ _).symm
    · rintro ⟨n, hn⟩
      have hx : x = n ≫ (Standard.unipotentToParabolic i ν ∅).hom.hom := by
        apply hincl.injective
        rw [← hp]
        change _ = (n ≫ (Standard.unipotentToParabolic i ν ∅).hom.hom) ≫
          (Standard.parabolicHom i ν ∅).hom.hom
        rw [← hn]
        change n ≫ (Standard.unipotentHom i ν ∅).hom.hom = _
        rw [← Standard.unipotentToParabolic_comp i ν ∅]
        simp only [Grp.comp_hom_hom, Category.assoc]
      have h2 : x ≫ q.hom.hom = 1 := (hker _ x).mpr ⟨n, hx.symm⟩
      have h1 : r x = 1 := by
        change x ≫ (q ≫ Standard.leviToParabolic i ν ∅).hom.hom = 1
        simp only [Grp.comp_hom_hom, ← Category.assoc, h2, MonObj.one_comp]
      rw [h1, map_one]

/-- Without any further input, `N(𝔸_F)` lies in `G(𝔸_F)¹` as soon as unipotent rational
quotients are compact. -/
theorem standardUnipotentImage_le_normOne [LocallyOfFiniteType G.X.hom]
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hU : UnipotentRationalQuotientCompactStatement.{u}) :
    standardUnipotentImage F G T i ν ≤ normOneSubgroup F G := by
  obtain ⟨-, -, -, -, hN, -⟩ := hsetup
  have hN := hN.1
  set N := Standard.unipotentScheme i ν ∅
  have : IsAffine N.X.left :=
    isAffine_of_isClosedSubgroup F G _ (Standard.isClosedSubgroup_unipotentHom i ν ∅)
  have : LocallyOfFiniteType N.X.hom := by
    have : IsClosedImmersion (Standard.unipotentHom i ν ∅).hom.hom.left :=
      Standard.isClosedSubgroup_unipotentHom i ν ∅
    rw [← Over.w (Standard.unipotentHom i ν ∅).hom.hom]
    infer_instance
  have : CompactSpace (RationalQuotient F N) :=
    hU F N hN.smooth hN.connectedSpace hN.isUnipotent
  rintro _ ⟨n, rfl⟩
  exact map_normOneSubgroup_le F N G (Standard.unipotentHom i ν ∅)
    ⟨n, mem_normOneSubgroup_of_compactSpace F N n, rfl⟩

end Levi

section Exponents

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ T)

theorem characterValue_add' {R : CommRingCat.{u}} {S : CommGroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A] (χ ψ : characterLattice S)
    (s : Lie.AffinePoints S.toGrp A) :
    Lie.characterValue (χ + ψ) s = Lie.characterValue χ s * Lie.characterValue ψ s := by
  unfold Lie.characterValue
  rw [← map_mul]
  exact congrArg _ (comp_groupHom_add s χ ψ)

theorem characterValue_zero' {R : CommRingCat.{u}} {S : CommGroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A] (s : Lie.AffinePoints S.toGrp A) :
    Lie.characterValue (0 : characterLattice S) s = 1 := by
  unfold Lie.characterValue
  exact (congrArg _ (comp_groupHom_zero s)).trans (map_one _)

omit [IsAffineHom G.X.hom] in
/-- The normalized norm of a restricted character, as an additive map on characters. -/
def restrictedNormHom (x : Lie.AffinePoints T₀.toGrp (Adeles F)) :
    characterLattice T →+ Additive ℝ≥0 where
  toFun χ := Additive.ofMul (PositiveRealTorus.normCharacter F T₀ (j ≫ χ) x : ℝ≥0)
  map_zero' := by
    rw [Limits.comp_zero, PositiveRealTorus.normCharacter_apply, characterValue_zero', map_one,
      Units.val_one, ofMul_one]
  map_add' χ ψ := by
    rw [Preadditive.comp_add, ← ofMul_mul, ← Units.val_mul, PositiveRealTorus.normCharacter_apply,
      PositiveRealTorus.normCharacter_apply, PositiveRealTorus.normCharacter_apply,
      characterValue_add', map_mul]

theorem restrictedNorm_sum_nsmul [Fintype (simpleRelativeRoots i ν)]
    (x : Lie.AffinePoints T₀.toGrp (Adeles F)) (k : simpleRelativeRoots i ν → ℕ) :
    (PositiveRealTorus.normCharacter F T₀
        (j ≫ ∑ α : simpleRelativeRoots i ν, k α • (α : characterLattice T)) x : ℝ≥0) =
      ∏ α : simpleRelativeRoots i ν,
        (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) x : ℝ≥0) ^ k α := by
  have h := map_sum (restrictedNormHom j x) (fun α => k α • (α : characterLattice T)) Finset.univ
  simp only [map_nsmul] at h
  have h' := congrArg Additive.toMul h
  simpa only [restrictedNormHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, toMul_sum,
    toMul_nsmul] using h'

/-- The positive-root product of the modulus formula is a product of powers of the simple-root
norms with nonzero exponents. -/
theorem exists_simpleRoot_exponents [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)
    [Fintype (simpleRelativeRoots i ν)] :
    ∃ e : simpleRelativeRoots i ν → ℕ, (∀ α, e α ≠ 0) ∧
      ∀ x : Lie.AffinePoints T₀.toGrp (Adeles F),
        ∏ᶠ (β : characterLattice T) (_ : β ∈ positiveRelativeRoots i ν),
            (PositiveRealTorus.normCharacter F T₀ (j ≫ β) x : ℝ≥0) ^
              Module.finrank F (weightSpace i β) =
          ∏ α : simpleRelativeRoots i ν,
            (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) x : ℝ≥0) ^ e α := by
  classical
  have hfin := hT.finite_positiveRelativeRoots i ν
  have hex : ∀ β ∈ AddSubmonoid.closure (simpleRelativeRoots i ν),
      ∃ k : simpleRelativeRoots i ν → ℕ, β = ∑ α : simpleRelativeRoots i ν, k α • (α : characterLattice T) := by
    intro β hβ
    induction hβ using AddSubmonoid.closure_induction with
    | mem β hβ =>
      refine ⟨Pi.single ⟨β, hβ⟩ 1, ?_⟩
      simp [Pi.single_apply, ite_smul]
    | zero => exact ⟨0, by simp⟩
    | add β γ _ _ hβ hγ =>
      obtain ⟨k, rfl⟩ := hβ
      obtain ⟨k', rfl⟩ := hγ
      exact ⟨k + k', by simp [add_smul, Finset.sum_add_distrib]⟩
  let n : characterLattice T → simpleRelativeRoots i ν → ℕ := fun β =>
    if hβ : β ∈ simpleRelativeRoots i ν then Pi.single ⟨β, hβ⟩ 1
    else if h : β ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) then (hex β h).choose
    else 0
  have hn : ∀ β ∈ positiveRelativeRoots i ν, β = ∑ α : simpleRelativeRoots i ν, n β α • (α : characterLattice T) := by
    intro β hβ
    by_cases hs : β ∈ simpleRelativeRoots i ν
    · simp [n, hs, Pi.single_apply, ite_smul]
    · have hc := positiveRelativeRoots_subset_closure_simpleRelativeRoots i ν hβ
      have hc' : β ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) := hc
      have hnβ : n β = (hex β hc').choose := by
        simp only [n, hs, hc', dite_false, dite_true]
      rw [hnβ]
      exact (hex β hc').choose_spec
  have hnα : ∀ α : simpleRelativeRoots i ν, n α α = 1 := by
    intro α
    simp [n, α.2]
  let m : characterLattice T → ℕ := fun β => Module.finrank F (weightSpace i β)
  refine ⟨fun α => ∑ β ∈ hfin.toFinset, n β α * m β, ?_, ?_⟩
  · intro α
    have hαΦ : (α : characterLattice T) ∈ hfin.toFinset :=
      hfin.mem_toFinset.mpr (simpleRelativeRoots_subset_positive i ν α.2)
    have hm : m α ≠ 0 := by
      have hne := ((mem_relativeRoots).1 α.2.1.1).2
      intro h0
      exact hne (Submodule.finrank_eq_zero.mp h0)
    have hle := Finset.single_le_sum (f := fun β => n β α * m β)
      (fun _ _ => Nat.zero_le _) hαΦ
    rw [hnα α, one_mul] at hle
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.pos_of_ne_zero hm) hle)
  · intro x
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    calc ∏ β ∈ hfin.toFinset,
          (PositiveRealTorus.normCharacter F T₀ (j ≫ β) x : ℝ≥0) ^ m β
        = ∏ β ∈ hfin.toFinset, ∏ α : simpleRelativeRoots i ν,
            (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) x : ℝ≥0) ^
              (n β α * m β) := by
          refine Finset.prod_congr rfl fun β hβ => ?_
          have hβ' := restrictedNorm_sum_nsmul i ν j x (n β)
          rw [← hn β (hfin.mem_toFinset.mp hβ)] at hβ'
          rw [hβ', ← Finset.prod_pow]
          refine Finset.prod_congr rfl fun α _ => ?_
          rw [pow_mul]
      _ = ∏ α : simpleRelativeRoots i ν, ∏ β ∈ hfin.toFinset,
            (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) x : ℝ≥0) ^
              (n β α * m β) := Finset.prod_comm
      _ = _ := by
          refine Finset.prod_congr rfl fun α _ => ?_
          rw [Finset.prod_pow_eq_pow_sum]

end Exponents

section Main

/-- **Finite Haar measure of Siegel sets from the modulus formula.** Compactness of unipotent
rational quotients, the modulus formula for the positive torus on `N(𝔸_F)` and compactness of
simple-root boxes imply `SiegelProductFiniteMeasureStatement`. -/
theorem siegelProductFiniteMeasureStatement_of_inputs
    (hU : UnipotentRationalQuotientCompactStatement.{u})
    (hmod : PositiveTorusUnipotentModulusStatement.{u})
    (hbox : SimpleRootBoxCompactStatement.{u}) :
    SiegelProductFiniteMeasureStatement.{u} := by
  classical
  intro F _ _ G _ _ hG T i ν T₀ j hsetup C t hIw hcompat
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hTmax, -, -, -, -, hlevi, -, ⟨D, d, t₀, hd, -, ht₀⟩, -⟩ := id hsetup
  -- the adelic subgroups, read inside `G(𝔸_F)¹`
  have hNH := standardUnipotentImage_le_normOne F G T i ν T₀ j hsetup hU
  have hKH : C.compactSubgroup ≤ normOneSubgroup F G :=
    compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup
  have hHc := isClosed_normOneSubgroup F G
  let Q : Subgroup (normOneSubgroup F G) := (standardParabolicImage F G T i ν).subgroupOf _
  let M : Subgroup (normOneSubgroup F G) := (standardLeviImage F G T i ν).subgroupOf _
  let U : Subgroup (normOneSubgroup F G) := (standardUnipotentImage F G T i ν).subgroupOf _
  let K : Subgroup (normOneSubgroup F G) := C.compactSubgroup.subgroupOf _
  have hQ : IsClosed (Q : Set (normOneSubgroup F G)) :=
    (isClosed_standardParabolicImage F G T i ν).preimage continuous_subtype_val
  have hM : IsClosed (M : Set (normOneSubgroup F G)) :=
    (isClosed_standardLeviImage F G T i ν).preimage continuous_subtype_val
  have hUc : IsClosed (U : Set (normOneSubgroup F G)) :=
    (isClosed_standardUnipotentImage F G T i ν).preimage continuous_subtype_val
  have hK : IsCompact (K : Set (normOneSubgroup F G)) :=
    hHc.isClosedEmbedding_subtypeVal.isCompact_preimage C.compact_compactSubgroup
  -- the Levi decomposition `Q = M ⋉ U` with continuous projection
  obtain ⟨f, hfc, hfM, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hsetup
  have hfH : ∀ q : Q, f ⟨(q : normOneSubgroup F G), q.2⟩ ∈ normOneSubgroup F G := by
    intro q
    let p : standardParabolicImage F G T i ν := ⟨(q : normOneSubgroup F G), q.2⟩
    have hmem : (f p)⁻¹ * (p : AdelicGroupPoints F G) ∈ standardUnipotentImage F G T i ν := by
      have h := (hfker ((⟨f p, standardLeviImage_le_parabolic F G T i ν (hfM p)⟩ :
        standardParabolicImage F G T i ν)⁻¹ * p)).mp (by
          rw [map_mul, map_inv, hfid (f p) (hfM p), inv_mul_cancel])
      simpa using h
    have h1 : (p : AdelicGroupPoints F G) ∈ normOneSubgroup F G := (q : normOneSubgroup F G).2
    have h2 := (normOneSubgroup F G).mul_mem h1 ((normOneSubgroup F G).inv_mem (hNH hmem))
    simpa using h2
  let ιQ : Q →* standardParabolicImage F G T i ν :=
    ((normOneSubgroup F G).subtype.comp Q.subtype).codRestrict _ (fun q => q.2)
  let fH : Q →* normOneSubgroup F G := (f.comp ιQ).codRestrict _ hfH
  have hMQ : M ≤ Q := fun x hx => standardLeviImage_le_parabolic F G T i ν hx
  have hUQ : U ≤ Q := fun x hx => standardUnipotentImage_le_parabolic F G T i ν hx
  have hfHM : ∀ q, fH q ∈ M := fun q => hfM _
  have hfHid : ∀ m (hm : m ∈ M), fH ⟨m, hMQ hm⟩ = m := fun m hm => Subtype.ext (hfid _ hm)
  have hfHker : ∀ q, fH q = 1 ↔ (q : normOneSubgroup F G) ∈ U := fun q =>
    (show fH q = 1 ↔ f ⟨(q : normOneSubgroup F G), q.2⟩ = 1 from
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩).trans (hfker _)
  have hsd := Aubert.General.IsSemidirectDecomposition.of_retraction hMQ hUQ fH hfHM hfHid
    hfHker
  have hfHc : Continuous fH := by
    have : Continuous (fun q : Q => f ⟨(q : normOneSubgroup F G), q.2⟩) :=
      hfc.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    exact this.subtype_mk _
  have hp := Aubert.General.IsSemidirectDecomposition.continuous_of_retraction_projection
    hMQ hUQ fH hfHM hfHid hfHker hfHc
  -- the saturated-set bound from `G(𝔸_F)¹ = Q K`
  have : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let μQ : Measure Q := Measure.haar
  have hQK : ∀ g : normOneSubgroup F G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k := by
    intro g
    have hg : (g : AdelicGroupPoints F G) ∈
        Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
          (C.compactSubgroup : Set (AdelicGroupPoints F G)) := by
      rw [hIw.2]
      exact Set.mem_univ _
    obtain ⟨_, ⟨y, rfl⟩, k, hk, hyk⟩ := hg
    have hyH : map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) y ∈
        normOneSubgroup F G := by
      have hy : map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) y =
          (g : AdelicGroupPoints F G) * k⁻¹ := by
        rw [← hyk]
        exact (mul_inv_cancel_right _ _).symm
      rw [hy]
      exact (normOneSubgroup F G).mul_mem g.2 ((normOneSubgroup F G).inv_mem (hKH hk))
    exact ⟨⟨_, hyH⟩, ⟨y, rfl⟩, ⟨k, hKH hk⟩, hk, Subtype.ext hyk.symm⟩
  obtain ⟨c, -, hc⟩ := CompactFactorization.exists_pos_measure_eq_of_mul_mem
    (Measure.haar : Measure (normOneSubgroup F G)) Q hQ K hK hQK μQ
  -- the positive torus inside `G(𝔸_F)¹`
  have hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G := by
    rw [← ht₀, ← hd.2]
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ t₀.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  let a := positiveMapNormOneOfDerived F G T i T₀ j hT
  have haM : ∀ x, a.toMonoidHom x ∈ M := fun x =>
    positiveMap_mem_standardLeviImage F G T i ν T₀ j x
  have hacent : ∀ x, ∀ m ∈ M, Commute (a.toMonoidHom x) m := by
    intro x m hm
    have hm' : (m : AdelicGroupPoints F G) ∈ (torusCentralizer i).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
      rw [← hlevi, ← standardLeviImage_eq]
      exact hm
    have hm'' : ∀ (V : Over (Spec (CommRingCat.of F)))
        (b : V ⟶ (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F))))
        (s : V ⟶ T.X), Commute (b ≫ (m : AdelicGroupPoints F G)) (s ≫ i.hom.hom) := hm'
    have h' : Commute (m : AdelicGroupPoints F G) (positiveMap F G T i T₀ j x) := by
      have h := hm'' _ (𝟙 _) (x.val ≫ (CommGroupScheme.groupHom j).hom.hom)
      rw [Category.id_comp] at h
      convert h using 1
      change x.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom = _
      simp only [Grp.comp_hom_hom, Category.assoc]
    exact Subtype.ext h'.symm.eq
  have haK : ∀ k ∈ K, k ∈ Q → ∀ x, Commute k (a.toMonoidHom x) := by
    intro k hk hkQ x
    exact Subtype.ext (hcompat (k : AdelicGroupPoints F G) hk hkQ x).eq
  -- simple roots, the compact box and the modulus
  have hTs : IsSplitTorus T.toGrp := hTmax.1.1
  let : Fintype (simpleRelativeRoots i ν) := (hTs.finite_simpleRelativeRoots i ν).fintype
  let lam : simpleRelativeRoots i ν → PositiveRealTorus.intrinsicSubgroup F T₀ →* ℝ≥0ˣ :=
    fun α => (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T))).toMonoidHom.comp
      (PositiveRealTorus.intrinsicSubgroup F T₀).subtype
  have hboxc : IsCompact (SiegelSetMeasure.dyadicBox lam) := by
    have h := hbox F G hG T i ν T₀ j hsetup 2
    convert h using 1
    ext x
    simp only [SiegelSetMeasure.dyadicBox, Set.mem_ofPred_eq, Subtype.forall]
    exact Iff.rfl
  obtain ⟨e, he, hexp⟩ := exists_simpleRoot_exponents (G := G) i ν j hTs
  have hδ : ∀ x, ∏ α, (lam α x : ℝ≥0) ^ e α ≤
      (HaarModulus.closedNormalizerCharacter U hUc
        ⟨a.toMonoidHom x, hsd.levi_le_normalizer (haM x)⟩ : ℝ≥0) := by
    intro x
    have h1 := Aubert.General.closedNormalizerCharacter_subgroupOf_of_mem
      (normOneSubgroup F G) (standardUnipotentImage F G T i ν) hHc
      (isClosed_standardUnipotentImage F G T i ν) hNH (a.toMonoidHom x)
      (positiveMap_mem_normalizer F G T i ν T₀ j x) (hsd.levi_le_normalizer (haM x))
    have h2 := (hexp x.1).symm.trans (hmod F G hG T i ν T₀ j hsetup x).symm
    exact le_of_eq (h2.trans (congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) h1.symm))
  -- the abstract Siegel-set bound
  have key := SiegelSetMeasure.measure_mul_chamber_mul_lt_top
    (Measure.haar : Measure (normOneSubgroup F G)) hQ hM hUc hK hsd hp μQ c
    (fun S hS hsat => (hc S hS hsat).le)
    (ΩU := Subtype.val ⁻¹'
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) '' C.omegaN))
    (ΩM := Subtype.val ⁻¹'
      ((fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) '' C.omegaM))
    (hHc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (C.compact_omegaN.image (map F _ G (Standard.unipotentHom i ν ∅)).continuous))
    (by rintro g ⟨n, -, hn⟩; exact ⟨n, hn⟩)
    (hHc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (C.compact_omegaM.image
        ((map F _ G (Standard.leviHom i ν ∅)).continuous.comp continuous_subtype_val)))
    (by rintro g ⟨m, -, hm⟩; exact ⟨(m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)), hm⟩)
    a.toMonoidHom a.continuous haM hacent haK lam hboxc e he hδ (t := (t : ℝ≥0)) t.ne_zero
  refine lt_of_le_of_lt (measure_mono ?_) key
  intro g hg
  obtain ⟨n, hn, m, hm, x, hx, k, hk, hgeq⟩ :=
    (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j
      (PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)
      (g : AdelicGroupPoints F G)).mp hg
  have hnH : map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n ∈
      normOneSubgroup F G := hNH ⟨n, rfl⟩
  have hmH : map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m.1 ∈
      normOneSubgroup F G :=
    map_normOneSubgroup_le F _ G (Standard.leviHom i ν ∅) ⟨m.1, m.2, rfl⟩
  have hgdecomp : g = ⟨_, hnH⟩ * ⟨_, hmH⟩ * a.toMonoidHom x * ⟨k, hKH hk⟩ :=
    Subtype.ext hgeq.symm
  rw [hgdecomp]
  refine Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩)
    ⟨x, ?_, rfl⟩) hk
  intro α
  exact Units.val_le_val.mpr (hx α α.2)

end Main

end Langlands.Global.AdelicSiegelFactors
