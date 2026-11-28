import Langlands.Global.AdelicArchimedeanTripleCell
import Langlands.GroupScheme.Dynamic.RingPointOpenCell
import Langlands.Global.AdelicSiegelConjugationBound
import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof
import Langlands.Global.AdelicRationalHeightReduction
import Langlands.GroupScheme.Dynamic.GmOrbitInversion
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # The archimedean open cell for an algebraic Siegel setup

For an algebraic Siegel setup `(T, i, ν, T₀, j)` of a connected reductive group `G` over a number
field, `exists_siegel_archimedeanCell` gives an identity neighborhood `W` of `G(𝔸)` whose points
are `n q` with `n` in a compact subset of the standard unipotent subgroup `N(𝔸)` and `a q a⁻¹` in
a fixed compact set for every point `a` of the weak simple-root chamber. It combines the opposite
cell `U(-ζ) · Z(ζ) · U(ζ)` of a standard cocharacter `ζ` at the archimedean places
(`Dynamic.affinePoints_opposite_cell_mem_nhds_one`), the assembly
`exists_nhds_eq_ofFinite_mul_triple`, the chamber contraction of the opposite unipotent subgroup
(the standard unipotent subgroup of `-ν`) and the commutation of the positive torus with the
standard Levi subgroup and with the finite adelic points. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Topology Opposite
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

section Opposite

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- The opposite cocharacter `t ↦ ζ(t⁻¹)` is the cocharacter `-ζ`. -/
theorem powerHom_neg_one_comp_groupHom (zeta : cocharacterLattice T) :
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        (CommGroupScheme.groupHom zeta ≫ i) =
      CommGroupScheme.groupHom (-zeta) ≫ i := by
  apply hom_ext_points
  intro Y x
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [GmOrbitInversion.comp_groupHom_neg]

variable [IsAffineHom G.X.hom]

/-- The negative of a generic cocharacter is generic. -/
theorem isGenericCocharacter_neg {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) :
    IsGenericCocharacter i (-ν) := by
  intro a ha
  simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)

variable [Mono i.hom.hom.left]

/-- With a relative root system, the positive roots for `-ν` are the negatives of the positive
roots for `ν`. -/
theorem neg_mem_positiveRelativeRoots_of_neg (hR : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) {ν : cocharacterLattice T} {α : characterLattice T}
    (hα : α ∈ positiveRelativeRoots i (-ν)) : -α ∈ positiveRelativeRoots i ν := by
  refine ⟨hR.neg_mem_relativeRoots i hT hα.1, ?_⟩
  have h := hα.2
  simp only [map_neg, LinearMap.neg_apply] at h ⊢
  linarith

/-- With a relative root system, the simple roots for `-ν` are the negatives of the simple
roots for `ν`. -/
theorem neg_mem_simpleRelativeRoots_of_neg (hR : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) {ν : cocharacterLattice T} {α : characterLattice T}
    (hα : α ∈ simpleRelativeRoots i (-ν)) : -α ∈ simpleRelativeRoots i ν := by
  refine ⟨neg_mem_positiveRelativeRoots_of_neg i hR hT hα.1, ?_⟩
  rintro ⟨β, hβ, β₂, hβb, hsum⟩
  apply hα.2
  have hβ' : -β ∈ positiveRelativeRoots i (-ν) := by
    refine ⟨hR.neg_mem_relativeRoots i hT hβ.1, ?_⟩
    have h := hβ.2
    simp only [map_neg, LinearMap.neg_apply] at h ⊢
    linarith
  have hβb' : -β₂ ∈ positiveRelativeRoots i (-ν) := by
    refine ⟨hR.neg_mem_relativeRoots i hT hβb.1, ?_⟩
    have h := hβb.2
    simp only [map_neg, LinearMap.neg_apply] at h ⊢
    linarith
  exact ⟨-β, hβ', -β₂, hβb', by rw [← neg_add, ← hsum, neg_neg]⟩

/-- The negative of a standard cocharacter for the empty set is standard for `-ν`. -/
theorem isStandardCocharacter_neg (hR : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν ∅ zeta) :
    IsStandardCocharacter i (-ν) ∅ (-zeta) := by
  refine ⟨Set.empty_subset _, fun α hα => absurd hα (Set.notMem_empty α), fun α hα _ => ?_⟩
  have hpos := neg_mem_positiveRelativeRoots_of_neg i hR hT hα.1
  have h := (hzeta.pairing_pos_iff_not_mem_closure i ν hpos).mpr (by
    rw [AddSubmonoid.closure_empty, AddSubmonoid.mem_bot, neg_eq_zero]
    exact (mem_relativeRoots.mp hα.1.1).1)
  simp only [map_neg, LinearMap.neg_apply] at h ⊢
  linarith

end Opposite

section Chamber

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ T)

/-- The normalized norm of the negative of a character is the inverse norm. -/
theorem normCharacter_comp_neg (x : Lie.AffinePoints T₀.toGrp (Adeles F))
    (α : characterLattice T) :
    PositiveRealTorus.normCharacter F T₀ (j ≫ (-α)) x =
      (PositiveRealTorus.normCharacter F T₀ (j ≫ α) x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Units.ext
  rw [Units.val_mul, ← normCharacter_comp_add_val j x (-α) α, neg_add_cancel,
    normCharacter_comp_zero_val j x, Units.val_one]

/-- The inverse of a point of the weak simple-root chamber of `ν` lies in the weak simple-root
chamber of `-ν` with the same threshold. -/
theorem inv_mem_weakSimpleRootChamber_neg (hR : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) (t : ℝ≥0ˣ) {a : PositiveRealTorus.intrinsicSubgroup F T₀}
    (ha : a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t) :
    a⁻¹ ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i (-ν) t := by
  intro α hα
  have h := ha (-α) (neg_mem_simpleRelativeRoots_of_neg i hR hT hα)
  change t ≤ PositiveRealTorus.normCharacter F T₀ (j ≫ α) ((a : Lie.AffinePoints _ _)⁻¹)
  rw [map_inv, ← normCharacter_comp_neg j]
  exact h

end Chamber

section Contraction

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (mu : cocharacterLattice T)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ T)

/-- **Chamber contraction of compact unipotent sets.** For a maximal split torus `i`, a generic
cocharacter `mu`, a compact set `Ω` of adelic points of the standard unipotent subgroup of `mu` and
a threshold `t`, the conjugates `a⁻¹ n a` (`n ∈ Ω`, `a` in the weak chamber of `mu`) lie in one
compact subset of `G(𝔸)`. -/
theorem exists_isCompact_conj_unipotent_of_generic (hG : IsConnectedReductive G)
    (hTmax : IsMaximalSplitTorus i) (hgen : IsGenericCocharacter i mu)
    (Ω : Set (AdelicGroupPoints F (Standard.unipotentScheme i mu ∅))) (hΩ : IsCompact Ω)
    (t : ℝ≥0ˣ) :
    ∃ K : Set (AdelicGroupPoints F G), IsCompact K ∧
      ∀ n ∈ Ω, ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i mu t,
        (positiveMap F G T i T₀ j a)⁻¹ *
          map F (Standard.unipotentScheme i mu ∅) G (Standard.unipotentHom i mu ∅) n *
            positiveMap F G T i T₀ j a ∈ K := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, rho, hrho⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hinj : Function.Injective (RepresentationGrowth.adelicMatrix F G rho) :=
      (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
    have : Subsingleton (AdelicGroupPoints F G) := hinj.subsingleton
    exact ⟨Set.univ, Set.finite_univ.isCompact, fun _ _ _ _ => Set.mem_univ _⟩
  · obtain ⟨B, hB⟩ := exists_adelicHeight_conj_unipotent_le_of_maximalSplit F G T i mu T₀ j hG
      hTmax hgen rho hN Ω hΩ t
    obtain ⟨-, hprop⟩ := RepresentationGrowth.adelicRepresentationHeightProperness F G N rho hN
    refine ⟨RepresentationGrowth.adelicHeight F G rho ⁻¹' Set.Icc 0 B,
      (hprop hrho).isCompact_preimage isCompact_Icc, fun n hn a ha => ⟨?_, hB n hn a ha⟩⟩
    exact zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN _)

end Contraction

section Represented

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}

/-- The points of a represented subgroup functor over an algebra are the image of the points of
a representing homomorphism. -/
theorem carrier_eq_range_of_isRepresentedBy {S : SubgroupFunctor G} {iota : H ⟶ G}
    (hiota : S.IsRepresentedBy iota) (A : CommAlgCat.{u} R) :
    (S.carrier ((algSpec R).obj (op A)) : Set (G.affinePoints A)) =
      Set.range (H.affinePointsTarget iota A) := by
  rw [← hiota.2]
  ext x
  exact SubgroupFunctor.mem_range

end Represented

section Cell

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- **The archimedean open cell of a Siegel setup.** There are an identity neighborhood `W` of
`G(𝔸)`, a compact set `N₁` of adelic points of the standard unipotent subgroup `N` and a compact
`Q ⊆ G(𝔸)` such that every `g ∈ W` is `n q` with `n ∈ N₁` and `a q a⁻¹ ∈ Q` for every point `a`
of the weak simple-root chamber `|β(a)| ≥ t`. -/
theorem exists_siegel_archimedeanCell (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∃ W ∈ 𝓝 (1 : AdelicGroupPoints F G),
      ∃ N₁ : Set (AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)), IsCompact N₁ ∧
      ∃ Q : Set (AdelicGroupPoints F G), IsCompact Q ∧
      ∀ g ∈ W, ∃ n ∈ N₁, ∀ a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t,
        positiveMap F G T i T₀ j a *
            ((map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n)⁻¹ * g) *
          (positiveMap F G T i T₀ j a)⁻¹ ∈ Q := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hTmax, hgen, -, -, -, hlevi, -, hder, -⟩ := id hsetup
  obtain ⟨D, d, t₀, -, ht₀, -⟩ := hder
  have hT₀ : IsSplitTorus T₀.toGrp := ht₀.isSplitSubtorus.1
  have : Mono i.hom.hom.left := hTmax.isSplitSubtorus.mono
  have hT : IsSplitTorus T.toGrp := hTmax.isSplitSubtorus.1
  have hR : HasRelativeRootSystem i := relativeRootSystem F G hG T i hTmax
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨⟨zeta, hzeta⟩, hcomp⟩ :=
    standardCocharacter F G hG T i hTmax ν hgen ∅ (Set.empty_subset _)
  obtain ⟨-, hMeq, hNeq⟩ := hcomp zeta hzeta
  obtain ⟨-, hcomp'⟩ := standardCocharacter F G hG T i hTmax (-ν)
    (isGenericCocharacter_neg i hgen) ∅ (Set.empty_subset _)
  obtain ⟨-, -, hUeq⟩ := hcomp' (-zeta) (isStandardCocharacter_neg i hR hT hzeta)
  -- the three closed subgroups
  have hclU := Standard.isClosedSubgroup_unipotentHom i (-ν) ∅
  have hclM := Standard.isClosedSubgroup_leviHom i ν ∅
  have hclN := Standard.isClosedSubgroup_unipotentHom i ν ∅
  have : IsAffineHom (Standard.unipotentScheme i (-ν) ∅).X.hom := hclU.isAffineHom
  have : IsAffineHom (Standard.leviScheme i ν ∅).X.hom := hclM.isAffineHom
  have : IsAffineHom (Standard.unipotentScheme i ν ∅).X.hom := hclN.isAffineHom
  have : IsAffine (Standard.unipotentScheme i (-ν) ∅).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i (-ν) ∅).X.hom
  have : IsAffine (Standard.leviScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.leviScheme i ν ∅).X.hom
  have : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i ν ∅).X.hom
  have : IsClosedImmersion (Standard.unipotentHom i (-ν) ∅).hom.hom.left := hclU
  have : IsClosedImmersion (Standard.leviHom i ν ∅).hom.hom.left := hclM
  have : IsClosedImmersion (Standard.unipotentHom i ν ∅).hom.hom.left := hclN
  -- the archimedean cells
  have hcell : ∀ v : InfinitePlace F, ∀ A ∈ 𝓝 (1 : InfinitePlaceGroupPoints F G v),
      {x : InfinitePlaceGroupPoints F G v |
        ∃ a ∈ A ∩ Set.range ((Standard.unipotentScheme i (-ν) ∅).affinePointsTarget
          (Standard.unipotentHom i (-ν) ∅) (CommAlgCat.of F v.Completion)),
        ∃ b ∈ A ∩ Set.range ((Standard.leviScheme i ν ∅).affinePointsTarget
          (Standard.leviHom i ν ∅) (CommAlgCat.of F v.Completion)),
        ∃ c ∈ A ∩ Set.range ((Standard.unipotentScheme i ν ∅).affinePointsTarget
          (Standard.unipotentHom i ν ∅) (CommAlgCat.of F v.Completion)),
          x = a * b * c} ∈ 𝓝 (1 : InfinitePlaceGroupPoints F G v) := by
    intro v A hA
    have h := Dynamic.affinePoints_opposite_cell_mem_nhds_one F v.Completion G
      (CommGroupScheme.groupHom zeta ≫ i) A hA A hA A hA
    rw [powerHom_neg_one_comp_groupHom i zeta, ← hUeq, ← hMeq, ← hNeq,
      carrier_eq_range_of_isRepresentedBy (Standard.isRepresentedBy_unipotentHom i (-ν) ∅),
      carrier_eq_range_of_isRepresentedBy (Standard.isRepresentedBy_leviHom i ν ∅),
      carrier_eq_range_of_isRepresentedBy (Standard.isRepresentedBy_unipotentHom i ν ∅)] at h
    exact h
  obtain ⟨W₀, hW₀, K₁, hK₁, K₂, hK₂, K₃, hK₃, L, hL, hdec⟩ :=
    exists_nhds_eq_ofFinite_mul_triple (Standard.unipotentHom i (-ν) ∅)
      (Standard.leviHom i ν ∅) (Standard.unipotentHom i ν ∅) hcell
  obtain ⟨Kc, hKc, hcon⟩ := exists_isCompact_conj_unipotent_of_generic i (-ν) j hG hTmax
    (isGenericCocharacter_neg i hgen) K₁⁻¹ hK₁.inv t
  refine ⟨W₀⁻¹, inv_mem_nhds_one _ hW₀, K₃⁻¹, hK₃.inv,
    (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) '' K₂⁻¹) * Kc *
      (ofFinite F G '' L⁻¹),
    ((hK₂.inv.image (map F _ G _).continuous).mul hKc).mul
      (hL.inv.image (ofFinite F G).continuous), ?_⟩
  intro g hg
  obtain ⟨l, hl, x₁, hx₁, x₂, hx₂, x₃, hx₃, hgdec⟩ := hdec g⁻¹ hg
  refine ⟨x₃⁻¹, Set.inv_mem_inv.mpr hx₃, fun a ha => ?_⟩
  set pa := positiveMap F G T i T₀ j a with hpa
  set mU := map F (Standard.unipotentScheme i (-ν) ∅) G (Standard.unipotentHom i (-ν) ∅)
  set mM := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)
  set mN := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  have hq : (mN x₃⁻¹)⁻¹ * g = mM x₂⁻¹ * mU x₁⁻¹ * ofFinite F G l⁻¹ := by
    have hg' : g = (g⁻¹)⁻¹ := (inv_inv g).symm
    rw [hg', hgdec]
    simp only [map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hpainf : pa = ofInfinite F G (infinite F G pa) := by
    conv_lhs => rw [← pair_projections F G pa]
    rw [finite_positiveMap F G T i T₀ j hT₀ a, ofInfinite_eq_pair]
  have hcomF : Commute pa (ofFinite F G l⁻¹) := by
    rw [hpainf]
    exact factors_commute F G _ _
  have hcomM : Commute pa (mM x₂⁻¹) :=
    positiveMap_commute_of_mem_standardLevi hlevi j a ⟨x₂⁻¹, rfl⟩
  have heq : pa * ((mN x₃⁻¹)⁻¹ * g) * pa⁻¹ =
      mM x₂⁻¹ * (pa * mU x₁⁻¹ * pa⁻¹) * ofFinite F G l⁻¹ := by
    rw [hq]
    calc pa * (mM x₂⁻¹ * mU x₁⁻¹ * ofFinite F G l⁻¹) * pa⁻¹
        = (pa * mM x₂⁻¹) * mU x₁⁻¹ * (ofFinite F G l⁻¹ * pa⁻¹) := by group
      _ = (mM x₂⁻¹ * pa) * mU x₁⁻¹ * (pa⁻¹ * ofFinite F G l⁻¹) := by
          rw [hcomM.eq, (hcomF.inv_left).eq]
      _ = mM x₂⁻¹ * (pa * mU x₁⁻¹ * pa⁻¹) * ofFinite F G l⁻¹ := by group
  rw [heq]
  refine Set.mul_mem_mul (Set.mul_mem_mul ⟨x₂⁻¹, Set.inv_mem_inv.mpr hx₂, rfl⟩ ?_)
    ⟨l⁻¹, Set.inv_mem_inv.mpr hl, rfl⟩
  have h := hcon x₁⁻¹ (Set.inv_mem_inv.mpr hx₁) a⁻¹
    (inv_mem_weakSimpleRootChamber_neg i j hR hT t ha)
  rwa [map_inv (positiveMap F G T i T₀ j), inv_inv] at h

end Cell

end Langlands.Global.AdelicSiegelFactors
