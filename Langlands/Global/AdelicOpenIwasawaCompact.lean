import Langlands.Global.AdelicGroupProduct
import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Langlands.Global.AdelicPositiveTorusCompatibility
import Langlands.Global.InfinitePlaceLeviIwasawaProof
import Langlands.Global.AdelicParabolicCompactCover

/-! # A compact subgroup, an open subgroup and finitely many translates for the Siegel setup

For an actual algebraic Siegel setup with canonical minimal parabolic `P`, this file builds,
without any finite-place Iwasawa decomposition:

* a compact subgroup `K ≤ G(𝔸_F)` whose archimedean components lie in Levi-compatible
  maximal compact subgroups `K_w` and whose finite part lies in a compact open subgroup `U`
  of `G(𝔸_f)`;
* the open subgroup `H₁` of points whose finite part lies in `U`, with `K ≤ H₁` and
  `H₁ ⊆ P(𝔸_F) K`;
* a finite set `W ⊆ G(𝔸_F)¹` with `P(𝔸_F) (K W) = G(𝔸_F)`.

The parabolic part of `K` commutes with the positive torus `A_{T₀}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The archimedean component of an actual adelic point is the component of its infinite
adelic part. -/
theorem atInfinitePlace_eq_atPlace_infinite (w : InfinitePlace F) (g : AdelicGroupPoints F G) :
    atInfinitePlace F G w g = InfiniteAdelicGroupPoints.atPlace F G w (infinite F G g) := by
  apply G.affinePointEvaluation_injective
  funext a
  dsimp only
  rw [atInfinitePlace_evaluation, InfiniteAdelicGroupPoints.atPlace_evaluation]
  change _ = G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F))
    (G.affinePointMap (CommAlgCat.ofHom
      (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) g) a w
  rw [G.affinePointEvaluation_map]
  rfl

/-- The finite adelic part commutes with the adelic map of a group-scheme homomorphism. -/
theorem finite_map {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    (f : G ⟶ H) (g : AdelicGroupPoints F G) :
    finite F H (map F G H f g) =
      G.affinePointsTarget f (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) (finite F G g) :=
  DFunLike.congr_fun (G.affinePointsTarget_naturality f
    (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))) g

end AdelicGroupPoints

namespace AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- **Compact subgroup, open subgroup and finite translates.** For every actual algebraic
Siegel setup of a connected reductive group over a number field there are a compact subgroup
`K` and an open subgroup `H₁ ⊇ K` of `G(𝔸_F)` with `H₁ ⊆ P(𝔸_F) K`, such that the parabolic
part of `K` commutes with `A_{T₀}`, and a finite set `W ⊆ G(𝔸_F)¹` with
`P(𝔸_F) (K W) = G(𝔸_F)`, where `P` is the canonical minimal standard parabolic. -/
theorem exists_compact_openSubgroup_finite_cover
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ (K H₁ : Subgroup (AdelicGroupPoints F G)) (W : Set (AdelicGroupPoints F G)),
      IsCompact (K : Set (AdelicGroupPoints F G)) ∧
        IsOpen (H₁ : Set (AdelicGroupPoints F G)) ∧ K ≤ H₁ ∧
        (H₁ : Set (AdelicGroupPoints F G)) ⊆
          Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
            (K : Set (AdelicGroupPoints F G)) ∧
        IsPositiveTorusCompatible F G T i ν T₀ j K ∧
        W.Finite ∧ W ⊆ (normOneSubgroup F G : Set (AdelicGroupPoints F G)) ∧
        Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
            ((K : Set (AdelicGroupPoints F G)) * W) = Set.univ := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hp : IsParabolicSubgroup (Standard.parabolicHom i ν ∅) := hS.2.2.1.isParabolicSubgroup
  have hl : IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) := hS.2.2.2.1
  have : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left := hp.isClosedSubgroup
  have : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left
  set P := Standard.parabolicScheme i ν ∅ with hPdef
  set p := Standard.parabolicHom i ν ∅ with hpdef
  choose Karch hKarch using InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement F G hG P p hp
    (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅) hl
  let U : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
    FiniteAdelicGroupPoints.compactOpenSubgroup F G
  let Kinf : Subgroup (InfiniteAdelicGroupPoints F G) :=
    (Subgroup.pi Set.univ Karch).comap
      (InfiniteAdelicGroupPoints.completions F G).toMulEquiv.toMonoidHom
  let K : Subgroup (AdelicGroupPoints F G) :=
    (Kinf.prod (U : Subgroup (FiniteAdelicGroupPoints F G))).comap
      (split F G).toMulEquiv.toMonoidHom
  let H₁ : Subgroup (AdelicGroupPoints F G) :=
    (U : Subgroup (FiniteAdelicGroupPoints F G)).comap (finite F G).toMonoidHom
  have hmemK : ∀ g, g ∈ K ↔
      (∀ w, atInfinitePlace F G w g ∈ Karch w) ∧ finite F G g ∈ U := by
    intro g
    simp only [K, Kinf, Subgroup.mem_comap, Subgroup.mem_prod, Subgroup.mem_pi,
      Set.mem_univ, true_implies, atInfinitePlace_eq_atPlace_infinite]
    rfl
  have hmemH : ∀ g, g ∈ H₁ ↔ finite F G g ∈ U := fun g => Iff.rfl
  -- compactness of `K`
  have hKinf : IsCompact (Kinf : Set (InfiniteAdelicGroupPoints F G)) := by
    have hpi : IsCompact (Set.univ.pi fun w => (Karch w : Set (InfinitePlaceGroupPoints F G w))) :=
      isCompact_univ_pi fun w => (hKarch w).1.1
    have := (InfiniteAdelicGroupPoints.completions F G).toHomeomorph.isCompact_preimage.mpr hpi
    convert this using 1
    ext x
    simp [Kinf, Subgroup.mem_pi]
  have hKc : IsCompact (K : Set (AdelicGroupPoints F G)) := by
    have hprod := hKinf.prod (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G)
    have := (split F G).toHomeomorph.isCompact_preimage.mpr hprod
    convert this using 1
    ext g
    exact Iff.rfl
  -- openness of `H₁`
  have hH₁ : IsOpen (H₁ : Set (AdelicGroupPoints F G)) :=
    U.isOpen.preimage (finite F G).continuous
  have hKH₁ : K ≤ H₁ := fun g hg => ((hmemK g).1 hg).2
  -- `H₁ ⊆ P(𝔸) K`, from the archimedean Iwasawa decompositions
  have hH₁P : (H₁ : Set (AdelicGroupPoints F G)) ⊆
      Set.range (map F P G p) * (K : Set (AdelicGroupPoints F G)) := by
    intro g hg
    have hloc : ∀ w : InfinitePlace F, ∃ q : P.affinePoints (CommAlgCat.of F w.Completion),
        ∃ k ∈ Karch w, P.affinePointsTarget p _ q * k = atInfinitePlace F G w g := by
      intro w
      have hw : atInfinitePlace F G w g ∈
          Set.range (P.affinePointsTarget p (CommAlgCat.of F w.Completion)) *
            (Karch w : Set (InfinitePlaceGroupPoints F G w)) := by
        rw [(hKarch w).2.1]
        exact Set.mem_univ _
      obtain ⟨_, ⟨q, rfl⟩, k, hk, h⟩ := hw
      exact ⟨q, k, hk, h⟩
    choose q k hk hqk using hloc
    let x : AdelicGroupPoints F P := ofInfinite F P (InfiniteAdelicGroupPoints.assemble F P q)
    refine ⟨map F P G p x, ⟨x, rfl⟩, (map F P G p x)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    rw [SetLike.mem_coe, hmemK]
    constructor
    · intro w
      have h1 : atInfinitePlace F G w (map F P G p x) =
          P.affinePointsTarget p (CommAlgCat.of F w.Completion) (q w) := by
        have h2 := atPlace_map F P p (.inl w) x
        have h3 : atPlace F P (.inl w) x = q w := by
          change atInfinitePlace F P w x = q w
          rw [atInfinitePlace_eq_atPlace_infinite, infinite_ofInfinite,
            InfiniteAdelicGroupPoints.atPlace_assemble]
        rw [h3] at h2
        exact h2
      rw [map_mul, map_inv, h1, ← hqk w, inv_mul_cancel_left]
      exact hk w
    · rw [map_mul, map_inv, finite_map, finite_ofInfinite, map_one, inv_one, one_mul]
      exact (hmemH g).1 hg
  -- positive-torus compatibility, from the archimedean components only
  have hcompat : IsPositiveTorusCompatible F G T i ν T₀ j K :=
    isPositiveTorusCompatible_of_setup_leviCompatibleIwasawaCompacts F G T i ν T₀ j hS K
      Karch hKarch (fun w k hk => ((hmemK k).1 hk).1 w)
  -- finitely many right `H₁`-translates cover a compact norm-one parabolic cover
  obtain ⟨Ω₀, hΩ₀c, hΩ₀1, hcov₀⟩ := hS.hasCompactNormOneParabolicCover F G T i ν T₀ j hG
  obtain ⟨W, hWΩ, hWfin, hΩW⟩ := hΩ₀c.elim_finite_subcover_image (b := Ω₀)
    (c := fun x => (H₁ : Set (AdelicGroupPoints F G)) * {x})
    (fun x _ => hH₁.mul_right)
    (fun x hx => Set.mem_iUnion₂.mpr ⟨x, hx, Set.mem_mul.mpr ⟨1, H₁.one_mem, x, rfl, one_mul x⟩⟩)
  refine ⟨K, H₁, W, hKc, hH₁, hKH₁, hH₁P, hcompat, hWfin, hWΩ.trans hΩ₀1, ?_⟩
  refine Set.eq_univ_of_forall fun g => ?_
  have hg : g ∈ Set.range (map F P G p) * Ω₀ := by
    rw [hcov₀]
    exact Set.mem_univ g
  obtain ⟨_, ⟨y, rfl⟩, z, hz, hyz⟩ := hg
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp (hΩW hz)
  obtain ⟨h, hh, w', hw', hhw⟩ := Set.mem_mul.mp hzw
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  obtain ⟨_, ⟨y', rfl⟩, k, hk, hyk⟩ := hH₁P hh
  refine ⟨map F P G p (y * y'), ⟨y * y', rfl⟩, k * w', Set.mul_mem_mul hk hw, ?_⟩
  rw [← hyz, ← hhw, ← hyk, map_mul]
  group

end AdelicSiegelFactors

end Langlands.Global
