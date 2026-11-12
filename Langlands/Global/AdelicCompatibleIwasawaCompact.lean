import Langlands.Global.AdelicPositiveTorusCompatibility
import Langlands.Global.AdelicIwasawaAssembly
import Langlands.Global.FinitePlaceIwasawaStatement

/-! # A compatible maximal compact subgroup for the actual Siegel setup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

/-- For every actual algebraic Siegel setup there is a maximal compact subgroup `K` of
`G(𝔸_F)` with `P(𝔸_F) K = G(𝔸_F)` for the canonical minimal parabolic `P`, whose parabolic
part `P(𝔸_F) ∩ K` commutes with the positive torus `A_{T₀}`. -/
def AdelicCompatibleIwasawaCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          ∃ K : Subgroup (AdelicGroupPoints F G),
            IsParabolicIwasawaCompact F G
                (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K ∧
              IsPositiveTorusCompatible F G T i ν T₀ j K

section Local

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
  (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)

/-- The local condition used to patch the compact subgroup: local Iwasawa compactness at
every place and, at each infinite place, also the Levi-compatible conditions. -/
def IsLeviCompatibleLocalCompact :
    ∀ v : Place F, Subgroup (PlaceGroupPoints F G v) → Prop
  | .inl w, L => InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G P p M l w L
  | .inr v, L => CoordinateCompactPatching.IsLocalIwasawaCompact
      (P.affinePointsTarget p (placeCompletion F (.inr v))) L

theorem IsLeviCompatibleLocalCompact.isLocalIwasawaCompact {v : Place F}
    {L : Subgroup (PlaceGroupPoints F G v)}
    (h : IsLeviCompatibleLocalCompact F G P p M l v L) :
    CoordinateCompactPatching.IsLocalIwasawaCompact
      (P.affinePointsTarget p (placeCompletion F v)) L := by
  rcases v with w | v
  · exact ⟨h.1, h.2.1⟩
  · exact h

/-- Adelic Iwasawa assembly in which the archimedean members of the compact family are
Levi-compatible Iwasawa compacts. The resulting subgroup is the actual coordinate subgroup
of the patched local family. -/
theorem exists_leviCompatible_parabolicIwasawaCompact
    [IsAffine G.X.left] [IsAffine P.X.left]
    (harch : ∀ w : InfinitePlace F, ∃ L : Subgroup (InfinitePlaceGroupPoints F G w),
      InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G P p M l w L)
    (hfinite : ∀ v : FinitePlace F, ∃ L : Subgroup (FinitePlaceGroupPoints F G v),
      CoordinateCompactPatching.IsLocalIwasawaCompact
        (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) L)
    (K₀ : ∀ v : FinitePlace F, Subgroup (FinitePlaceGroupPoints F G v))
    (hK₀ : IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p K₀) :
    ∃ Kloc : ∀ v : Place F, Subgroup (PlaceGroupPoints F G v),
      (∀ w : InfinitePlace F,
        InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G P p M l w (Kloc (.inl w))) ∧
      IsParabolicIwasawaCompact F G P p
        (CoordinateCompactAssembly.coordinateSubgroup
          (fun v => (atPlace F G v).toMonoidHom) Kloc) := by
  obtain ⟨hlocalK, habsorb, hintegral⟩ := hK₀
  have hint : IsUniformlyIntegral F G (extendFinite F G K₀) := hintegral
  let good := IsLeviCompatibleLocalCompact F G P p M l
  have hex : ∀ v, ∃ L, good v L := by
    rintro (w | v)
    · exact harch w
    · exact hfinite v
  let Kloc := CoordinateCompactPatching.patchFamily good hex (extendFinite F G K₀)
  have hK (v : Place F) : good v (Kloc v) :=
    CoordinateCompactPatching.good_patchFamily good hex _ v
  have hKeq : ∀ᶠ v in cofinite, Kloc v = extendFinite F G K₀ v :=
    CoordinateCompactPatching.patchFamily_eventually_eq good hex _
      (eventually_place_of_finite F
        (hlocalK.mono fun v hv => ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩))
  have hgood (a : AdelicGroupPoints F G) : ∀ᶠ v in cofinite, atPlace F G v a ∈ Kloc v := by
    filter_upwards [hKeq, eventually_atPlace_mem_of_finite F G
      (K := extendFinite F G K₀) habsorb a] with v heq hv
    rwa [heq]
  refine ⟨Kloc, fun w => hK (.inl w), ?_, ?_⟩
  · exact CoordinateCompactAssembly.compact_maximal_coordinateSubgroup
      (hint.of_eventuallyEq hKeq).compactProductLift (fun _ _ h => ext_atPlace F G h)
      (fun v => (atPlace F G v).continuous)
      (fun v => ((hK v).isLocalIwasawaCompact F G P p M l).1.1)
      (fun v => ((hK v).isLocalIwasawaCompact F G P p M l).1.2)
  · exact CoordinateCompactAssembly.range_mul_coordinateSubgroup_eq_univ
      (map F P G p : AdelicGroupPoints F P →* AdelicGroupPoints F G)
      (fun v => (atPlace F P v : AdelicGroupPoints F P →* PlaceGroupPoints F P v))
      (fun v => P.affinePointsTarget p (placeCompletion F v))
      (fun v b => atPlace_map F P p v b) hgood
      (fun q hq => exists_atPlace_eq_of_eventually_one F P q hq)
      (fun v => ((hK v).isLocalIwasawaCompact F G P p M l).2)

end Local

/-- Archimedean Levi-compatible Iwasawa existence, finite-place Iwasawa existence and the
almost-everywhere integral Iwasawa family give a compatible maximal compact subgroup for
every actual algebraic Siegel setup. -/
theorem adelicCompatibleIwasawaCompactStatement_of_local
    (harch : InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement.{u})
    (hfinite : FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u})
    (hintegral : IntegralIwasawaFamily.ExistenceStatement.{u}) :
    AdelicCompatibleIwasawaCompactStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS
  have hp : IsParabolicSubgroup (Standard.parabolicHom i ν ∅) := hS.2.2.1.isParabolicSubgroup
  have hl : IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) := hS.2.2.2.1
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion (Standard.parabolicHom i ν ∅).hom.hom.left :=
    hp.isClosedSubgroup
  have : IsAffine (Standard.parabolicScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.parabolicHom i ν ∅).hom.hom.left
  obtain ⟨K₀, hK₀⟩ := hintegral F G hG _ _ hp
  obtain ⟨Kloc, hKarch, hK⟩ := exists_leviCompatible_parabolicIwasawaCompact F G
    (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
    (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅)
    (harch F G hG _ _ hp _ _ hl) (hfinite F G hG _ _ hp) K₀ hK₀
  exact ⟨_, hK, isPositiveTorusCompatible_coordinateSubgroup F G T i ν T₀ j hS Kloc hKarch⟩

end Langlands.Global.AdelicSiegelFactors
