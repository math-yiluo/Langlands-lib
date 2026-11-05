import Langlands.Global.AdelicPositiveTorusCompatibilityStatement
import Langlands.Global.RealSplitTorusAdelicComparison

/-! # Adelic positive-torus compatibility from archimedean Levi intersections -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Every finite-place component of a point of the coordinate positive torus is one. -/
theorem atFinitePlace_full (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (v : Langlands.Global.FinitePlace F) (x : I → ℝ≥0ˣ) :
    atFinitePlace F T.toGrp v (full F I T e x) = 1 := by
  apply (coordinates F I T e (FiniteCompletion F v)).injective
  have h := coordinates_affineMap F T I e (adeleProjection F (.inr v)) (full F I T e x)
  change coordinates F I T e (FiniteCompletion F v)
    (atFinitePlace F T.toGrp v (full F I T e x)) = _ at h
  rw [h, coordinates_full]
  funext b
  calc
    Units.map (adeleProjection F (.inr v)).toMonoidHom
        (PositiveRealIdeles.full F (x b)) = 1 := by
      apply Units.ext
      rfl
    _ = coordinates F I T e (FiniteCompletion F v) 1 b :=
      (congrFun (coordinates F I T e (FiniteCompletion F v)).map_one b).symm

/-- The finite-place identity is intrinsic and includes split rank zero. -/
theorem atFinitePlace_intrinsic (hT : IsSplitTorus T.toGrp)
    (v : Langlands.Global.FinitePlace F) (a : intrinsicSubgroup F T) :
    atFinitePlace F T.toGrp v a.val = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  have ha : a.val ∈ subgroup F I T e := by
    rw [subgroup_eq_intrinsicSubgroup]
    exact a.property
  obtain ⟨x, hx⟩ := ha
  rw [← hx]
  exact atFinitePlace_full F T I e v x

end Langlands.Global.PositiveRealTorus

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

omit [IsAffineHom G.X.hom] in
/-- The actual positive image has trivial finite-place components for a split source. -/
theorem atFinitePlace_positiveMap (hT₀ : IsSplitTorus T₀.toGrp)
    (v : Langlands.Global.FinitePlace F) (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
    atFinitePlace F G v (positiveMap F G T i T₀ j a) = 1 := by
  change atPlace F G (.inr v)
    (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) a.val) = 1
  rw [atPlace_map]
  change GroupScheme.affinePointsTarget T₀.toGrp (CommGroupScheme.groupHom j ≫ i)
    (placeCompletion F (.inr v)) (atFinitePlace F T₀.toGrp v a.val) = 1
  rw [PositiveRealTorus.atFinitePlace_intrinsic F T₀ hT₀, map_one]

omit [NumberField F] in
/-- The standard Levi commutes with the actual torus image over every coefficient algebra
when its all-test subgroup functor is the torus centralizer. -/
theorem commute_of_mem_standardLevi_image
    (hlevi : standardLevi i ν ∅ = torusCentralizer i)
    (A : CommAlgCat.{u} (CommRingCat.of F)) (g : G.affinePoints A)
    (hg : g ∈ Set.range ((Standard.leviScheme i ν ∅).affinePointsTarget
      (Standard.leviHom i ν ∅) A)) (a : GroupScheme.affinePoints T₀.toGrp A) :
    Commute g (GroupScheme.affinePointsTarget T₀.toGrp
      (CommGroupScheme.groupHom j ≫ i) A a) := by
  have hg' : g ∈ (SubgroupFunctor.range (Standard.leviHom i ν ∅)).carrier
      ((algSpec (CommRingCat.of F)).obj (op A)) := hg
  rw [(Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi] at hg'
  have h := hg' _ (𝟙 _) (a ≫ (CommGroupScheme.groupHom j).hom.hom)
  simpa only [Category.id_comp, Category.assoc, GroupScheme.affinePointsTarget_apply,
    Grp.comp_hom_hom] using h

/-- Levi-compatible archimedean compact containment implies actual adelic
positive-torus compatibility. All local compacts and their properties are supplied. -/
theorem isPositiveTorusCompatible_of_leviCompatibleIwasawaCompacts
    (hT₀ : IsSplitTorus T₀.toGrp)
    (hlevi : standardLevi i ν ∅ = torusCentralizer i)
    (K : Subgroup (AdelicGroupPoints F G))
    (Karch : ∀ v : NumberField.InfinitePlace F,
      Subgroup (InfinitePlaceGroupPoints F G v))
    (hKarch : ∀ v, InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
      (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅) v (Karch v))
    (hprojection : ∀ v k, k ∈ K → atInfinitePlace F G v k ∈ Karch v) :
    IsPositiveTorusCompatible F G T i ν T₀ j K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro k hk hkP a
  change k * positiveMap F G T i T₀ j a = positiveMap F G T i T₀ j a * k
  apply ext_atPlace F G
  intro v
  rw [map_mul, map_mul]
  cases v with
  | inl v =>
      have hkP' : atInfinitePlace F G v k ∈
          Set.range ((Standard.parabolicScheme i ν ∅).affinePointsTarget
            (Standard.parabolicHom i ν ∅) (CommAlgCat.of F v.Completion)) := by
        obtain ⟨p, rfl⟩ := hkP
        exact ⟨atInfinitePlace F (Standard.parabolicScheme i ν ∅) v p,
          (atPlace_map F (Standard.parabolicScheme i ν ∅)
            (Standard.parabolicHom i ν ∅) (.inl v) p).symm⟩
      have hkm := (hKarch v).mem_levi F G hkP' (hprojection v k hk)
      rw [Standard.leviToParabolic_comp] at hkm
      have hcomm := commute_of_mem_standardLevi_image F G T i ν T₀ j hlevi
        (CommAlgCat.of F v.Completion) (atInfinitePlace F G v k) hkm
        (atInfinitePlace F T₀.toGrp v a.val)
      change atPlace F G (.inl v) k *
          atPlace F G (.inl v)
            (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) a.val) =
        atPlace F G (.inl v)
            (map F T₀.toGrp G (CommGroupScheme.groupHom j ≫ i) a.val) *
          atPlace F G (.inl v) k
      rw [atPlace_map]
      exact hcomm.eq
  | inr v =>
      have hfin : atPlace F G (.inr v) (positiveMap F G T i T₀ j a) = 1 :=
        atFinitePlace_positiveMap F G T i T₀ j hT₀ v a
      rw [hfin, mul_one, one_mul]

/-- An existing Siegel algebraic setup supplies the split source and
all-test Levi centralizer equality needed by the compatibility implication. -/
theorem isPositiveTorusCompatible_of_setup_leviCompatibleIwasawaCompacts
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (Karch : ∀ v : NumberField.InfinitePlace F,
      Subgroup (InfinitePlaceGroupPoints F G v))
    (hKarch : ∀ v, InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
      (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅) v (Karch v))
    (hprojection : ∀ v k, k ∈ K → atInfinitePlace F G v k ∈ Karch v) :
    IsPositiveTorusCompatible F G T i ν T₀ j K := by
  obtain ⟨_, _, _, _, _, hlevi, _, hderived, _⟩ := hsetup
  obtain ⟨D, d, t₀, _, ht₀, _⟩ := hderived
  exact isPositiveTorusCompatible_of_leviCompatibleIwasawaCompacts F G T i ν T₀ j
    ht₀.1.1 hlevi K Karch hKarch hprojection

/-- The actual coordinate subgroup has positive-torus compatibility when its
infinite-place subgroups are Levi-compatible for the canonical standard groups. -/
theorem isPositiveTorusCompatible_coordinateSubgroup
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (Kloc : ∀ v : Place F, Subgroup (PlaceGroupPoints F G v))
    (hKarch : ∀ v : NumberField.InfinitePlace F,
      InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G
        (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
        (Standard.leviScheme i ν ∅) (Standard.leviToParabolic i ν ∅) v (Kloc (.inl v))) :
    IsPositiveTorusCompatible F G T i ν T₀ j
      (CoordinateCompactAssembly.coordinateSubgroup
        (fun v => (atPlace F G v).toMonoidHom) Kloc) :=
  isPositiveTorusCompatible_of_setup_leviCompatibleIwasawaCompacts F G T i ν T₀ j
    hsetup _ (fun v => Kloc (.inl v)) hKarch (fun v _ hk => hk (.inl v))

/-- The exact universal compatibility target, with all local data and
projection-containment premises retained. -/
theorem adelicPositiveTorusCompatibility :
    AdelicPositiveTorusCompatibilityStatement.{u} := by
  intro F _ _ G T _ i ν T₀ j hT₀ hlevi K Karch hKarch hprojection
  exact isPositiveTorusCompatible_of_leviCompatibleIwasawaCompacts F G T i ν T₀ j
    hT₀ hlevi K Karch hKarch hprojection

end Langlands.Global.AdelicSiegelFactors
