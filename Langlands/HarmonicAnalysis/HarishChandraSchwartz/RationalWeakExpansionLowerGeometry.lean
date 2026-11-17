import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionWeyl
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.Representation.Plancherel.DynamicOppositeStandardIntertwining

/-! # The actual lower semistandard geometry of the weak expansion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz.WeakExpansion

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I I' : Set (characterLattice T))

/-- The actual torus cocharacter translated by a chosen normalizer representative. -/
def conjugatedCocharacter (ζ : cocharacterLattice T) (n : normalizerPoints i) :
    cocharacterLattice T :=
  cocharacterAut (normalizingAut i n) ζ

/-- The conjugated cocharacter, inside the actual lower Levi scheme. -/
def lowerCocharacter (ζ : cocharacterLattice T) (n : normalizerPoints i) :
    (Gm (Spec (CommRingCat.of F))).toGrp ⟶ lowerAmbient i ν I' :=
  CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
    Standard.leviTorusHom i ν I'

/-- Inclusion in G recovers the conjugated ambient cocharacter. -/
theorem lowerCocharacter_comp (ζ : cocharacterLattice T) (n : normalizerPoints i) :
    lowerCocharacter i ν I' ζ n ≫ Standard.leviHom i ν I' =
      (CommGroupScheme.groupHom ζ ≫ i) ≫ (G.innerIso (n : rationalPoints G)).hom := by
  rw [lowerCocharacter, Category.assoc, Standard.leviTorusHom_comp,
    conjugatedCocharacter, groupHom_cocharacterAut_comp]

/-- The dynamic subgroups of the translated torus cocharacter are the forward
conjugates of the original standard subgroups, on every test scheme. -/
theorem conjugatedCocharacter_dynamic (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i) :
    Dynamic.parabolic (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) =
        conjugatedParabolic i ν I n ∧
    Dynamic.centralizer (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) =
        conjugatedLevi i ν I n ∧
    Dynamic.unipotent (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) =
        conjugatedUnipotent i ν I n := by
  obtain ⟨hP, hL, hU⟩ := (standardCocharacter F G hG T i hi ν hν I hI).2 ζ hζ
  have hc : (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i) ≫
      (G.innerIso (n : rationalPoints G)).inv = CommGroupScheme.groupHom ζ ≫ i := by
    rw [conjugatedCocharacter, groupHom_cocharacterAut_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨?_, ?_, ?_⟩
  · rw [Dynamic.parabolic_eq_comap_of_iso _ (G.innerIso (n : rationalPoints G)).symm,
      Iso.symm_hom, hc, ← hP]
    rfl
  · rw [Dynamic.centralizer_eq_comap_of_iso _ (G.innerIso (n : rationalPoints G)).symm,
      Iso.symm_hom, hc, ← hL]
    rfl
  · rw [Dynamic.unipotent_eq_comap_of_iso _ (G.innerIso (n : rationalPoints G)).symm,
      Iso.symm_hom, hc, ← hU]
    rfl

/-- The lower dynamic subgroups are exactly the three previously defined
intersection functors inside M', without standardizing the lower parabolic. -/
theorem lowerCocharacter_dynamic (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i) :
    Dynamic.parabolic (lowerCocharacter i ν I' ζ n) = lowerParabolic i ν I I' n ∧
    Dynamic.centralizer (lowerCocharacter i ν I' ζ n) = lowerLevi i ν I I' n ∧
    Dynamic.unipotent (lowerCocharacter i ν I' ζ n) = lowerUnipotent i ν I I' n := by
  have h := conjugatedCocharacter_dynamic i ν I hG hi hν hI ζ hζ n
  have hc : lowerCocharacter i ν I' ζ n ≫ Standard.leviHom i ν I' =
      CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i := by
    rw [lowerCocharacter, Category.assoc, Standard.leviTorusHom_comp]
  refine ⟨?_, ?_, ?_⟩
  · rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ _
      (Standard.isClosedSubgroup_leviHom i ν I'), hc, h.1]
    rfl
  · rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup _ _
      (Standard.isClosedSubgroup_leviHom i ν I'), hc, h.2.1]
    rfl
  · rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup _ _
      (Standard.isClosedSubgroup_leviHom i ν I'), hc, h.2.2]
    rfl

/-- The literal groups used by the dynamic coefficient and packet API are the
actual lower intersection groups, with no additional model transport. -/
theorem lowerCocharacter_points (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i) :
    Langlands.Plancherel.DynamicOppositeStandardIntertwining.parabolic
        (lowerCocharacter i ν I' ζ n) = (lowerParabolic i ν I I' n).rationalPoints ∧
    Langlands.Plancherel.DynamicOppositeStandardIntertwining.levi
        (lowerCocharacter i ν I' ζ n) = (lowerLevi i ν I I' n).rationalPoints := by
  have h := lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n
  exact ⟨congrArg SubgroupFunctor.rationalPoints h.1,
    congrArg SubgroupFunctor.rationalPoints h.2.1⟩

local instance lowerIsAffineHom : IsAffineHom (lowerAmbient i ν I').X.hom :=
  leviScheme_isAffineHom i ν I'
local instance lowerIsAffine : IsAffine (lowerAmbient i ν I').X.left :=
  isAffine_of_isAffineHom (lowerAmbient i ν I').X.hom

/-- Closed affine representatives, compatible inclusions and a Levi decomposition
of the actual lower intersection functors on every test scheme. -/
def lowerDecompositionModel (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i) :
    SubgroupFunctor.ClosedDecompositionModel
      (lowerParabolic i ν I I' n) (lowerLevi i ν I I' n) (lowerUnipotent i ν I I' n) :=
  let h := lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n
  (Dynamic.affineDecompositionModel (lowerCocharacter i ν I' ζ n)).reindex
    h.1 h.2.1 h.2.2

/-- The actual lower triple is semistandard in M': it contains the fixed torus
and is a parabolic with its connected reductive Levi and geometric radical. -/
def lowerSemistandardIndex (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (hI' : I' ⊆ simpleRelativeRoots i ν)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν I ζ)
    (n : normalizerPoints i) : SemistandardSpectralIndex (Standard.leviTorusHom i ν I') where
  parabolic := lowerParabolic i ν I I' n
  levi := lowerLevi i ν I I' n
  radical := lowerUnipotent i ν I I' n
  torus_le_levi := by
    have h := lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n
    rw [← h.2.1]
    exact (range_le_torusCentralizer (Standard.leviTorusHom i ν I')).trans
      (torusCentralizer_le_dynamicCentralizer _
        (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n)))
  isParabolicWithLeviAndRadical := by
    have h := lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n
    rw [← h.1, ← h.2.1, ← h.2.2]
    exact (SemistandardSpectralIndex.ofCocharacter
      (i := Standard.leviTorusHom i ν I')
      (Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive
        hG i hi ν hν I' hI') (conjugatedCocharacter i ζ n)).isParabolicWithLeviAndRadical

section Points

variable [TopologicalSpace F] [IsTopologicalRing F] [LocallyOfFiniteType G.X.hom]

local instance ambientIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance ambientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance lowerTopology : TopologicalSpace (rationalPoints (lowerAmbient i ν I')) :=
  rationalPointTopology F (lowerAmbient i ν I').X

/-- Forward conjugation identifies the original inducing Levi with the literal
dynamic Levi in the actual lower ambient group, with their inherited topologies. -/
def lowerLeviConjugation (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I') :
    standardLeviPoints i ν I ≃ₜ*
      (Dynamic.centralizer (lowerCocharacter i ν I' ζ n)).rationalPoints := by
  let e := standardLeviRationalPointsHomeomorph i ν I' (Standard.leviHom i ν I')
    (Standard.isRepresentedBy_leviHom i ν I') (Standard.isClosedSubgroup_leviHom i ν I')
  let c := rationalPointsConjHomeomorph G (n : rationalPoints G)
  have hesym (x : standardLeviPoints i ν I') :
      rationalPoints.map (Standard.leviHom i ν I') (e.symm x) = x :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hmem (m : standardLeviPoints i ν I) :
      c m ∈ (conjugatedLevi i ν I n).rationalPoints := by
    rw [conjugatedLevi_points]
    exact Subgroup.mem_map.mpr ⟨m, m.property, rfl⟩
  let f (m : standardLeviPoints i ν I) : rationalPoints (lowerAmbient i ν I') :=
    e.symm ⟨c m, hn _ (hmem m)⟩
  have hf (m : standardLeviPoints i ν I) :
      rationalPoints.map (Standard.leviHom i ν I') (f m) = c m := hesym _
  have hfmem (m : standardLeviPoints i ν I) :
      f m ∈ (Dynamic.centralizer (lowerCocharacter i ν I' ζ n)).rationalPoints := by
    rw [(lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n).2.1]
    change rationalPoints.map (Standard.leviHom i ν I') (f m) ∈
      (conjugatedLevi i ν I n).rationalPoints
    rw [hf]
    exact hmem m
  let g (m : (Dynamic.centralizer (lowerCocharacter i ν I' ζ n)).rationalPoints) :
      standardLeviPoints i ν I :=
    ⟨c.symm (rationalPoints.map (Standard.leviHom i ν I') m), by
      have hm : (m : rationalPoints (lowerAmbient i ν I')) ∈
          (lowerLevi i ν I I' n).rationalPoints :=
        Eq.mp (congrArg
          (fun L : SubgroupFunctor (lowerAmbient i ν I') =>
            (m : rationalPoints (lowerAmbient i ν I')) ∈ L.rationalPoints)
          (lowerCocharacter_dynamic i ν I I' hG hi hν hI ζ hζ n).2.1) m.property
      change rationalPoints.map (Standard.leviHom i ν I') m ∈
        ((standardLevi i ν I).comap (G.innerIso (n : rationalPoints G)).inv).rationalPoints
        at hm
      rw [SubgroupFunctor.rationalPoints_comap, rationalPoints_map_innerIso_inv] at hm
      change (n : rationalPoints G)⁻¹ *
        rationalPoints.map (Standard.leviHom i ν I') m * n ∈ standardLeviPoints i ν I
      simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv] using hm⟩
  refine
    { toFun m := ⟨f m, hfmem m⟩
      invFun := g
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro m
    apply Subtype.ext
    change c.symm (rationalPoints.map (Standard.leviHom i ν I') (f m)) = m
    rw [hf, c.symm_apply_apply]
  · intro m
    apply Subtype.ext
    apply (standardLeviRationalPointsEquiv i ν I' (Standard.leviHom i ν I')
      (Standard.isRepresentedBy_leviHom i ν I')).injective
    apply Subtype.ext
    change rationalPoints.map (Standard.leviHom i ν I') (f (g m)) =
      rationalPoints.map (Standard.leviHom i ν I') m
    rw [hf]
    exact c.apply_symm_apply _
  · intro a b
    apply Subtype.ext
    apply (standardLeviRationalPointsEquiv i ν I' (Standard.leviHom i ν I')
      (Standard.isRepresentedBy_leviHom i ν I')).injective
    apply Subtype.ext
    change rationalPoints.map (Standard.leviHom i ν I') (f (a * b)) =
      rationalPoints.map (Standard.leviHom i ν I') (f a * f b)
    rw [map_mul, hf, hf, hf]
    exact map_mul c _ _
  · exact (e.symm.continuous.comp
      ((c.continuous.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact (c.symm.continuous.comp
      ((continuous_subtype_val.comp e.continuous).comp continuous_subtype_val)).subtype_mk _

@[simp]
theorem map_lowerLeviConjugation (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I')
    (m : standardLeviPoints i ν I) :
    rationalPoints.map (Standard.leviHom i ν I')
        (lowerLeviConjugation i ν I I' hG hi hν hI ζ hζ n hn m) =
      (n : rationalPoints G) * (m : rationalPoints G) * (n : rationalPoints G)⁻¹ := by
  let e := standardLeviRationalPointsHomeomorph i ν I' (Standard.leviHom i ν I')
    (Standard.isRepresentedBy_leviHom i ν I') (Standard.isClosedSubgroup_leviHom i ν I')
  change rationalPoints.map (Standard.leviHom i ν I') (e.symm _) = _
  exact congrArg Subtype.val (e.apply_symm_apply _)

@[simp]
theorem lowerLeviConjugation_symm_coe (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hI : I ⊆ simpleRelativeRoots i ν) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν I ζ) (n : normalizerPoints i)
    (hn : conjugatedLevi i ν I n ≤ standardLevi i ν I')
    (m : (Dynamic.centralizer (lowerCocharacter i ν I' ζ n)).rationalPoints) :
    ((lowerLeviConjugation i ν I I' hG hi hν hI ζ hζ n hn).symm m :
        rationalPoints G) =
      (n : rationalPoints G)⁻¹ * rationalPoints.map (Standard.leviHom i ν I') m * n :=
  rfl

end Points

end Langlands.HarishChandraSchwartz.WeakExpansion
