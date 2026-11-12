import Langlands.Global.AdelicHeightMinimumLeviRestriction
import Langlands.Global.AdelicIntersectionHeightChain
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction

/-! # Height minima on the canonical standard Levi after dropping the first line -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

omit [NumberField F] in
/-- The canonical representative of any valid standard unipotent subgroup is
unipotent, using a standard cocharacter and the dynamic unipotence theorem. -/
theorem isUnipotent_standardUnipotentScheme
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsUnipotent (Standard.unipotentScheme i ν J) := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  have hU := Standard.isRepresentedBy_unipotentHom i ν J
  rw [(heq ζ hζ).2.2] at hU
  exact Dynamic.isUnipotent_unipotentRepresentative
    (CommGroupScheme.groupHom ζ ≫ i) hU

/-- The actual adelic image of each canonical standard Levi normalizes the
actual adelic image of its standard unipotent subgroup, for every index set. -/
theorem standardLevi_adelic_range_le_normalizer
    (J : Set (characterLattice T)) :
    (map F (Standard.leviScheme i ν J) G (Standard.leviHom i ν J)).toMonoidHom.range ≤
      Subgroup.normalizer
        ((map F (Standard.unipotentScheme i ν J) G
          (Standard.unipotentHom i ν J)).toMonoidHom.range :
            Set (AdelicGroupPoints F G)) := by
  let Q := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  have hL :
      (map F (Standard.leviScheme i ν J) G (Standard.leviHom i ν J)).toMonoidHom.range =
        (standardLevi i ν J).carrier Q :=
    congrArg (fun S : SubgroupFunctor G => S.carrier Q)
      (Standard.isRepresentedBy_leviHom i ν J).2
  have hU :
      (map F (Standard.unipotentScheme i ν J) G
        (Standard.unipotentHom i ν J)).toMonoidHom.range =
        (standardUnipotent i ν J).carrier Q :=
    congrArg (fun S : SubgroupFunctor G => S.carrier Q)
      (Standard.isRepresentedBy_unipotentHom i ν J).2
  rw [hL, hU]
  have key : ∀ p ∈ (standardLevi i ν J).carrier Q,
      ∀ x ∈ (standardUnipotent i ν J).carrier Q,
        p * x * p⁻¹ ∈ (standardUnipotent i ν J).carrier Q := by
    intro p hp x hx
    exact StandardLeviIntersection.conj_mem_standardUnipotent i ν
      (standardLevi_le_standardParabolic i ν J Q hp) hx
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key p hp x
  · intro hx
    have h := key p⁻¹ (inv_mem hp) _ hx
    simpa [mul_assoc] using h

omit [NumberField F] in
/-- Every standard unipotent subgroup lies in every standard parabolic for
valid subsets of the fixed simple roots. -/
theorem standardUnipotent_le_other_standardParabolic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν) :
    standardUnipotent i ν J ≤ standardParabolic i ν K := by
  have hO := (standardParabolicOrder F G hG T i hi ν hν).1
  have hU := ((hO ∅ J (Set.empty_subset _) hJ).2 (Set.empty_subset J)).2
  have hP := (hO ∅ K (Set.empty_subset _) hK).1.mp (Set.empty_subset K)
  exact hU.trans ((standardUnipotent_le_standardParabolic i ν ∅).trans hP)

omit [NumberField F] in
/-- All-test preservation by a standard parabolic passes to every valid
canonical standard unipotent subgroup. -/
theorem preservesCoordinateLine_standardUnipotent_of_standardParabolic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν K)).PreservesCoordinateLine j) :
    (ρ.restrict (Standard.unipotentHom i ν J)).PreservesCoordinateLine j := by
  intro Q x
  have hx : x ≫ (Standard.unipotentHom i ν J).hom.hom ∈
      (standardUnipotent i ν J).carrier Q := by
    rw [← (Standard.isRepresentedBy_unipotentHom i ν J).2]
    exact ⟨x, rfl⟩
  have hp := standardUnipotent_le_other_standardParabolic F G T i ν hG hi hν
    J K hJ hK Q hx
  rw [← (Standard.isRepresentedBy_parabolicHom i ν K).2] at hp
  obtain ⟨y, hy⟩ := hp
  change y ≫ (Standard.parabolicHom i ν K).hom.hom =
    x ≫ (Standard.unipotentHom i ν J).hom.hom at hy
  simpa only [MatrixRepresentation.pointMatrix_restrict, hy] using hline Q y

/-- In the first canonical Levi, intersect the pullbacks of the next `l`
individual parabolics. The first ambient stabilizer is omitted. -/
def standardLeviTailPrefixRationalSubgroup
    (K : ℕ → Set (characterLattice T)) (l : ℕ) :
    Subgroup (RationalGroupPoints F (Standard.leviScheme i ν (K 0))) :=
  ⨅ a, ⨅ (_ : a < l),
    ((standardParabolic i ν (K (a + 1))).carrier
      ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))).comap
        ((Standard.leviScheme i ν (K 0)).affinePointsTarget
          (Standard.leviHom i ν (K 0)) (CommAlgCat.of F F))

omit [NumberField F] in
@[simp] theorem mem_standardLeviTailPrefixRationalSubgroup
    (K : ℕ → Set (characterLattice T)) (l : ℕ)
    (q : RationalGroupPoints F (Standard.leviScheme i ν (K 0))) :
    q ∈ standardLeviTailPrefixRationalSubgroup F G T i ν K l ↔
      ∀ a, a < l →
        (Standard.leviScheme i ν (K 0)).affinePointsTarget
          (Standard.leviHom i ν (K 0)) (CommAlgCat.of F F) q ∈
            (standardParabolic i ν (K (a + 1))).carrier
              ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := by
  simp only [standardLeviTailPrefixRationalSubgroup, Subgroup.mem_iInf,
    Subgroup.mem_comap]

omit [NumberField F] in
@[simp] theorem standardLeviTailPrefixRationalSubgroup_zero
    (K : ℕ → Set (characterLattice T)) :
    standardLeviTailPrefixRationalSubgroup F G T i ν K 0 = ⊤ := by
  ext q
  simp

omit [NumberField F] in
/-- The tail intersections descend without nesting the individual parabolics. -/
theorem standardLeviTailPrefixRationalSubgroup_antitone
    (K : ℕ → Set (characterLattice T)) :
    Antitone (standardLeviTailPrefixRationalSubgroup F G T i ν K) := by
  intro a b hab q hq
  exact (mem_standardLeviTailPrefixRationalSubgroup F G T i ν K a q).2
    (fun k hk => (mem_standardLeviTailPrefixRationalSubgroup F G T i ν K b q).1 hq k
      (lt_of_lt_of_le hk hab))

omit [NumberField F] in
/-- Pulling the ambient prefix through the first Levi inclusion removes its
automatic first parabolic condition and leaves exactly the tail prefix. -/
theorem standardLeviTailPrefixRationalSubgroup_eq_comap
    (K : ℕ → Set (characterLattice T)) (l : ℕ) :
    standardLeviTailPrefixRationalSubgroup F G T i ν K l =
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a)) (l + 1)).comap
          ((Standard.leviScheme i ν (K 0)).affinePointsTarget
            (Standard.leviHom i ν (K 0)) (CommAlgCat.of F F)) := by
  ext q
  have he (a : ℕ) :
      closedChainRationalSubgroup F G
          (fun b => Standard.parabolicScheme i ν (K b))
          (fun b => Standard.parabolicHom i ν (K b)) a =
        (standardParabolic i ν (K a)).carrier
          ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) :=
    congrArg (fun S : SubgroupFunctor G =>
      S.carrier ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))))
      (Standard.isRepresentedBy_parabolicHom i ν (K a)).2
  simp only [mem_standardLeviTailPrefixRationalSubgroup, Subgroup.mem_comap,
    mem_closedPrefixRationalSubgroup, he]
  constructor
  · intro h a ha
    cases a with
    | zero =>
      apply standardLevi_le_standardParabolic i ν (K 0)
      rw [← (Standard.isRepresentedBy_leviHom i ν (K 0)).2]
      exact ⟨q, rfl⟩
    | succ a => exact h a (Nat.lt_of_succ_lt_succ ha)
  · intro h a ha
    exact h (a + 1) (Nat.succ_lt_succ ha)

/-- Given an actual factorization into a separately norm-one first Levi point
and a canonical unipotent point, the remaining minimum inequalities hold in
that Levi over exactly the preceding tail intersections, with the same constant. -/
theorem mem_chainHeightMinimalSet_standardLevi_tail
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hline : ∀ a, ((ρ a).restrict (Standard.parabolicHom i ν (K a))).PreservesCoordinateLine
      (j a))
    (c : ℝ) (m : normOneSubgroup F (Standard.leviScheme i ν (K 0)))
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν (K 0)))
    (p : normOneSubgroup F G)
    (hp : (p : AdelicGroupPoints F G) =
      map F (Standard.leviScheme i ν (K 0)) G (Standard.leviHom i ν (K 0)) m *
        map F (Standard.unipotentScheme i ν (K 0)) G
          (Standard.unipotentHom i ν (K 0)) x)
    (hmin : p ∈ chainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1)
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a))) c) :
    m ∈ chainHeightMinimalSet F (Standard.leviScheme i ν (K 0)) s
      (fun a => d (a + 1))
      (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
      (fun a => Pi.single (j (a + 1)) 1)
      (standardLeviTailPrefixRationalSubgroup F G T i ν K) c := by
  refine mem_chainHeightMinimalSet_restrict_of_unipotent_factor F G
    (Standard.leviScheme i ν (K 0)) (Standard.leviHom i ν (K 0))
    (Standard.unipotentScheme i ν (K 0)) (Standard.unipotentHom i ν (K 0))
    (isUnipotent_standardUnipotentScheme F G T i ν hG hi hν (K 0) (hK 0))
    (s + 1) s d ρ j
    (closedPrefixRationalSubgroup F G
      (fun a => Standard.parabolicScheme i ν (K a))
      (fun a => Standard.parabolicHom i ν (K a)))
    (standardLeviTailPrefixRationalSubgroup F G T i ν K)
    (fun a => a + 1) (fun _ ha => Nat.succ_lt_succ ha) ?_ ?_
    (standardLevi_adelic_range_le_normalizer F G T i ν (K 0)) c m x p hp hmin
  · intro a _
    exact preservesCoordinateLine_standardUnipotent_of_standardParabolic F G T i ν
      hG hi hν (K 0) (K (a + 1)) (hK 0) (hK (a + 1))
      (ρ (a + 1)) (j (a + 1)) (hline (a + 1))
  · intro a _ q
    exact (standardLeviTailPrefixRationalSubgroup_eq_comap F G T i ν K a).le q.property

end Langlands.Global.RepresentationGrowth
