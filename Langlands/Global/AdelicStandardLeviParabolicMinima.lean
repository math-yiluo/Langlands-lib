import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction

/-! # Intrinsic standard-parabolic height minima in the first canonical Levi -/

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

local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- The preceding rational intersections formed from the actual standard
parabolics of the first canonical Levi, indexed by the ambient intersections.
No root validity or nesting is needed to define the family. -/
def standardLeviParabolicTailPrefixRationalSubgroup
    (K : ℕ → Set (characterLattice T)) (l : ℕ) :
    Subgroup (RationalGroupPoints F (Standard.leviScheme i ν (K 0))) :=
  let iL := standardLeviTorusFactor i ν (K 0)
    (Standard.isRepresentedBy_leviHom i ν (K 0))
  closedPrefixRationalSubgroup F (Standard.leviScheme i ν (K 0))
    (fun a => Standard.parabolicScheme iL ν (K 0 ∩ K (a + 1)))
    (fun a => Standard.parabolicHom iL ν (K 0 ∩ K (a + 1))) l

omit [NumberField F] in
/-- On the actual rational-point test, the intrinsic preceding standard
parabolic intersections of the first Levi are exactly the ambient tail
intersections pulled back to that Levi. -/
theorem standardLeviParabolicTailPrefixRationalSubgroup_eq_tail
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν) (l : ℕ) :
    standardLeviParabolicTailPrefixRationalSubgroup F G T i ν K l =
      standardLeviTailPrefixRationalSubgroup F G T i ν K l := by
  let iL := standardLeviTorusFactor i ν (K 0)
    (Standard.isRepresentedBy_leviHom i ν (K 0))
  have he (a : ℕ) :
      closedChainRationalSubgroup F (Standard.leviScheme i ν (K 0))
        (fun b => Standard.parabolicScheme iL ν (K 0 ∩ K (b + 1)))
        (fun b => Standard.parabolicHom iL ν (K 0 ∩ K (b + 1))) a =
      ((standardParabolic i ν (K (a + 1))).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))).comap
          ((Standard.leviScheme i ν (K 0)).affinePointsTarget
            (Standard.leviHom i ν (K 0)) (CommAlgCat.of F F)) := by
    unfold closedChainRationalSubgroup
    rw [(Standard.isRepresentedBy_parabolicHom iL ν (K 0 ∩ K (a + 1))).2]
    have hP := (standardLeviStandardFamilies_inter_canonical i ν hG hi hν
      (K 0) (K (a + 1)) (hK 0) (hK (a + 1))).1
    change standardParabolic iL ν (K 0 ∩ K (a + 1)) = _ at hP
    rw [hP]
    rfl
  change (⨅ a, ⨅ (_ : a < l),
    closedChainRationalSubgroup F (Standard.leviScheme i ν (K 0))
      (fun b => Standard.parabolicScheme iL ν (K 0 ∩ K (b + 1)))
      (fun b => Standard.parabolicHom iL ν (K 0 ∩ K (b + 1))) a) = _
  simp only [he, standardLeviTailPrefixRationalSubgroup]

/-- Rewrite the transferred height minima as the identical preceding-intersection
construction for the actual standard parabolics inside the smaller Levi. -/
theorem mem_chainHeightMinimalSet_standardLevi_parabolicTail
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
    let iL := standardLeviTorusFactor i ν (K 0)
      (Standard.isRepresentedBy_leviHom i ν (K 0))
    m ∈ chainHeightMinimalSet F (Standard.leviScheme i ν (K 0)) s
      (fun a => d (a + 1))
      (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
      (fun a => Pi.single (j (a + 1)) 1)
      (closedPrefixRationalSubgroup F (Standard.leviScheme i ν (K 0))
        (fun a => Standard.parabolicScheme iL ν (K 0 ∩ K (a + 1)))
        (fun a => Standard.parabolicHom iL ν (K 0 ∩ K (a + 1)))) c := by
  have htail := mem_chainHeightMinimalSet_standardLevi_tail F G T i ν
    hG hi hν K hK s d ρ j hline c m x p hp hmin
  have he :
      standardLeviParabolicTailPrefixRationalSubgroup F G T i ν K =
        standardLeviTailPrefixRationalSubgroup F G T i ν K :=
    funext (standardLeviParabolicTailPrefixRationalSubgroup_eq_tail
      F G T i ν hG hi hν K hK)
  rw [← he] at htail
  exact htail

/-- Exact all-test adapted stabilizers and height minima both pass to the
intrinsic standard-parabolic family in the first canonical Levi. -/
theorem standardLevi_parabolicTail_exactStabilizers_and_minima
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hstab : ∀ a (Q : Over (Spec (CommRingCat.of F))) (y : Q ⟶ G.X),
      y ∈ (standardParabolic i ν (K a)).carrier Q ↔
        ∃ b : Γ(Q.left, ⊤)ˣ,
          ((ρ a).pointMatrix Q y : Matrix (Fin (d a)) (Fin (d a)) Γ(Q.left, ⊤)) *ᵥ
            Pi.single (j a) 1 =
              (b : Γ(Q.left, ⊤)) • (Pi.single (j a) 1 : Fin (d a) → Γ(Q.left, ⊤)))
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
    let iL := standardLeviTorusFactor i ν (K 0)
      (Standard.isRepresentedBy_leviHom i ν (K 0))
    (∀ a (Q : Over (Spec (CommRingCat.of F))) (y : Q ⟶ (Standard.leviScheme i ν (K 0)).X),
      y ∈ (standardParabolic iL ν (K 0 ∩ K (a + 1))).carrier Q ↔
        ∃ b : Γ(Q.left, ⊤)ˣ,
          (((ρ (a + 1)).restrict (Standard.leviHom i ν (K 0))).pointMatrix Q y :
            Matrix (Fin (d (a + 1))) (Fin (d (a + 1))) Γ(Q.left, ⊤)) *ᵥ
              Pi.single (j (a + 1)) 1 =
                (b : Γ(Q.left, ⊤)) •
                  (Pi.single (j (a + 1)) 1 : Fin (d (a + 1)) → Γ(Q.left, ⊤))) ∧
      m ∈ chainHeightMinimalSet F (Standard.leviScheme i ν (K 0)) s
        (fun a => d (a + 1))
        (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
        (fun a => Pi.single (j (a + 1)) 1)
        (closedPrefixRationalSubgroup F (Standard.leviScheme i ν (K 0))
          (fun a => Standard.parabolicScheme iL ν (K 0 ∩ K (a + 1)))
          (fun a => Standard.parabolicHom iL ν (K 0 ∩ K (a + 1)))) c := by
  refine ⟨?_, ?_⟩
  · intro a
    exact standardLevi_inter_coordinateLine_stabilizer i ν hG hi hν
      (K 0) (K (a + 1)) (hK 0) (hK (a + 1))
      (ρ (a + 1)) (j (a + 1)) (hstab (a + 1))
  · apply mem_chainHeightMinimalSet_standardLevi_parabolicTail F G T i ν
      hG hi hν K hK s d ρ j ?_ c m x p hp hmin
    intro a Q y
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstab a Q (y ≫ (Standard.parabolicHom i ν (K a)).hom.hom)).1 (by
        rw [← (Standard.isRepresentedBy_parabolicHom i ν (K a)).2]
        exact ⟨y, rfl⟩)

end Langlands.Global.RepresentationGrowth
