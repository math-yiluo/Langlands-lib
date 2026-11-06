import Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingStatement
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.GroupScheme.Rational.ParabolicLeviStandardConjugation
import Langlands.GroupScheme.Rational.ReductiveParabolicContraction
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Comparing represented and standard cuspidality

An internal comparison retaining the explicit parabolic and split-torus
conjugacy inputs. This does not prove existence of a cuspidal splitting.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RationalPointFamily

section Algebraic

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}

private theorem isIso_of_range_eq_top (p : P ⟶ G)
    (hp : IsClosedSubgroup p) (h : SubgroupFunctor.range p = ⊤) : IsIso p := by
  let : IsClosedImmersion p.hom.hom.left := hp
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, h⟩
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro Q
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨x, Category.comp_id x⟩
  let e := hrep.isoOfIsRepresentedBy hid
  have he : e.hom = p := by
    simpa using hrep.isoOfIsRepresentedBy_hom_comp hid
  rw [← he]
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)]

private theorem exists_rootSet_eq {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ I : Finset (SimpleRoot i ν), rootSet i ν I = J := by
  classical
  refine ⟨Finset.univ.filter (fun α => α.val ∈ J), ?_⟩
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact (Finset.mem_filter.mp hβ).2
  · intro hα
    exact ⟨⟨α, hJ hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩

/-- An actual proper parabolic's supplied geometric radical is conjugate,
on rational points, to the unipotent subgroup of an actual proper standard face. -/
structure ProperParabolicUnipotentStandardization
    {P U : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G) (r : U ⟶ P) where
  face : Finset (SimpleRoot i ν)
  proper : face ≠ Finset.univ
  conjugatingPoint : rationalPoints G
  radicalPoints : ∀ x : rationalPoints G, x ∈ unipotent i ν face ↔
    conjugatingPoint⁻¹ * x * conjugatingPoint ∈ pointImage (r ≫ p)

/-- Standardization retains the original chosen radical, rather than selecting
a replacement radical or assuming a point-image compatibility. -/
def properParabolicUnipotentStandardization [Mono i.hom.hom.left]
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hproper : ¬ IsIso p) :
    ProperParabolicUnipotentStandardization i ν p r := by
  classical
  apply Classical.choice
  let g := parabolicLeviStandardConjugatingPoint hPD
    dynamicGeometricUnipotentRadical hconj hG hi hRoots hν p l hp hl
  obtain ⟨J, ζ, hζ, hP, _, hPdyn, _⟩ := g.property
  obtain ⟨I, hI⟩ := exists_rootSet_eq i ν hζ.1
  have hcmp :=
    (hRoots.standardCocharacterDynamicComparison i ν J hi.isSplitSubtorus.1 hν
      (relativeRootSignsDetermineDynamic k G hG T i hi)).standard_eq_dynamic i ν J hζ
  have hIproper : I ≠ Finset.univ := by
    intro hfull
    have hJ : J = simpleRelativeRoots i ν := by
      rw [← hI, hfull, rootSet_univ]
    have hcmp0 :=
      (hRoots.standardCocharacterDynamicComparison i ν _ hi.isSplitSubtorus.1 hν
        (relativeRootSignsDetermineDynamic k G hG T i hi)).standard_eq_dynamic
        i ν _ (isStandardCocharacter_simple_zero i ν)
    have htop : standardParabolic i ν J = ⊤ := by
      rw [hJ, hcmp0.1, groupHom_zero_comp_eq_trivialCocharacter,
        Dynamic.parabolic_trivialCocharacter]
    have hp' := hp.comp_iso (G.innerIso g.val)
    have hiso := isIso_of_range_eq_top (p ≫ (G.innerIso g.val).hom)
      hp'.isClosedSubgroup (hP.trans htop)
    let := hiso
    have hcancel : IsIso p := by
      have heq : p = (p ≫ (G.innerIso g.val).hom) ≫ (G.innerIso g.val).inv := by simp
      rw [heq]
      infer_instance
    exact hproper hcancel
  have hp' := hp.comp_iso (G.innerIso g.val)
  let : IsClosedImmersion (p ≫ (G.innerIso g.val).hom).hom.hom.left :=
    hp'.isClosedSubgroup
  have hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (p ≫ (G.innerIso g.val).hom) := ⟨Over.mono_of_mono_left _, hPdyn⟩
  have hrad := Dynamic.range_comp_radical_eq_unipotent_of_reductive
    hG (CommGroupScheme.groupHom ζ ≫ i) (p ≫ (G.innerIso g.val).hom) hrep r hr.1
  have hpoints : pointImage (r ≫ p ≫ (G.innerIso g.val).hom) = unipotent i ν I := by
    change (SubgroupFunctor.range (r ≫ p ≫ (G.innerIso g.val).hom)).carrier
      (Over.mk (𝟙 _)) = (standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _))
    rw [hrad, hI, hcmp.2.2]
  have hconjU : ∀ x : rationalPoints G, x ∈ unipotent i ν I ↔
      g.val⁻¹ * x * g.val ∈ pointImage (r ≫ p) := by
    intro x
    rw [← hpoints]
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (r ≫ p) g.val x
  exact ⟨⟨I, hIproper, g.val, hconjU⟩⟩

end Algebraic

section Topology

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)]

local instance : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Proper-standard vanishing implies all-actual vanishing, retaining only
parabolic recognition, maximal split-torus conjugacy and the actual root
system as structural inputs. The chosen Levi and radical are preserved. -/
theorem isSupercuspidal_of_isCuspidal
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (h : ∀ I, IsSemidirectDecomposition
      (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hA : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A) :
    IsSupercuspidal A := by
  intro P M U p l r hp hl hr hmul hproper
  let s := properParabolicUnipotentStandardization i ν hPD hconj hG hi hν hRoots
    p l r hp hl hr hproper
  have hvanish := hA ⟨s.face, s.proper⟩
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation
    (unipotent i ν s.face) 1) at hvanish
  change Subsingleton (Jacquet.Localization.Coinvariants A.representation
    (pointImage (r ≫ p)) 1)
  let := hvanish
  exact (coinvariantsTranslateEquiv s.conjugatingPoint s.radicalPoints A.representation).injective.subsingleton

/-- Standard and all-represented cuspidality agree for the actual standard
family, under the explicit structural recognition and conjugacy inputs. -/
theorem isSupercuspidal_iff_isCuspidal
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    IsSupercuspidal A ↔
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
        hU A := by
  constructor
  · exact isCuspidal_of_all_represented_parabolics i ν hPD hStandard hG hi hν hRoots hU A
  · exact isSupercuspidal_of_isCuspidal i ν hPD hconj hG hi hν hRoots _ hU A

end Topology

end Langlands.Aubert.General.RepresentedParabolic
