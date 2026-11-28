import Langlands.Automorphic.GroupSchemeParabolicRadicals
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.Exponents.ArbitraryParabolicTemperedAmbientTransport
import Langlands.Representation.Aubert.General.Conjugation

/-! # Normalized induction from a conjugated represented parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Points

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The point image of a subgroup map conjugated by `g` after a change of source. -/
private theorem mem_pointImage_iso_comp_innerIso {H H' : GroupScheme (Spec (CommRingCat.of k))}
    (e : H' ≅ H) (j : H ⟶ G) (g x : rationalPoints G) :
    x ∈ pointImage (e.hom ≫ j ≫ (G.innerIso g).hom) ↔ g⁻¹ * x * g ∈ pointImage j := by
  rw [pointImage_iso_comp]
  exact mem_pointImage_comp_innerIso j g x

end Points

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M M' U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviInductionConjugationAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction from two represented parabolics `P` and `P'` is isomorphic as soon
as `P'` is the conjugate of `P` by `g` and the Levi embedding of `P'` is that of `P`
conjugated by `g`, after a change of Levi source `φ : M' ≅ M`. The inducing
representation is pulled back along the point map of `φ`. The case `g = 1`, `φ = 𝟙`
says that induction depends only on the range of the parabolic and the Levi embedding. -/
def leviInductionIsoOfConj {P' M' U' : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (p' : P' ⟶ G) (l' : M' ⟶ P') (r' : U' ⟶ P')
    (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (g : rationalPoints G) (φ : M' ≅ M)
    (hrange : SubgroupFunctor.range p' = SubgroupFunctor.range (p ≫ (G.innerIso g).hom))
    (hlevi : l' ≫ p' = φ.hom ≫ l ≫ p ≫ (G.innerIso g).hom) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := hl'.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    letI := leviPointTopology l' hl'
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (leviInductionFunctor p l r hp hr hl hmul).obj σ ≅
        (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj
          (SmoothRep.pullback (ambientIsoPointsEquiv φ) σ) := by
  haveI := hl.isConnectedReductive.isAffineHom
  haveI := hl'.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  letI := leviPointTopology l' hl'
  intro σ
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let h₂ := isSemidirectDecomposition_pointImage p' l' r' hp'.isClosedSubgroup hr' hmul'
  have hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hU₂ := isClosed_pointImage_comp p' r' hp'.isClosedSubgroup hr'.1.isClosedSubgroup
  have hPP' : ∀ x : rationalPoints G,
      x ∈ pointImage p' ↔ g⁻¹ * x * g ∈ pointImage p := by
    intro x
    rw [pointImage_eq_range_carrier p', hrange, ← pointImage_eq_range_carrier]
    exact mem_pointImage_comp_innerIso p g x
  have hMM' : ∀ x : rationalPoints G,
      x ∈ pointImage (l' ≫ p') ↔ g⁻¹ * x * g ∈ pointImage (l ≫ p) := by
    intro x
    rw [hlevi]
    simpa only [Category.assoc] using mem_pointImage_iso_comp_innerIso φ (l ≫ p) g x
  have hrad : SubgroupFunctor.range (r ≫ (p ≫ (G.innerIso g).hom)) =
      SubgroupFunctor.range (r' ≫ p') :=
    Automorphic.GroupSchemeFunctions.parabolicRadical_range_eq
      (hp.comp_iso (G.innerIso g)).isClosedSubgroup hp'.isClosedSubgroup hrange.symm
      hr.1 hr'.1
  have hUU' : ∀ x : rationalPoints G,
      x ∈ pointImage (r' ≫ p') ↔ g⁻¹ * x * g ∈ pointImage (r ≫ p) := by
    intro x
    rw [pointImage_eq_range_carrier (r' ≫ p'), ← hrad, ← pointImage_eq_range_carrier]
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (r ≫ p) g x
  refine inductionConjugationIsoApp h h₂ g hPP' hMM' hUU' hU hU₂
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ) ≪≫
    (normalizedInductionFunctor h₂ hU₂).mapIso
      (SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun x => ?_)))
  have hx : (leviPointsEquiv p l hp hl).symm (conjugationEquiv g hMM' x) =
      ambientIsoPointsEquiv φ ((leviPointsEquiv p' l' hp' hl').symm x) := by
    apply (leviPointsEquiv p l hp hl).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Subtype.ext
    obtain ⟨y, rfl⟩ := (leviPointsEquiv p' l' hp' hl').surjective x
    rw [ContinuousMulEquiv.symm_apply_apply, leviPointsEquiv_apply_coe, ambientIsoPointsEquiv_apply,
      ← pointMap_comp_apply]
    change g⁻¹ * rationalPoints.map (l' ≫ p') y * g = _
    rw [hlevi, ← Category.assoc φ.hom, ← Category.assoc (φ.hom ≫ l),
      pointMap_comp_apply, rationalPoints_map_innerIso]
    change g⁻¹ * (g * _ * g⁻¹) * g = _
    group
    rw [Category.assoc]
  ext v
  change σ.representation ((leviPointsEquiv p l hp hl).symm (conjugationEquiv g hMM' x)) v =
    σ.representation (ambientIsoPointsEquiv φ ((leviPointsEquiv p' l' hp' hl').symm x)) v
  rw [hx]

/-- Normalized induction from a represented parabolic is isomorphic to normalized
induction from its conjugate by `g`, with the Levi source changed by `e : M' ≅ M`
and the inducing representation pulled back along the point map of `e`. The map on
induced functions is `f ↦ f(g⁻¹ ·)` (published `inductionConjugationIsoApp`). -/
def leviInductionConjugateIso (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (g : rationalPoints G) (e : M' ≅ M) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := (hl.iso_comp e).isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    letI := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (leviInductionFunctor p l r hp hr hl hmul).obj σ ≅
        (leviInductionFunctor (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r (hp.comp_iso _) hr
          (hl.iso_comp e) (isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul)).obj
          (SmoothRep.pullback (ambientIsoPointsEquiv e) σ) :=
  leviInductionIsoOfConj p l r hp hl hr hmul
    (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r (hp.comp_iso _) (hl.iso_comp e) hr
    (isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul) g e rfl (by
      simp only [Category.assoc])

/-- Normalized induction depends only on the range of the parabolic and on the Levi
embedding: two actual parabolic data with the same range and the same Levi embedding of the
same `M` have isomorphic inductions. -/
def leviInductionIsoOfRangeEq {P' U' : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (p' : P' ⟶ G) (l' : M ⟶ P') (r' : U' ⟶ P')
    (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (hrange : SubgroupFunctor.range p' = SubgroupFunctor.range p) (hlevi : l' ≫ p' = l ≫ p) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (leviInductionFunctor p l r hp hr hl hmul).obj σ ≅
        (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ := by
  haveI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  intro σ
  refine leviInductionIsoOfConj p l r hp hl hr hmul p' l' r' hp' hl' hr' hmul' 1 (Iso.refl M)
    (by rw [innerIso_one_hom, Category.comp_id]; exact hrange)
    (by rw [innerIso_one_hom, Category.comp_id, Iso.refl_hom, Category.id_comp, hlevi]) σ ≪≫
    (leviInductionFunctor p' l' r' hp' hr' hl' hmul').mapIso
      (SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun m => ?_)))
  ext v
  change σ.representation (ambientIsoPointsEquiv (Iso.refl M) m) v = σ.representation m v
  congr 2

end Langlands.Aubert.General.RepresentedParabolic
