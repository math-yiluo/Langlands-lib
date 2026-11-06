import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Reparametrizing the Levi source of an arbitrary parabolic

A rational Levi `l : M ⟶ P` can be replaced by `e.hom ≫ l` for an isomorphism of group
schemes `e : M' ≅ M`, and its split component `a : A ⟶ M` by `a ≫ e.inv`. The Levi image
in `G(k)`, the composite `a ≫ l ≫ p` and the radical are unchanged, so the normalized
Jacquet exponents and the root presentations, with their cones, are unchanged. Together
with the published inner-conjugation invariance this moves an exponent along a parabolic
whose Levi is conjugate to `M` to a parabolic whose Levi source is `M` itself.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {L L' U P : GroupScheme S}

/-- The multiplication morphism of a reparametrized Levi factors through the
reparametrization of the first factor. -/
theorem subgroupMultiplication_iso_comp (e : L' ≅ L) (l : L ⟶ P) (r : U ⟶ P) :
    subgroupMultiplication (e.hom ≫ l) r =
      (e.hom.hom.hom ▷ U.X) ≫ subgroupMultiplication l r := by
  simp only [subgroupMultiplication, Grp.comp_hom_hom, MonObj.comp_mul, whiskerRight_fst_assoc,
    whiskerRight_snd_assoc]

/-- The multiplication morphism stays an isomorphism after reparametrizing the Levi. -/
theorem isIso_subgroupMultiplication_iso_comp (e : L' ≅ L) {l : L ⟶ P} {r : U ⟶ P}
    (hmul : IsIso (subgroupMultiplication l r)) :
    IsIso (subgroupMultiplication (e.hom ≫ l) r) := by
  have : IsIso e.hom.hom.hom := (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
  rw [subgroupMultiplication_iso_comp]
  infer_instance

end Scheme

variable {k : Type u} [Field k] {L L' P : GroupScheme (Spec (CommRingCat.of k))}

/-- Precomposing a rational Levi with an isomorphism of group schemes gives a rational Levi,
with the same unipotent radical. -/
theorem IsRationalLeviSubgroup.iso_comp {l : L ⟶ P} (hl : IsRationalLeviSubgroup l)
    (e : L' ≅ L) : IsRationalLeviSubgroup (e.hom ≫ l) := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  exact ⟨hl.isAffineHom, IsClosedSubgroup.iso_comp e hl.isClosedSubgroup,
    IsConnectedReductive.of_iso e hl.isConnectedReductive, U, r, hr,
    isIso_subgroupMultiplication_iso_comp e hmul⟩

namespace ParabolicRootPresentation

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {G M M' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The same presentation data present the parabolic with its Levi source reparametrized by
`e : M' ≅ M` and its split component `a ≫ e.inv`. -/
def leviIsoComp (r : ParabolicRootPresentation p l a) (e : M' ≅ M) :
    ParabolicRootPresentation p (e.hom ≫ l) (a ≫ e.inv) where
  data := r.data
  isCompatible := by
    have hrange : SubgroupFunctor.range ((e.hom ≫ l) ≫ p) = SubgroupFunctor.range (l ≫ p) := by
      rw [Category.assoc]
      exact SubgroupFunctor.range_iso_comp e (l ≫ p)
    obtain ⟨ζ, hζ, hP, hM⟩ := r.isCompatible.realization
    exact {
      parabolic := r.isCompatible.parabolic
      levi := r.isCompatible.levi.iso_comp e
      splitComponent := r.isCompatible.splitComponent.comp_iso e.symm
      maximalSplit := r.isCompatible.maximalSplit
      generic := r.isCompatible.generic
      subset_simpleRoots := r.isCompatible.subset_simpleRoots
      parabolic_eq := r.isCompatible.parabolic_eq
      levi_eq := hrange.trans r.isCompatible.levi_eq
      factor_comp := by
        rw [r.isCompatible.factor_comp]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      minimal := r.isCompatible.minimal
      minimal_le := r.isCompatible.minimal_le
      realization := ⟨ζ, hζ, hP, hrange.trans hM⟩ }

@[simp] theorem leviIsoComp_data (r : ParabolicRootPresentation p l a) (e : M' ≅ M) :
    (r.leviIsoComp e).data = r.data := rfl

theorem restrictedRoots_leviIsoComp (r : ParabolicRootPresentation p l a) (e : M' ≅ M) :
    (r.leviIsoComp e).restrictedRoots = r.restrictedRoots := rfl

variable [LocallyOfFiniteType G.X.hom]

/-- Reparametrizing the Levi source retains the positive root-combination cone. -/
theorem positiveCone_leviIsoComp (r : ParabolicRootPresentation p l a) (e : M' ≅ M) :
    (r.leviIsoComp e).positiveCone = r.positiveCone := rfl

/-- Reparametrizing the Levi source retains the nonnegative root-combination cone. -/
theorem nonnegCone_leviIsoComp (r : ParabolicRootPresentation p l a) (e : M' ≅ M) :
    (r.leviIsoComp e).nonnegCone = r.nonnegCone := rfl

end ParabolicRootPresentation

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G H H' P M M' U : GroupScheme (Spec (CommRingCat.of k))}

private theorem rationalPoints_map_comp_apply' {K : GroupScheme (Spec (CommRingCat.of k))}
    (f : H' ⟶ H) (g : H ⟶ K) (x : rationalPoints H') :
    rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

/-- Precomposing with an isomorphism does not change the literal point image. -/
theorem pointImage_iso_comp (e : H' ≅ H) (j : H ⟶ G) :
    pointImage (e.hom ≫ j) = pointImage j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨rationalPoints.map e.hom y, (rationalPoints_map_comp_apply' e.hom j y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨rationalPoints.map e.inv y, ?_⟩
    change rationalPoints.map (e.hom ≫ j) (rationalPoints.map e.inv y) = rationalPoints.map j y
    rw [← rationalPoints_map_comp_apply', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]

local instance leviReparametrizationAmbientPointTopology :
    TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Reparametrizing the Levi source by `e : M' ≅ M`, with split component `a ≫ e.inv`,
preserves every actual normalized Jacquet exponent. The parabolic, radical, character
and representation are retained. -/
theorem isNormalizedJacquetExponent_iso_comp_iff (e : M' ≅ M)
    (hl' : IsRationalLeviSubgroup (e.hom ≫ l))
    (hmul' : IsIso (subgroupMultiplication (e.hom ≫ l) r))
    (ha : IsSplitComponent a) (ha' : IsSplitComponent (a ≫ e.inv))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p (e.hom ≫ l) r hp hl' hr hmul' ha' π χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ := by
  let := RationalPointFamily.splitComponentPointTopology ha
  have eL : pointImage ((e.hom ≫ l) ≫ p) = pointImage (l ≫ p) := by
    simpa only [Category.assoc] using pointImage_iso_comp e (l ≫ p)
  refine normalizedGeneralizedWeight_congr
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p (e.hom ≫ l) r hr)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) π _ _
    (splitComponentPointsMap_mem_center ((e.hom ≫ l) ≫ p) ha')
    (splitComponentPointsMap_mem_center (l ≫ p) ha) rfl eL ?_ χ
  refine MonoidHom.ext fun t => Subtype.ext ?_
  change rationalPoints.map ((e.hom ≫ l) ≫ p) (rationalPoints.map (a ≫ e.inv) t) =
    rationalPoints.map (l ≫ p) (rationalPoints.map a t)
  rw [← rationalPoints_map_comp_apply', ← rationalPoints_map_comp_apply']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Inner conjugation of the ambient inclusion by `g` combined with reparametrization of the
Levi source by `e : M' ≅ M` preserves every actual normalized Jacquet exponent. -/
theorem isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff (g : rationalPoints G)
    (e : M' ≅ M) (hp' : IsParabolicSubgroup (p ≫ (G.innerIso g).hom))
    (hl' : IsRationalLeviSubgroup (e.hom ≫ l))
    (hmul' : IsIso (subgroupMultiplication (e.hom ≫ l) r))
    (ha : IsSplitComponent a) (ha' : IsSplitComponent (a ≫ e.inv))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r hp' hl' hr hmul' ha'
        π χ ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ :=
  (isNormalizedJacquetExponent_iso_comp_iff (p ≫ (G.innerIso g).hom) l r hp' hl hr hmul e
    hl' hmul' ha ha' π χ).trans
    (isNormalizedJacquetExponent_comp_innerIso_iff p l r hp hl hr hmul ha g π χ)

end Langlands.Aubert.General.RepresentedParabolic
