import Langlands.AlgebraicGeometry.SquareZeroLiftingSmooth
import Langlands.GroupScheme.Cohomology.SourceTransport
import Langlands.GroupScheme.HomScheme.NormalizerConjugation
import Langlands.GroupScheme.HomScheme.SquareZeroCohomologyStatement
import Langlands.GroupScheme.SplitExistence.OppositeFactorPairs
import Langlands.GroupScheme.Torus.MultiplicativeTypeNormalizerFinitePresentation
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry

/-! # Square-zero lifting for torus normalizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem evaluate_comp_hom {S : Scheme.{u}} {H G L : GroupScheme S}
    {U U₀ : Over S} (a : U₀ ⟶ U) (f : RelativeHom H G U) (g : RelativeHom G L U) :
    evaluate a (f ≫ g) = evaluate a f ≫ evaluate a g :=
  Descent.pullHom_comp a.left (Over.w a) (Over.w a) (Over.w a) f g

private theorem conjugateRelative_eq_of_comm {S : Scheme.{u}} {H : GroupScheme S}
    {A : CommGroupScheme S} {U : Over S} (f : RelativeHom H A.toGrp U)
    (g : U ⟶ A.toGrp.X) : conjugateRelative f g = f := by
  let A' := (CommGroupScheme.baseChange U.hom).obj A
  let p := RelativeLevi.pulledBackPoint A.toGrp U g
  exact (congrArg (f ≫ ·) (SplitExistence.innerIso_hom_eq_id_of_comm A' p)).trans
    (Category.comp_id f)

private theorem evaluate_bijective_of_conjugatorLifting_comm {S : Scheme.{u}}
    {H : GroupScheme S} {A : CommGroupScheme S} {U U₀ : Over S} (a : U₀ ⟶ U)
    (h : HasConjugatorLifting H A.toGrp a) :
    Function.Bijective (evaluate (H := H) (G := A.toGrp) a) := by
  refine ⟨fun f g hfg => ?_, h.1⟩
  obtain ⟨p, _, hp⟩ := h.2 f g 1 (by
    rw [conjugateRelative_eq_of_comm (A := A)]
    exact hfg.symm)
  exact (conjugateRelative_eq_of_comm (A := A) f p).symm.trans hp.symm

private theorem exists_lift_sourceIso {S : Scheme.{u}} {A : CommGroupScheme S}
    {U U₀ : Over S} (a : U₀ ⟶ U) (h : HasConjugatorLifting A.toGrp A.toGrp a)
    (e₀ : (baseChange U₀.hom).obj A.toGrp ≅ (baseChange U₀.hom).obj A.toGrp) :
    ∃ e : (baseChange U.hom).obj A.toGrp ≅ (baseChange U.hom).obj A.toGrp,
      evaluate a e.hom = e₀.hom := by
  have hbij := evaluate_bijective_of_conjugatorLifting_comm (A := A) a h
  obtain ⟨f, hf⟩ := hbij.surjective e₀.hom
  obtain ⟨g, hg⟩ := hbij.surjective e₀.inv
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }, hf⟩
  · apply hbij.injective
    rw [evaluate_comp_hom, hf, hg, Iso.hom_inv_id]
    exact (Descent.pullHom_id a.left U.hom U₀.hom (Over.w a) A.toGrp).symm
  · apply hbij.injective
    rw [evaluate_comp_hom, hg, hf, Iso.inv_hom_id]
    exact (Descent.pullHom_id a.left U.hom U₀.hom (Over.w a) A.toGrp).symm

open Langlands.AlgebraicGeometry in
/-- The square-zero cohomology bridge lifts points of the represented normalizer
of a closed split torus in a smooth ambient group. -/
theorem hasAffineSquareZeroLifting_of_splitTorusNormalizer
    (hdeform : SquareZeroHomomorphismCohomologyStatement.{u})
    {S : Scheme.{u}} {G N : GroupScheme S} [Smooth G.X.hom] {A : CommGroupScheme S}
    (t : A.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp) (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hn : (torusNormalizer t).IsRepresentedBy n) :
    HasAffineSquareZeroLifting N.X.hom := by
  intro C I hI x₀ y h
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let b := q ≫ y
  let U := Over.mk y
  let U₀ := Over.mk b
  let a : U₀ ⟶ U := Over.homMk q
  let x₀' : U₀ ⟶ N.X := Over.homMk x₀ h
  let g₀ := x₀' ≫ n.hom.hom
  have hg₀ : g₀ ∈ (torusNormalizer t).carrier U₀ := by
    rw [← hn.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x₀', rfl⟩
  let : IsClosedImmersion t.hom.hom.left := ht
  let e₀ := normalizerSourceIso t g₀ hg₀
  let hDiag := hA.isRelativeDiagonalizable
  let : IsAffineHom ((baseChange y).obj A.toGrp).X.hom := (hDiag.baseChange y).isAffineHom
  let hflat : Flat ((baseChange y).obj A.toGrp).X.hom := (hDiag.baseChange y).flat
  have haff : IsAffine ((baseChange y).obj A.toGrp).X.left :=
    isAffine_of_isAffineHom ((baseChange y).obj A.toGrp).X.hom
  have hcoh := Cohomology.hasVanishingLowDegreeCohomology_of_isDiagonalizable (hDiag.baseChange b)
  let : Smooth A.toGrp.X.hom := (RelativeTorus.IsTorus.of_isSplitTorus hA).smooth
  have hAA : HasConjugatorLifting A.toGrp A.toGrp a :=
    hdeform S A.toGrp A.toGrp C I hI y b rfl hflat haff hcoh
  have hAG : HasConjugatorLifting A.toGrp G a :=
    hdeform S A.toGrp G C I hI y b rfl hflat haff hcoh
  obtain ⟨e, he⟩ := exists_lift_sourceIso (A := A) a hAA e₀.1
  let f : RelativeHom A.toGrp G U := (baseChange U.hom).map t
  let f' : RelativeHom A.toGrp G U := e.hom ≫ f
  have hef : evaluate a f' = conjugateRelative (evaluate a f) g₀ := by
    simp only [f', f, evaluate_comp_hom, he, evaluate_baseChange]
    exact e₀.2.symm
  obtain ⟨g, hg, hfg⟩ := hAG.2 f f' g₀ hef
  have hgn : g ∈ (torusNormalizer t).carrier U :=
    (exists_sourceIso_conjugationFamily_iff t g).mp ⟨e, hfg.symm⟩
  rw [← hn.2] at hgn
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hgn
  let : Mono n.hom.hom := hn.1
  have hx₀ : a ≫ x = x₀' := by
    rw [← cancel_mono n.hom.hom, Category.assoc, hx, hg]
  exact ⟨x.left, Over.w x, congrArg (fun z => z.left) hx₀⟩

end Langlands.GroupScheme.HomScheme

namespace Langlands.GroupScheme

open HomScheme in
/-- A closed, locally finitely presented torus normalizer is smooth if the
square-zero cohomology bridge holds. -/
theorem relativeTorusNormalizer_smooth_of_squareZeroCohomology
    (hdeform : SquareZeroHomomorphismCohomologyStatement.{u})
    {S : Scheme.{u}} {G N : GroupScheme S} [Smooth G.X.hom]
    {A : CommGroupScheme S} (t : A.toGrp ⟶ G) (hA : RelativeTorus.IsTorus A.toGrp)
    (ht : IsClosedSubgroup t) (n : N ⟶ G)
    (hn : (torusNormalizer t).IsRepresentedBy n) [LocallyOfFinitePresentation N.X.hom] :
    Smooth N.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hA
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  let b := 𝒰.f k
  let B := baseChange b
  let : Smooth (B.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : LocallyOfFinitePresentation (B.obj N).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd N.X.hom b)
    infer_instance
  have hn' := hn.baseChange b
  rw [← torusNormalizer_baseChange] at hn'
  exact (hasAffineSquareZeroLifting_of_splitTorusNormalizer hdeform
    (A := (CommGroupScheme.baseChange b).obj A)
    (B.map t) (h𝒰 k) (ht.baseChange b) (B.map n) hn').smooth

/-- The actual closed torus normalizer equipped with smooth structure, using
the supplied square-zero cohomology bridge. -/
def relativeTorusSmoothNormalizerModel_of_squareZeroCohomology
    (hdeform : HomScheme.SquareZeroHomomorphismCohomologyStatement.{u})
    {S : Scheme.{u}} {G : GroupScheme S} [Smooth G.X.hom]
    {A : CommGroupScheme S} (t : A.toGrp ⟶ G) (hA : RelativeTorus.IsTorus A.toGrp)
    (ht : IsClosedSubgroup t) :
    {N : SubgroupFunctor.ClosedRepresentative (torusNormalizer t) // Smooth N.group.X.hom} := by
  let N := relativeTorusFinitelyPresentedNormalizerModel t hA ht
  let : LocallyOfFinitePresentation N.1.group.X.hom := N.2.2
  exact ⟨N.1, relativeTorusNormalizer_smooth_of_squareZeroCohomology hdeform
    t hA ht N.1.hom N.1.represents⟩

end Langlands.GroupScheme
