import Langlands.Algebra.NumberFieldReducedNormLocalityProof
import Langlands.GroupScheme.Rational.NumberFieldTypeE6HasseReduction
import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesInjectivity
import Langlands.GroupScheme.CocycleKernelTwist
import Langlands.GroupScheme.Rational.FiniteSeparableQuotientLifts
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Torus.FieldCocycleDescent

/-! # Reduction of totally complex type E6 vanishing through a type A5 Levi -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]

/-- A simply connected group over a totally complex number field has trivial local
classes at every place, on the full pullback of a finite field cover. -/
theorem Cocycle.locallyTrivial_of_totallyComplex {L : Type u} [Field L] [Algebra F L]
    [FiniteDimensional F L] {G : GroupScheme (Spec (CommRingCat.of F))}
    (hF : NumberField.IsTotallyComplex F) (hsc : IsSimplyConnected G)
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : ξ.LocallyTrivial := by
  let ζ : Cocycle G (GaloisCocycle.cover F L) := Cocycle.coboundary 1
  have hζ : ζ.IsTrivial := ⟨1, fun _ _ => rfl⟩
  have h := simplyConnectedRealToAllPlacesComparison F G hsc L ζ ξ
    (fun w hw => ((NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hF.isComplex w)) hw).elim)
  intro v
  exact Cocycle.IsTrivial.of_cohomologous (h v) (hζ.baseChange _ _ _)

/-- The type A Hasse kernels give vanishing over totally complex fields by local
triviality. The inner case uses reduced-norm locality. -/
private theorem isTrivial_typeA_of_outerHasse
    (houter : NumberFieldOuterTypeAHasseStatement.{u})
    {H : GroupScheme (Spec (CommRingCat.of F))}
    (hF : NumberField.IsTotallyComplex F) (hsc : IsSimplyConnected H)
    (habs : IsAbsolutelyAlmostSimple H)
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (d : TitsIndexData H) {n : ℕ} (hn : 0 < n) (e : d.Vertex ≃ Fin n)
    (hCartan : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle H (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  have hlocal := ξ.locallyTrivial_of_totallyComplex hF hsc
  by_cases hstar : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
      d.star σ a = a
  · exact numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality
      Langlands.CentralSimple.numberFieldReducedNormLocality F H d n hsc habs
      ⟨hn, ⟨e, hCartan⟩, hstar⟩ L ξ hlocal
  · push Not at hstar
    exact houter F H d n e hsc habs hCartan hstar L ξ hlocal

section Quotient

variable {C D Q : GroupScheme (Spec (CommRingCat.of F))}
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_galois_quotient_cochain_lift (q : C ⟶ Q)
    [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    (f : GaloisCocycle.cover F L ⟶ Q.X) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : Algebra L M)
      (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
      (g : GaloisCocycle.cover F M ⟶ C.X),
      g ≫ q.hom.hom = GaloisCocycle.coverMap F L M ≫ f := by
  let V : Over (Spec (CommRingCat.of L)) := Over.mk (pullback.snd q.hom.hom.left f.left)
  have : Smooth V.hom := inferInstanceAs (Smooth (pullback.snd q.hom.hom.left f.left))
  have : Surjective V.hom := inferInstanceAs (Surjective (pullback.snd q.hom.hom.left f.left))
  have : Nonempty V.left := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨z, _⟩ := (inferInstance : Surjective V.hom).surj x
    exact ⟨z⟩
  obtain ⟨E, _, _, hEL, _, ⟨w⟩⟩ :=
    Langlands.AlgebraicGeometry.exists_finiteSeparable_point_of_smooth V
  let : Algebra F E := Algebra.compHom E (algebraMap F L)
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L E := hEL
  let : FiniteDimensional F E := FiniteDimensional.trans F L E
  obtain ⟨M, hMF, hMgal, ⟨φ⟩⟩ := exists_finite_galois_algHom F E
  let ψ := φ.comp (IsScalarTower.toAlgHom F L E)
  let : Algebra L M := ψ.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  let r := GaloisCocycle.coverMap F L M
  let t : (GaloisCocycle.cover F M).left ⟶ Spec (CommRingCat.of E) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  let w₀ : Spec (CommRingCat.of E) ⟶ pullback q.hom.hom.left f.left := w.left
  have hw : w₀ ≫ pullback.snd q.hom.hom.left f.left = algebraBaseMap L E :=
    Over.w w
  have hr : t ≫ algebraBaseMap L E = r.left := by
    simp only [t, algebraBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let g₀ := t ≫ w₀ ≫ pullback.fst q.hom.hom.left f.left
  have hcomp : g₀ ≫ q.hom.hom.left = r.left ≫ f.left := by
    calc
      _ = t ≫ w₀ ≫ (pullback.fst q.hom.hom.left f.left ≫ q.hom.hom.left) := by
        simp only [g₀, Category.assoc]
      _ = (t ≫ (w₀ ≫ pullback.snd q.hom.hom.left f.left)) ≫ f.left := by
        rw [pullback.condition]
        simp only [Category.assoc]
      _ = _ := by rw [hw, hr]
  let g : GaloisCocycle.cover F M ⟶ C.X := Over.homMk g₀ (by
    rw [← Over.w q.hom.hom, ← Category.assoc, hcomp, Category.assoc, Over.w f, Over.w r])
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, hMF, hMgal, g, ?_⟩
  exact Over.OverMorphism.ext hcomp

variable [IsGalois F L]

set_option backward.isDefEq.respectTransparency false in
private theorem isTrivial_of_split_torus_quotient [IsAffineHom C.X.hom]
    (i : D ⟶ C) (hi : IsClosedSubgroup i)
    (q : C ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : Smooth D.X.hom) (hQ : IsSplitTorus Q)
    (hvanish : ∀ (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
      (τ : Cocycle D (GaloisCocycle.cover F M)), τ.IsTrivial)
    (ξ : Cocycle C (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  have hFppqc := fieldExtension_fpqc F L
  let : IsAffineHom (GaloisCocycle.cover F L).hom :=
    inferInstanceAs (IsAffineHom (algebraBaseMap F L))
  let : Flat (GaloisCocycle.cover F L).hom := hFppqc.2.1
  let : Surjective (GaloisCocycle.cover F L).hom := hFppqc.1
  obtain ⟨f, hf⟩ := Cocycle.isTrivial_of_isSplitTorus_overField hQ (ξ.map q)
  let : Mono i.hom.hom.left := hi.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hi' : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsAffine Q.X.left := SplittingAssembly.isAffine_of_isTorus Q hQ.isTorus
  let : QuasiCompact q.hom.hom.left := inferInstance
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hi' hD
  let : Surjective q.hom.hom.left := hq.2.1
  obtain ⟨M, _, _, _, _, _, _, g, hg⟩ := exists_galois_quotient_cochain_lift q f
  let r := GaloisCocycle.coverMap F L M
  have hgf {T : Over (Spec (CommRingCat.of F))} (a b : T ⟶ GaloisCocycle.cover F M) :
      ((ξ.refine r).map q).toFun a b =
        (Cocycle.coboundary (g ≫ q.hom.hom)).toFun a b := by
    rw [hg]
    simpa only [Cocycle.map, Cocycle.refine_toFun, Cocycle.coboundary, Category.assoc, r] using
      hf (a ≫ r) (b ≫ r)
  let τ := Cocycle.kernelTwist (ξ.refine r) q g hgf
  let e := hq.kernelIso hi'
  have hτ : τ.IsTrivial :=
    Cocycle.IsTrivial.of_map_retract e.inv e.hom e.inv_hom_id (hvanish M (τ.map e.inv))
  let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  exact GaloisCocycle.isTrivial_of_refine F L M ξ
    (Cocycle.isTrivial_of_kernelTwist (ξ.refine r) q g hgf hτ)

end Quotient

/-- A cocycle carried by the centralizer of a split line, with an actual derived
subgroup of type A5 and a represented split torus quotient. -/
structure TypeE6SplitLeviCocycleFactorization
    {G : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    (ξ : Cocycle G U) where
  line : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
  line_closed : IsClosedSubgroup line
  centralizer : GroupScheme (Spec (CommRingCat.of F))
  inclusion : centralizer ⟶ G
  centralizer_closed : IsClosedSubgroup inclusion
  represents : (torusCentralizer line).IsRepresentedBy inclusion
  derivedGroup : GroupScheme (Spec (CommRingCat.of F))
  derivedInclusion : derivedGroup ⟶ centralizer
  isDerived : IsDerivedSubgroup derivedInclusion
  simplyConnected : IsSimplyConnected derivedGroup
  absolutelyAlmostSimple : IsAbsolutelyAlmostSimple derivedGroup
  [isAffine : IsAffineHom derivedGroup.X.hom]
  [locallyFiniteType : LocallyOfFiniteType derivedGroup.X.hom]
  index : TitsIndexData derivedGroup
  numbering : index.Vertex ≃ Fin 5
  cartan_eq : ∀ a b, index.cartan a b = CartanMatrix.A 5 (numbering a) (numbering b)
  quotient : GroupScheme (Spec (CommRingCat.of F))
  quotientMap : centralizer ⟶ quotient
  quotient_split : IsSplitTorus quotient
  isQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range derivedInclusion) quotientMap
  cochain : U ⟶ G.X
  cocycle : Cocycle centralizer U
  factorization : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ U),
    (cocycle.map inclusion).toFun a b = (ξ.twist cochain).toFun a b

attribute [instance] TypeE6SplitLeviCocycleFactorization.isAffine
  TypeE6SplitLeviCocycleFactorization.locallyFiniteType

/-- The geometric reduction of type E6 cocycles to a split-line centralizer
with simply connected derived group of type A5. The factorization may be
exhibited on a finite Galois refinement of the original cover. -/
def NumberFieldTotallyComplexTypeE6LeviFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], NumberField.IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)),
        ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : Algebra L M)
          (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M),
          Nonempty (TypeE6SplitLeviCocycleFactorization
            (ξ.refine (GaloisCocycle.coverMap F L M)))

set_option backward.isDefEq.respectTransparency false in
/-- The type A5 Levi factorization and the outer type A Hasse kernel imply
totally complex vanishing for all simply connected groups of type E6. -/
theorem numberFieldTotallyComplexTypeE6Vanishing_of_leviFactorization
    (hlevi : NumberFieldTotallyComplexTypeE6LeviFactorizationStatement.{u})
    (houter : NumberFieldOuterTypeAHasseStatement.{u}) :
    NumberFieldTotallyComplexTypeE6VanishingStatement.{u} := by
  intro F _ _ hF G _ _ d e hsc habs hCartan L _ _ _ _ ξ
  obtain ⟨M, _, _, _, _, _, _, ⟨p⟩⟩ := hlevi F hF G d e hsc habs hCartan L ξ
  let : IsAffineHom p.centralizer.X.hom := p.centralizer_closed.isAffineHom
  have h := isTrivial_of_split_torus_quotient p.derivedInclusion p.isDerived.1
    p.quotientMap p.isQuotient p.simplyConnected.isSemisimple.isConnectedReductive.smooth
    p.quotient_split (fun _ _ _ _ _ τ =>
      isTrivial_typeA_of_outerHasse houter hF p.simplyConnected p.absolutelyAlmostSimple
        p.index (by decide) p.numbering p.cartan_eq τ) p.cocycle
  have htwist := (h.map p.inclusion).of_cohomologous
    (Cocycle.cohomologous_of_toFun_eq fun a b => p.factorization a b)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  exact GaloisCocycle.isTrivial_of_refine F L M ξ htwist.of_twist

end Langlands.GroupScheme
