import Langlands.GroupScheme.SmoothSubgroupCosetSpace
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedDenseAffineOpenReduction
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartClosedPointCoverage

/-! # Affine representation of the quotient by the actual reduced subgroup -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.ReducedCosetAffine

variable {k : Type u} [Field k] [PerfectField k]
  (N : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType N.X.hom]

abbrev inclusion : reducedSubgroup N ⟶ N := reducedSubgroupι N

local instance : Mono (inclusion N).hom.hom := Over.mono_of_mono_left _

abbrev quotient : Langlands.AlgebraicGeometry.AlgebraicSpace (Spec (CommRingCat.of k)) :=
  HomogeneousQuotientSheaf.space (inclusion N) inferInstance

abbrev projection : (schemeYoneda _).obj N.X ⟶ (quotient N).presheaf :=
  HomogeneousQuotientSheaf.projection (inclusion N)

/-- Every reduced test-scheme point maps to the neutral coset. -/
lemma projection_eq_one {T : Over (Spec (CommRingCat.of k))} [IsReduced T.left]
    (x : T ⟶ N.X) :
    (projection N).app (op T) ⟨x⟩ = (projection N).app (op T) ⟨(1 : T ⟶ N.X)⟩ := by
  apply (HomogeneousQuotientSheaf.projection_eq_iff (inclusion N) T x 1).mpr
  have hx : x ∈ (SubgroupFunctor.range (inclusion N)).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨ReducedSubgroup.liftOver x, ReducedSubgroup.liftOver_fac x⟩
  simpa using ((SubgroupFunctor.range (inclusion N)).carrier T).inv_mem hx

/-- The quotient has just its neutral section on every field test, because
the smooth pullback of the presentation is reduced. -/
lemma field_section_eq (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (z : (quotient N).sections (Over.mk b)) :
    z = (projection N).app (op (Over.mk b)) ⟨(1 : Over.mk b ⟶ N.X)⟩ := by
  let T : Over (Spec (CommRingCat.of k)) := Over.mk b
  let a := uliftYonedaEquiv.{u + 1}.symm z
  have hsm := HomogeneousQuotientSheaf.smooth_projection (inclusion N) (inferInstance)
  have hsurj := HomogeneousQuotientSheaf.surjective_projection (inclusion N) (inferInstance)
  let V := hsm.rep.pullback a
  let p : V ⟶ T := hsm.rep.snd a
  let v : V ⟶ N.X := hsm.rep.fst' a
  have hpb := hsm.rep.isPullback' a
  have : Smooth p.left := hsm.property_snd a
  have : Surjective p.left := hsurj.projection a (hsm.rep.fst a) p (hsm.rep.isPullback a)
  have : IsReduced V.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field K V.left p.left
  have hv : (projection N).app (op V) ⟨v⟩ = (quotient N).presheaf.map p.op z := by
    have he := congrArg (fun α => α.app (op V) ⟨𝟙 V⟩) hpb.w
    exact he
  have hloc : (quotient N).presheaf.map p.op z =
      (quotient N).presheaf.map p.op ((projection N).app (op T) ⟨(1 : T ⟶ N.X)⟩) := by
    rw [← hv, projection_eq_one]
    have he := congrArg (fun f => f (ULift.up (1 : T ⟶ N.X))) ((projection N).naturality p.op)
    simpa using he
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp (quotient N).toSheaf.property _
    (generate_singleton_mem_fppfTopology p)
  apply hsh.isSeparatedFor.ext
  rintro W f ⟨Z, g, _, ⟨⟩, rfl⟩
  change (quotient N).presheaf.map (g ≫ p).op z =
    (quotient N).presheaf.map (g ≫ p).op ((projection N).app (op T) ⟨(1 : T ⟶ N.X)⟩)
  simp only [op_comp, Functor.map_comp, types_comp_apply, hloc]

abbrev neutral : (quotient N).sections (𝟙_ (Over (Spec (CommRingCat.of k)))) :=
  (projection N).app (op (𝟙_ (Over (Spec (CommRingCat.of k)))))
    ⟨(1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ N.X)⟩

lemma map_neutral {T : Over (Spec (CommRingCat.of k))}
    (p : T ⟶ 𝟙_ (Over (Spec (CommRingCat.of k)))) :
    (quotient N).presheaf.map p.op (neutral N) =
      (projection N).app (op T) ⟨(1 : T ⟶ N.X)⟩ := by
  have he := congrArg (fun f => f (ULift.up
    (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ N.X))) ((projection N).naturality p.op)
  simpa [neutral] using he.symm

/-- Any representable open subfunctor with a point on a nonempty scheme is
the entire reduced-subgroup quotient. -/
lemma open_eq_top_of_nonempty (A : Subfunctor (quotient N).presheaf)
    (hA : IsOpenImmersion A.ι)
    {U : Over (Spec (CommRingCat.of k))} [Nonempty U.left]
    (x : (quotient N).sections U) (hx : x ∈ A.obj (op U)) : A = ⊤ := by
  let u : U.left := Classical.choice inferInstance
  let V := OpenSubfunctorPoints.residueFieldTest U u
  let p : V ⟶ 𝟙_ (Over (Spec (CommRingCat.of k))) := toUnit V
  have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Surjective p.left :=
    ⟨fun y => ⟨IsLocalRing.closedPoint (U.left.residueField u), Subsingleton.elim _ _⟩⟩
  have he : neutral N ∈ A.obj (op (𝟙_ (Over (Spec (CommRingCat.of k))))) := by
    apply OpenSubfunctorPoints.mem_of_surjective hA p
    rw [map_neutral]
    have hx' : (quotient N).presheaf.map
        (OpenSubfunctorPoints.residueFieldPoint U u).op x ∈ A.obj (op V) :=
      A.map (OpenSubfunctorPoints.residueFieldPoint U u).op hx
    have hz := field_section_eq N (U.left.residueField u) V.hom
      ((quotient N).presheaf.map (OpenSubfunctorPoints.residueFieldPoint U u).op x)
    rwa [hz] at hx'
  apply top_unique
  intro T z _
  apply OpenSubfunctorPoints.mem_of_field_tests hA z
  intro K _ f
  let W : Over (Spec (CommRingCat.of k)) := Over.mk (f ≫ T.unop.hom)
  let r : W ⟶ T.unop := Over.homMk f
  change (quotient N).presheaf.map r.op z ∈ A.obj (op W)
  rw [field_section_eq N K W.hom ((quotient N).presheaf.map r.op z)]
  change (projection N).app (op W) ⟨(1 : W ⟶ N.X)⟩ ∈ A.obj (op W)
  rw [← map_neutral N (toUnit W)]
  exact A.map (toUnit W).op he

/-- The quotient has an affine etale surjective presentation; any nonempty
affine open of an etale atlas already has full image. -/
lemma exists_affine_atlas :
    ∃ (U : Over (Spec (CommRingCat.of k)))
      (a : (schemeYoneda _).obj U ⟶ (quotient N).presheaf),
      IsAffine U.left ∧ LocallyOfFiniteType U.hom ∧ Nonempty U.left ∧
        IsEtale a ∧ IsSurjective a := by
  obtain ⟨_, _, _, _, _, W, aW, heW, hsW, hW⟩ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.smoothRelationQuotient _ N.X
      (HomogeneousQuotientFromEmbedding.arrowSpace (inclusion N))
      (HomogeneousQuotientFromEmbedding.source (inclusion N))
      (HomogeneousQuotientFromEmbedding.target (inclusion N))
      (HomogeneousQuotientFromEmbedding.isEquivalenceRelation (inclusion N))
      (HomogeneousQuotientFromEmbedding.hasSmoothProjections (inclusion N) inferInstance)
      inferInstance
  have : LocallyOfFiniteType W.hom := hW
  let g := uliftYonedaEquiv.{u + 1}.symm (neutral N)
  let P := heW.rep.pullback g
  let p := heW.rep.snd g
  have hp : Surjective p.left := hsW.projection g (heW.rep.fst g) p (heW.rep.isPullback g)
  obtain ⟨v, _⟩ := hp.surj (IsLocalRing.closedPoint k)
  let w : W.left := (heW.rep.fst' g).left v
  obtain ⟨U, hU, hwU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : W.left.Opens)) (show w ∈ (⊤ : W.left.Opens) from trivial)
  let V : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ W.hom)
  let j : V ⟶ W := Over.homMk U.ι
  have : IsAffine V.left := hU
  have : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ W.hom))
  have : Nonempty V.left := ⟨⟨w, hwU⟩⟩
  have : Etale j.left := inferInstanceAs (Etale U.ι)
  let a := (schemeYoneda _).map j ≫ aW
  have hea : IsEtale a := (isEtale_map j inferInstance).comp heW
  let A := (Subfunctor.range a).sheafify (fppfTopology _)
  have hA := OpenSubfunctorImages.sheafify_range_open a hea
  have htop : A = ⊤ := open_eq_top_of_nonempty N A hA (uliftYonedaEquiv a)
    (((Subfunctor.toRangeSheafify (fppfTopology _) a).app (op V) ⟨𝟙 V⟩).property)
  have : IsIso A.ι := (Subfunctor.eq_top_iff_isIso A).mp htop
  have hloc : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology _) a := by
    change CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology _)
      (Subfunctor.toRangeSheafify (fppfTopology _) a ≫ A.ι)
    infer_instance
  exact ⟨V, a, inferInstance, inferInstance, inferInstance, hea,
    OpenSubfunctorImages.isSurjective_of_isEtale_isLocallySurjective a hea hloc⟩

/-- A nonempty affine open is the whole quotient, so the actual quotient
is represented by an affine scheme. -/
lemma exists_affine_model :
    ∃ (V : Over (Spec (CommRingCat.of k))), IsAffine V.left ∧
      LocallyOfFiniteType V.hom ∧
      Nonempty ((schemeYoneda _).obj V ≅ (quotient N).presheaf) := by
  obtain ⟨U, a, hUa, hU, hUne, hea, hsa⟩ := exists_affine_atlas N
  have : IsAffine U.left := hUa
  have : Nonempty U.left := hUne
  have hd := HomogeneousQuotientSheaf.isClosedImmersion_diagonal (inclusion N)
    (inferInstance : Smooth (reducedSubgroup N).X.hom)
    (inferInstanceAs (IsClosedImmersion (inclusion N).hom.hom.left))
  have hS1 := Langlands.AlgebraicGeometry.AlgebraicSpace.separatedDenseAffineOpenLFT_of
    Langlands.AlgebraicGeometry.finiteLocallyFreeEquivalenceRelationAffineQuotient
    Langlands.AlgebraicGeometry.finiteLocallyFreeEquivalenceRelationInvariantAffineOpen
    Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteLocus.finiteLocus_invariant
  obtain ⟨V, W, i, p, b, hV, hVlft, hi, hpb, hdense⟩ :=
    hS1 k (quotient N).toSheaf (quotient N).property hd U a hea hsa hUa hU
  obtain ⟨_, w, _⟩ := hdense.nonempty
  let q : W ⟶ V := (schemeYoneda _).preimage b
  have : Nonempty V.left := ⟨q.left w⟩
  have htop : Subfunctor.range i = ⊤ := open_eq_top_of_nonempty N (Subfunctor.range i)
    (OpenSubfunctorLifting.range_open i hi) (uliftYonedaEquiv i) ⟨⟨𝟙 V⟩, rfl⟩
  have : Mono i := SliceOpenGluing.open_mono hi
  have : Epi i := (Subfunctor.epi_iff_range_eq_top i).mpr htop
  have : IsIso i := isIso_of_mono_of_epi i
  exact ⟨V, hV, hVlft, ⟨asIso i⟩⟩

/-- An affine scheme representing the actual quotient by the reduction,
with its actual smooth surjective scheme projection. -/
structure Model where
  space : Over (Spec (CommRingCat.of k))
  affine : IsAffine space.left
  locallyOfFiniteType : LocallyOfFiniteType space.hom
  comparison : (schemeYoneda _).obj space ≅ (quotient N).presheaf
  projection : N.X ⟶ space
  projection_eq : (schemeYoneda _).map projection ≫ comparison.hom =
    ReducedCosetAffine.projection N
  smooth : Smooth projection.left
  surjective : Surjective projection.left

/-- Choose an affine representative of the actual reduced-subgroup coset
space, retaining the canonical projection and all its scheme properties. -/
def model : Model N := Classical.choice (by
  obtain ⟨V, hVa, hVlft, ⟨e⟩⟩ := exists_affine_model N
  let q : N.X ⟶ V := (schemeYoneda _).preimage (projection N ≫ e.inv)
  have hq : (schemeYoneda _).map q = projection N ≫ e.inv :=
    Functor.map_preimage _ _
  have hqe : (schemeYoneda _).map q ≫ e.hom = projection N := by
    rw [hq]
    simp
  have hsm : IsSmooth ((schemeYoneda _).map q) := by
    rw [hq]
    exact (MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage (@Smooth.{u})
        (Over.forget (Spec (CommRingCat.of k)))).relative (schemeYoneda _))
      (projection N) e.inv).mpr
      (HomogeneousQuotientSheaf.smooth_projection (inclusion N) inferInstance)
  have hsurj : IsSurjective ((schemeYoneda _).map q) := by
    rw [hq]
    exact (MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget (Spec (CommRingCat.of k)))).relative (schemeYoneda _))
      (projection N) e.inv).mpr
      (HomogeneousQuotientSheaf.surjective_projection (inclusion N) inferInstance)
  exact
    ⟨{
      space := V
      affine := hVa
      locallyOfFiniteType := hVlft
      comparison := e
      projection := q
      projection_eq := hqe
      smooth := MorphismProperty.of_relative_map
        (P := MorphismProperty.inverseImage (@Smooth.{u})
          (Over.forget (Spec (CommRingCat.of k)))) (F := schemeYoneda _) hsm
      surjective := MorphismProperty.of_relative_map
        (P := MorphismProperty.inverseImage (@Surjective.{u})
          (Over.forget (Spec (CommRingCat.of k)))) (F := schemeYoneda _) hsurj }⟩)

end Langlands.GroupScheme.ReducedCosetAffine
