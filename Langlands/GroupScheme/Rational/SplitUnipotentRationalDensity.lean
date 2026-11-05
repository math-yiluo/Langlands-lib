import Langlands.AlgebraicGeometry.PointTopology.AffineDensity
import Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Dense rational points of split unipotent groups over infinite fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalDensity

open Langlands.AlgebraicGeometry.PointTopology RelativeRoot

variable {k : Type u} [Field k]

/-- The section `X' ⟶ X ⊗ X'` through a rational point `x` of `X`. -/
def pointSection {X : Over (Spec (CommRingCat.of k))} (X' : Over (Spec (CommRingCat.of k)))
    (x : RationalPoint k X) : X' ⟶ X ⊗ X' :=
  lift (toUnit X' ≫ x) (𝟙 X')

@[reassoc (attr := simp)]
theorem pointSection_fst {X : Over (Spec (CommRingCat.of k))}
    (X' : Over (Spec (CommRingCat.of k))) (x : RationalPoint k X) :
    pointSection X' x ≫ fst X X' = toUnit X' ≫ x :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem pointSection_snd {X : Over (Spec (CommRingCat.of k))}
    (X' : Over (Spec (CommRingCat.of k))) (x : RationalPoint k X) :
    pointSection X' x ≫ snd X X' = 𝟙 X' :=
  lift_snd _ _

/-- A point of `X ⊗ X'` lying over a rational point `x` of `X` is in the image of the
section through `x`. -/
theorem mem_range_pointSection {X X' : Over (Spec (CommRingCat.of k))}
    (x : RationalPoint k X) (a : Spec (CommRingCat.of k)) (z : (X ⊗ X').left)
    (h : x.left a = (fst X X').left z) :
    z ∈ Set.range (pointSection X' x).left := by
  obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := x.left) (g := (fst X X').left) a z h
  have hx : x.left ≫ X.hom = 𝟙 _ := Over.w x
  have hx' : x.left ≫ X.hom ≫ x.left = x.left := by
    rw [← Category.assoc, hx]
    exact Category.id_comp _
  have h1 : pullback.fst x.left (fst X X').left ≫ x.left =
      pullback.snd x.left (fst X X').left ≫ pullback.fst X.hom X'.hom :=
    pullback.condition
  have key : (pullback.snd x.left (fst X X').left ≫ (snd X X').left) ≫ (pointSection X' x).left =
      pullback.snd x.left (fst X X').left := by
    apply pullback.hom_ext
    · simp only [pointSection, Over.lift_left, Over.comp_left, Over.toUnit_left, Over.snd_left,
        Category.assoc, pullback.lift_fst]
      rw [← pullback.condition_assoc (f := X.hom) (g := X'.hom), ← reassoc_of% h1, hx', h1]
    · simp only [pointSection, Over.lift_left, Over.id_left, Over.snd_left, Category.assoc,
        pullback.lift_snd, Category.comp_id]
  refine ⟨(pullback.snd x.left (fst X X').left ≫ (snd X X').left) t, ?_⟩
  rw [← Scheme.Hom.comp_apply, key]
  exact ht

/-- If `X` has dense rational points and the first projection `X ⊗ X' ⟶ X` is open, the
union of the sections `X' ⟶ X ⊗ X'` through the rational points of `X` is dense. -/
theorem dense_iUnion_range_pointSection {X X' : Over (Spec (CommRingCat.of k))}
    (hopen : IsOpenMap (fst X X').left) (hX : HasDenseRationalPoints k X) :
    Dense (⋃ x : RationalPoint k X, Set.range (pointSection X' x).left) := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨z₀, hz₀⟩
  obtain ⟨w, hwO, hw⟩ := hX.inter_open_nonempty _ (hopen O hO) ⟨_, z₀, hz₀, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hwO
  simp only [Set.mem_iUnion, Set.mem_range] at hw
  obtain ⟨x, a, ha⟩ := hw
  exact ⟨z, hz, Set.mem_iUnion.mpr ⟨x, mem_range_pointSection x a z ha⟩⟩

/-- Dense rational points are stable under products when the first projection is open. -/
theorem HasDenseRationalPoints.tensor {X X' : Over (Spec (CommRingCat.of k))}
    (hopen : IsOpenMap (fst X X').left) (hX : HasDenseRationalPoints k X)
    (hX' : HasDenseRationalPoints k X') : HasDenseRationalPoints k (X ⊗ X') := by
  rw [HasDenseRationalPoints, dense_iff_inter_open]
  rintro O hO hne
  obtain ⟨z, hzO, hz⟩ := (dense_iUnion_range_pointSection (X' := X') hopen hX).inter_open_nonempty
    O hO hne
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨x, w, rfl⟩ := hz
  obtain ⟨_, hvO, hv⟩ := hX'.inter_open_nonempty _
    (hO.preimage (pointSection X' x).left.continuous) ⟨w, hzO⟩
  simp only [Set.mem_iUnion, Set.mem_range] at hv
  obtain ⟨x', b, rfl⟩ := hv
  refine ⟨_, hvO, Set.mem_iUnion.mpr ⟨x' ≫ pointSection X' x, b, ?_⟩⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply]

/-- Dense rational points transport along isomorphisms. -/
theorem HasDenseRationalPoints.of_iso {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)
    (hX : HasDenseRationalPoints k X) : HasDenseRationalPoints k Y := by
  apply hasDenseRationalPoints_of_denseRange e.hom _ hX
  apply Function.Surjective.denseRange
  intro y
  refine ⟨e.inv.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id, Over.id_left]
  rfl

/-- A trivial group scheme has dense rational points: its unit is surjective. -/
theorem hasDenseRationalPoints_of_range_id_eq_bot
    {H : GroupScheme (Spec (CommRingCat.of k))} (hH : SubgroupFunctor.range (𝟙 H) = ⊥) :
    HasDenseRationalPoints k H.X := by
  have hid : (𝟙 H.X : H.X ⟶ H.X) = 1 := by
    have hmem : 𝟙 H.X ∈ (SubgroupFunctor.range (𝟙 H)).carrier H.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.comp_id _⟩
    rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
    exact hmem
  apply Dense.mono (Set.subset_iUnion _ (η[H.X] : RationalPoint k H.X))
  apply Function.Surjective.denseRange
  intro z
  refine ⟨H.X.hom z, ?_⟩
  have h1 : (toUnit H.X ≫ η[H.X]).left = 𝟙 H.X.left := by
    rw [← Hom.one_def, ← hid, Over.id_left]
  rw [← Scheme.Hom.comp_apply]
  change ((toUnit H.X).left ≫ η[H.X].left) z = z
  rw [← Over.comp_left, h1]
  rfl

/-- Evaluations at rational points are dense in the spectrum of a polynomial ring over an
infinite field, for variables in `Type`. -/
theorem dense_mvPolynomial_evaluation (k : Type u) [Field k] [Infinite k] (n : Type) :
    Dense (Set.range fun x : n → k =>
      PrimeSpectrum.comap (MvPolynomial.eval x)
        (⟨⊥, inferInstance⟩ : PrimeSpectrum k)) := by
  classical
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨f, rfl⟩ ⟨p, hp⟩
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hp
  have he : ∃ x : n → k, MvPolynomial.eval x f ≠ 0 := by
    by_contra! h
    exact hf (MvPolynomial.funext fun x => by simpa using h x)
  obtain ⟨x, hx⟩ := he
  refine ⟨_, ?_, x, rfl⟩
  show PrimeSpectrum.comap (MvPolynomial.eval x) ⟨⊥, inferInstance⟩ ∈
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (MvPolynomial n k)))
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    Ideal.mem_bot]
  exact hx

/-- The spectrum of a polynomial ring over an infinite field has dense rational points, for
variables in `Type`. -/
theorem hasDenseRationalPoints_mvPolynomialSpec (k : Type u) [Field k] [Infinite k] (n : Type) :
    HasDenseRationalPoints k
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial n k)))) := by
  apply (dense_mvPolynomial_evaluation k n).mono
  rintro _ ⟨x, rfl⟩
  let p : RationalPoint k
      (Over.mk (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial n k)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (MvPolynomial.eval x))) (by
      change Spec.map (CommRingCat.ofHom (MvPolynomial.eval x)) ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _
      rw [← Spec.map_comp]
      convert Spec.map_id (CommRingCat.of k) using 1
      congr 1
      ext r
      exact MvPolynomial.eval_C r)
  exact Set.mem_iUnion.mpr ⟨p, ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum k), rfl⟩⟩

/-- Vector groups over infinite fields have dense rational points. -/
theorem hasDenseRationalPoints_vectorGroup [Infinite k] (n : ℕ) :
    HasDenseRationalPoints k (VectorGroup.groupScheme (CommRingCat.of k) n).X :=
  hasDenseRationalPoints_mvPolynomialSpec k (Fin n)

/-- One-dimensional vector groups over infinite fields have dense rational points. -/
theorem hasDenseRationalPoints_of_isVectorGroupOfDimension_one [Infinite k]
    {V : GroupScheme (Spec (CommRingCat.of k))} (hV : IsVectorGroupOfDimension V 1) :
    HasDenseRationalPoints k V.X :=
  HasDenseRationalPoints.of_iso ((Grp.forget _).mapIso hV.iso.symm)
    (hasDenseRationalPoints_vectorGroup 1)

/-- The first projection from a product whose second factor is flat and locally of
finite presentation over the field is open. -/
theorem isOpenMap_fst {X X' : Over (Spec (CommRingCat.of k))} [Flat X'.hom]
    [LocallyOfFinitePresentation X'.hom] : IsOpenMap (fst X X').left := by
  change IsOpenMap (pullback.fst X.hom X'.hom)
  exact (pullback.fst X.hom X'.hom).isOpenMap

/-- Over an infinite field, an affine group scheme with a finite split series has dense
rational points. -/
theorem hasDenseRationalPoints_of_hasSplitSeries [Infinite k] :
    ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))), HasSplitSeries n H →
      IsAffineHom H.X.hom → HasDenseRationalPoints k H.X
  | 0, _, h, _ => hasDenseRationalPoints_of_range_id_eq_bot h
  | n + 1, H, h, _ => by
    obtain ⟨K, V, Θ, hK, hV, hKa⟩ := SplitSeriesDecomposition.HasSplitSeries.exists_iso_tensor h
    have hKd := hasDenseRationalPoints_of_hasSplitSeries n K hK hKa
    have : Smooth V.X.hom := hV.smooth
    have hVd := hasDenseRationalPoints_of_isVectorGroupOfDimension_one hV
    exact HasDenseRationalPoints.of_iso Θ (HasDenseRationalPoints.tensor isOpenMap_fst hKd hVd)

/-- Over an infinite field, a split unipotent affine group scheme has dense rational
points. -/
theorem IsSplitUnipotent.hasDenseRationalPoints [Infinite k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (hH : IsSplitUnipotent H) : HasDenseRationalPoints k H.X := by
  obtain ⟨n, hn⟩ := hH
  exact hasDenseRationalPoints_of_hasSplitSeries n H hn inferInstance

end Langlands.GroupScheme.RationalDensity
