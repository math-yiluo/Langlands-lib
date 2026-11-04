import Langlands.GroupScheme.Rational.SplitSeriesDimension
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.HomogeneousQuotientRationalPoints
import Langlands.GroupScheme.FiniteFieldTorsorPointProof

/-! # Lie dimension and rational point count of split unipotent groups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- A group trivial on every test has Lie dimension zero. -/
theorem lieDimension_eq_zero_of_range_eq_bot {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] (h : SubgroupFunctor.range (𝟙 H) = ⊥) : Lie.dimension H = 0 := by
  have : Subsingleton (Additive (lieKernel H k)) := by
    constructor
    intro X Y
    have hX : ∀ Z : Additive (lieKernel H k), Z = 0 := by
      intro Z
      apply Additive.toMul.injective
      apply Subtype.ext
      have hm : Z.toMul.val ∈ (SubgroupFunctor.range (𝟙 H)).carrier _ :=
        ⟨Z.toMul.val, by
          change Z.toMul.val ≫ (𝟙 H : H ⟶ H).hom.hom = Z.toMul.val
          rw [Grp.id_hom_hom, Category.comp_id]⟩
      rw [h] at hm
      exact hm
    rw [hX X, hX Y]
  exact Module.finrank_zero_of_subsingleton

/-- An actual vector group of dimension `d` has Lie dimension `d`. -/
theorem IsVectorGroupOfDimension.lieDimension {V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom V.X.hom] {d : ℕ} (h : IsVectorGroupOfDimension V d) : Lie.dimension V = d := by
  obtain ⟨e, he⟩ := h
  have h := (vectorLieCoordinates e he (CommAlgCat.of k k)).finrank_eq
  unfold Lie.dimension
  simpa using h

/-- Lie dimension is additive along a represented fppf quotient whose kernel is smooth. -/
theorem IsFppfQuotient.lieDimension_eq_add {K H V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom H.X.hom] [IsAffineHom V.X.hom] [Smooth K.X.hom]
    [LocallyOfFiniteType H.X.hom] {j : K ⟶ H} (hj : IsClosedSubgroup j) {q : H ⟶ V}
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q) :
    Lie.dimension H = Lie.dimension K + Lie.dimension V := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hz : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have hsm : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hz inferInstance
  let L := Lie.targetMapLinear q k
  have hL : Function.Surjective L := Lie.targetMapLinear_surjective_of_smooth q k hsm
  let M := Lie.targetMapLinear j k
  have hM : Function.Injective M := Lie.targetMapLinear_injective j k
  have hker : LinearMap.ker L = LinearMap.range M := by
    apply le_antisymm
    · intro X hX
      have hX' : X.toMul.val ≫ q.hom.hom = 1 :=
        congrArg (fun Z : Additive (lieKernel V k) => Z.toMul.val) hX
      have hfib := (hq.fibers_iff hz _ 1 X.toMul.val).mp (by rw [MonObj.one_comp, hX'])
      rw [inv_one, one_mul] at hfib
      obtain ⟨Y, hY⟩ := hfib
      change Y ≫ j.hom.hom = X.toMul.val at hY
      have hYker : Y ∈ (Lie.reduction K (A := k)).ker := by
        apply mem_lieKernel_of_comp j Y
        rw [hY]
        exact X.toMul.property
      refine ⟨Additive.ofMul ⟨Y, hYker⟩, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hY
    · rintro _ ⟨Y, rfl⟩
      rw [LinearMap.mem_ker]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (Y.toMul.val ≫ j.hom.hom) ≫ q.hom.hom = 1
      have hfib := (hq.fibers_iff hz _ 1 (Y.toMul.val ≫ j.hom.hom)).mpr (by
        rw [inv_one, one_mul]
        exact ⟨Y.toMul.val, rfl⟩)
      rw [← hfib, MonObj.one_comp]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, hker,
    LinearMap.finrank_range_of_inj hM] at hrank
  unfold Lie.dimension
  omega

/-- The length of a finite Ga-series of a smooth affine group is its Lie dimension. -/
theorem HasSplitSeries.lieDimension_eq : ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [Smooth H.X.hom], HasSplitSeries n H → Lie.dimension H = n
  | 0, _, _, _, h => lieDimension_eq_zero_of_range_eq_bot h
  | n + 1, H, _, _, ⟨K, V, j, q, hj, hK, _, _, hq, hV, hs⟩ => by
    have : IsAffineHom K.X.hom := hj.isAffineHom
    have : IsAffineHom V.X.hom := hV.isAffineHom
    have : Smooth K.X.hom := hK
    rw [hq.lieDimension_eq_add hj, HasSplitSeries.lieDimension_eq n K hs, hV.lieDimension]

/-- A one-dimensional vector group over a field has as many rational points as the field. -/
theorem IsVectorGroupOfDimension.card_rationalPoints_one
    {V : GroupScheme (Spec (CommRingCat.of k))} (h : IsVectorGroupOfDimension V 1) :
    Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X) = Nat.card k := by
  obtain ⟨e, -⟩ := h
  rw [Nat.card_congr (e (Over.mk (𝟙 (Spec (CommRingCat.of k))))).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd.trans (Equiv.funUnique (Fin 1) _))]
  exact Nat.card_congr (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv

/-- Over a finite field with `q` elements, a group with a Ga-series of length `n` has
`q ^ n` rational points. -/
theorem HasSplitSeries.card_rationalPoints [Finite k] :
    ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom],
      HasSplitSeries n H →
        Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) = Nat.card k ^ n
  | 0, H, _, h => by
    rw [pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
    have hx : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, z = 1 := by
      intro z
      have hm : z ∈ (SubgroupFunctor.range (𝟙 H)).carrier _ := ⟨z, by
        change z ≫ (𝟙 H : H ⟶ H).hom.hom = z
        rw [Grp.id_hom_hom, Category.comp_id]⟩
      rw [h] at hm
      exact hm
    rw [hx x, hx y]
  | n + 1, H, _, ⟨K, V, j, q, hj, hK, hKc, _, hq, hV, hs⟩ => by
    let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
    have : IsAffineHom K.X.hom := hj.isAffineHom
    have : IsAffineHom V.X.hom := hV.isAffineHom
    have : Smooth K.X.hom := hK
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have hz : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
    have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
    have : Flat q.hom.hom.left := hq.1
    have : Surjective q.hom.hom.left := hq.2.1
    let φ : (T₀ ⟶ H.X) →* (T₀ ⟶ V.X) := ((yonedaGrp.map q).app (Opposite.op T₀)).hom
    have hφ : ∀ y, φ y = y ≫ q.hom.hom := fun _ => rfl
    have hsurj : Function.Surjective φ := by
      intro p
      obtain ⟨g, hg⟩ := HomogeneousQuotient.rational_lifts_of_finite_torsor_identity k H K j
        q.hom.hom (fun T g h => hq.fibers_iff hz T g h) finiteFieldTorsorPointStatement hKc p
      exact ⟨g, hg⟩
    have hker : Nat.card φ.ker = Nat.card (T₀ ⟶ K.X) := by
      symm
      refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨z ≫ j.hom.hom, ?_⟩) ⟨?_, ?_⟩)
      · rw [MonoidHom.mem_ker, hφ]
        have h := (hq.fibers_iff hz T₀ 1 (z ≫ j.hom.hom)).mpr (by
          rw [inv_one, one_mul]
          exact ⟨z, rfl⟩)
        rw [← h, MonObj.one_comp]
      · intro z z' hzz
        exact (cancel_mono j.hom.hom).mp (congrArg Subtype.val hzz)
      · rintro ⟨y, hy⟩
        rw [MonoidHom.mem_ker, hφ] at hy
        have h := (hq.fibers_iff hz T₀ 1 y).mp (by rw [MonObj.one_comp, hy])
        rw [inv_one, one_mul] at h
        obtain ⟨z, hz'⟩ := h
        exact ⟨z, Subtype.ext hz'⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, hker,
      HasSplitSeries.card_rationalPoints n K hs, hV.card_rationalPoints_one, pow_succ, mul_comm]

/-- Over a finite field, a closed split unipotent subgroup of a smooth connected split
unipotent affine group that contains every rational point is the whole group. -/
theorem isIso_of_surjective_rationalPoints [Finite k]
    {V U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    [IsAffineHom V.X.hom] [Smooth V.X.hom]
    (f : V ⟶ U) (hf : IsClosedSubgroup f) (hV : IsSplitUnipotent V) (hU : IsSplitUnipotent U)
    (hsurj : ∀ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
      ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X, v ≫ f.hom.hom = u) :
    IsIso f := by
  obtain ⟨nV, hsV⟩ := hV
  obtain ⟨nU, hsU⟩ := hU
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have hcard : Nat.card k ^ nV = Nat.card k ^ nU := by
    rw [← HasSplitSeries.card_rationalPoints nV V hsV,
      ← HasSplitSeries.card_rationalPoints nU U hsU]
    exact Nat.card_congr (Equiv.ofBijective (fun v => v ≫ f.hom.hom)
      ⟨fun v v' h => (cancel_mono f.hom.hom).mp h, hsurj⟩)
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hn : nV = nU := Nat.pow_right_injective hq hcard
  by_contra hiso
  have hlt := Lie.dimension_lt_of_proper_closedSubgroup f hf hiso
  rw [HasSplitSeries.lieDimension_eq nV V hsV, HasSplitSeries.lieDimension_eq nU U hsU] at hlt
  omega

end Langlands.GroupScheme.RelativeRoot
