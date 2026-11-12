import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformGaloisChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.PointTopology.PointSecondCountabilityProof
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Langlands.FieldTheory.CountableGaloisFamily

/-!
# Rational points of separated algebraic spaces of finite type are second countable

Let `K` be a henselian valued field with a countable base, over which countably many finite
Galois extensions receive every finite separable extension. For a separated algebraic space `X`
of finite type over `K`, the étale-chart topology on `X(K)` is second countable.

Cover an étale atlas of finite type by finitely many affine opens `V`. Every rational point lifts
to a point of some `V` over some finite separable extension, hence over one of the countably many
Galois extensions `L`. For each pair `(V, L)` there is one affine étale chart `M` whose rational
points cover all rational points lifting to `V(L)` (`UniformGaloisChart.exists_chart`). The images
of these countably many charts are open, second countable and cover `X(K)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap)
open Langlands.FieldTheory.CountableGaloisFamily (HasCountableGaloisFamily)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace EtaleChartSecondCountable

variable {k : Type u} [Field k]

/-- The chart given by an open of an atlas. -/
abbrev openChart {U : Over (Spec (CommRingCat.of k))} (O : U.left.Opens) :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (O.ι ≫ U.hom)

/-- The inclusion of the open chart in the atlas. -/
abbrev openChartι {U : Over (Spec (CommRingCat.of k))} (O : U.left.Opens) : openChart O ⟶ U :=
  Over.homMk O.ι rfl

/-- **Lifting rational points to an affine cover of an atlas.** Every `k`-point of `X` lifts,
over a finite separable extension, to a point of one of the opens of a cover of an étale
surjective atlas. -/
theorem exists_lift (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    {U : Over (Spec (CommRingCat.of k))} (a₀ : (schemeYoneda _).obj U ⟶ X.presheaf)
    (ha₀ : IsRepresentableMorphism a₀) (he₀ : IsEtale a₀) (hs₀ : IsSurjective a₀)
    (𝒪 : Set U.left.Opens) (h𝒪 : ∀ y : U.left, ∃ O ∈ 𝒪, y ∈ O) (x : RingPoints k X k) :
    ∃ O ∈ 𝒪, ∃ (L : Type u) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ ∃ v : specOver k L ⟶ openChart O,
        (schemeYoneda _).map v ≫ (schemeYoneda _).map (openChartι O) ≫ a₀ =
          (schemeYoneda _).map (specOverMap (Algebra.ofId k L)) ≫
            (uliftYonedaEquiv.symm x :
              (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf) := by
  let xh : (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := ha₀.pullback xh
  let p : P ⟶ ringTest k k := ha₀.snd xh
  let q : P ⟶ U := Functor.relativelyRepresentable.fst' ha₀ xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a₀ xh :=
    Functor.relativelyRepresentable.isPullback' ha₀ xh
  have hpe : Etale p.left := he₀.projection xh _ p hsq
  have hps : Surjective p.left := hs₀.projection xh _ p hsq
  have : Etale P.hom := by
    rw [← GaloisChartPoint.ringTest_self_left p]
    exact hpe
  have : Nonempty P.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    obtain ⟨z, -⟩ := hps.surj y
    exact ⟨z⟩
  obtain ⟨L, _, _, hL, hLs, ⟨w₀⟩⟩ := GaloisChartPoint.exists_separable_point P
  let v₁ : specOver k L ⟶ U := w₀ ≫ q
  have hv₁ : (schemeYoneda _).map v₁ ≫ a₀ =
      (schemeYoneda _).map (specOverMap (Algebra.ofId k L)) ≫ xh := by
    have hp : (w₀ ≫ p : specOver k L ⟶ ringTest k k) = specOverMap (Algebra.ofId k L) :=
      GaloisChartPoint.ringTest_self_hom_ext _ _
    simp only [v₁, Functor.map_comp, Category.assoc, hsq.w]
    rw [← Functor.map_comp_assoc]
    exact congrArg (fun t => (schemeYoneda _).map t ≫ xh) hp
  obtain ⟨y₀⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  obtain ⟨O, hO, hyO⟩ := h𝒪 (v₁.left y₀)
  have hrange : Set.range v₁.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim (α := Spec (CommRingCat.of L)) y y₀]
  let v : specOver k L ⟶ openChart O := Over.homMk (IsOpenImmersion.lift O.ι v₁.left hrange) (by
    change IsOpenImmersion.lift O.ι v₁.left hrange ≫ O.ι ≫ U.hom = _
    rw [IsOpenImmersion.lift_fac_assoc]
    exact Over.w v₁)
  have hv : v ≫ openChartι O = v₁ := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨O, hO, L, inferInstance, inferInstance, hL, hLs, v, ?_⟩
  rw [← Functor.map_comp_assoc, hv, hv₁]

/-- **Descent along a Galois extension.** A Galois-invariant `K`-point of an affine chart over
a `k`-point of `X` descends to a `k`-point of the chart with the same image. -/
theorem exists_point_of_invariant (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Over (Spec (CommRingCat.of k))} [IsAffine M.left]
    (tM : (schemeYoneda _).obj M ⟶ X.presheaf) (x : RingPoints k X k)
    (w : specOver k K ⟶ M) (hw : ∀ g : K ≃ₐ[k] K, specOverMap g.toAlgHom ≫ w = w)
    (hwt : (schemeYoneda _).map w ≫ tM = (schemeYoneda _).map (specOverMap (Algebra.ofId k K)) ≫
      (uliftYonedaEquiv.symm x :
        (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf)) :
    ∃ u : RingPoint k M k,
      RingPoints.map (AlgebraicSpace.homMk tM : (schemeToSpace _).obj M ⟶ X)
        ((schemeRingPointsEquiv k M k).symm u) = x := by
  obtain ⟨u, hu⟩ := GaloisChartPoint.exists_desc_of_galois_invariant w hw
  refine ⟨u, ?_⟩
  apply GaloisChartPoint.changeRing_injective X K
  have e₁ : RingPoints.map (AlgebraicSpace.homMk tM : (schemeToSpace _).obj M ⟶ X)
      ((schemeRingPointsEquiv k M k).symm u) =
        uliftYonedaEquiv ((schemeYoneda _).map u ≫ tM) := by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  have e₂ : x = uliftYonedaEquiv
      (uliftYonedaEquiv.symm x : (schemeYoneda _).obj (ringTest k k) ⟶ X.presheaf) :=
    (Equiv.apply_symm_apply _ _).symm
  have hu' : ringTestMap k (Algebra.ofId k K) ≫ u = w := hu
  rw [e₁, e₂]
  change X.presheaf.map (ringTestMap k (Algebra.ofId k K)).op _ =
    X.presheaf.map (ringTestMap k (Algebra.ofId k K)).op _
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  congr 1
  rw [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, hu']
  exact hwt

/-- **Countably many affine charts.** A separated algebraic space of finite type over a field
with a countable Galois family has countably many affine étale charts whose rational points
cover its rational points. -/
theorem exists_countable_charts (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : IsSeparated X) (hft : FiniteTypeOverRing k X) (hfam : HasCountableGaloisFamily k) :
    ∃ (ι : Type u) (_ : Countable ι) (M : ι → Over (Spec (CommRingCat.of k)))
      (tM : ∀ i, (schemeYoneda _).obj (M i) ⟶ X.presheaf),
      (∀ i, IsAffine (M i).left ∧ IsEtale (tM i)) ∧
      ∀ x : RingPoints k X k, ∃ i, ∃ u : RingPoint k (M i) k,
        RingPoints.map (AlgebraicSpace.homMk (tM i) : (schemeToSpace _).obj (M i) ⟶ X)
          ((schemeRingPointsEquiv k (M i) k).symm u) = x := by
  classical
  obtain ⟨U, a₀, he₀, hs₀, hP⟩ := hft
  have ha₀ : IsRepresentableMorphism a₀ := he₀.1
  have hQC : QuasiCompact U.hom := hP.2
  have hcpt : IsCompact (Set.univ : Set U.left) := by
    have := hQC.isCompact_preimage Set.univ isOpen_univ isCompact_univ
    simpa using this
  obtain ⟨s, hs, hseq⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : U.left.Opens))).mp (by simpa using hcpt)
  have : Finite s := hs.to_subtype
  obtain ⟨J, hJ, L, _, _, hLg, hLemb⟩ := hfam
  have hmem : ∀ y : U.left, ∃ O ∈ ((fun O : U.left.affineOpens => (O : U.left.Opens)) '' s),
      y ∈ O := by
    intro y
    have hy : y ∈ (⊤ : U.left.Opens) := trivial
    rw [hseq] at hy
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨O, hO, hyO⟩ := hy
    exact ⟨O, ⟨O, hO, rfl⟩, hyO⟩
  have hchart : ∀ p : s × J, ∃ (M : Over (Spec (CommRingCat.of k)))
      (tM : (schemeYoneda _).obj M ⟶ X.presheaf), IsAffine M.left ∧ IsEtale tM ∧
      ∀ (xh : (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf)
        (v : specOver k (L p.2) ⟶ openChart (p.1 : U.left.affineOpens).1)
        (π : specOver k (L p.2) ⟶ ringTest k k),
        (schemeYoneda _).map v ≫ (schemeYoneda _).map (openChartι _) ≫ a₀ =
          (schemeYoneda _).map π ≫ xh →
        ∃ w : specOver k (L p.2) ⟶ M,
          (∀ g : L p.2 ≃ₐ[k] L p.2, specOverMap g.toAlgHom ≫ w = w) ∧
          (schemeYoneda _).map w ≫ tM = (schemeYoneda _).map π ≫ xh := by
    intro p
    have := (hLg p.2).1
    have := (hLg p.2).2
    have hOaff : IsAffine (openChart (p.1 : U.left.affineOpens).1).left :=
      (p.1 : U.left.affineOpens).2
    have hsep : _root_.AlgebraicGeometry.IsSeparated
        (openChart (p.1 : U.left.affineOpens).1).hom :=
      _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom (h := isAffineHom_of_isAffine _)
    have het : IsEtale ((schemeYoneda _).map (openChartι (p.1 : U.left.affineOpens).1) ≫ a₀) :=
      IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale (p.1 : U.left.affineOpens).1.ι))) he₀
    exact UniformGaloisChart.exists_chart X hX (L p.2) _ het
  choose M tM hM using hchart
  refine ⟨s × J, inferInstance, M, tM, fun p => ⟨(hM p).1, (hM p).2.1⟩, fun x => ?_⟩
  obtain ⟨O, ⟨O', hO', rfl⟩, E, _, _, hE, hEs, v, hv⟩ :=
    exists_lift X a₀ ha₀ he₀ hs₀ _ hmem x
  obtain ⟨j, ⟨ψ⟩⟩ := hLemb E
  have := (hLg j).1
  have := (hLg j).2
  let p : s × J := (⟨O', hO'⟩, j)
  have hv' : (schemeYoneda _).map (specOverMap ψ ≫ v) ≫
      (schemeYoneda _).map (openChartι (p.1 : U.left.affineOpens).1) ≫ a₀ =
      (schemeYoneda _).map (specOverMap (Algebra.ofId k (L j))) ≫
        (uliftYonedaEquiv.symm x :
          (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf) := by
    have e : (specOverMap ψ ≫ specOverMap (Algebra.ofId k E) : specOver k (L j) ⟶ ringTest k k) =
        specOverMap (Algebra.ofId k (L j)) := GaloisChartPoint.ringTest_self_hom_ext _ _
    rw [Functor.map_comp_assoc, hv]
    exact ((schemeYoneda _).map_comp_assoc _ _ _).symm.trans
      (congrArg (fun t => (schemeYoneda _).map t ≫ _) e)
  obtain ⟨w, hw, hwt⟩ := (hM p).2.2 _ (specOverMap ψ ≫ v) _ hv'
  have := (hM p).1
  obtain ⟨u, hu⟩ := exists_point_of_invariant X (tM p) x w hw hwt
  exact ⟨p, u, hu⟩

/-- The image of a second countable space under a continuous open map is second countable. -/
theorem secondCountableTopology_range {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [SecondCountableTopology α] {f : α → β} (hf : Continuous f) (ho : IsOpenMap f) :
    SecondCountableTopology (Set.range f) :=
  (IsOpenQuotientMap.mk Set.rangeFactorization_surjective hf.rangeFactorization
    (ho.subtype_mk fun x => Set.mem_range_self x)).secondCountableTopology

variable {K : Type u} [NontriviallyNormedField K]

/-- **Second countability.** Over a henselian valued field with a countable base and a countable
Galois family, the rational points of a separated algebraic space of finite type are second
countable for the étale-chart topology. -/
theorem secondCountableTopology_etaleChartTopology
    (hK : Langlands.AlgebraicGeometry.PointTopology.IsHenselianValuedField K)
    [SecondCountableTopology K] (hfam : HasCountableGaloisFamily K)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsSeparated X)
    (hft : FiniteTypeOverRing K X) : @SecondCountableTopology _ (etaleChartTopology K X) := by
  obtain ⟨ι, hι, M, tM, hMp, hcov⟩ := exists_countable_charts X hX hft hfam
  have hlft : LocallyOfFiniteTypeOverBase X := by
    obtain ⟨U, a, ha, hs, hP⟩ := hft
    exact ⟨U, a, ha, hs, hP.1⟩
  let c : ι → EtaleFiniteTypeChart K X := fun i =>
    { scheme := M i
      hom := AlgebraicSpace.homMk (tM i)
      isEtale := (hMp i).2
      locallyOfFiniteType := locallyOfFiniteType_of_isEtale hlft (tM i) (hMp i).2
      quasiCompact := by
        have := (hMp i).1
        infer_instance }
  let _ := etaleChartTopology K X
  have hsc : ∀ i, SecondCountableTopology (Set.range (c i).pointMap) := fun i => by
    let _ : TopologicalSpace (RingPoint K (c i).scheme K) :=
      Langlands.AlgebraicGeometry.PointTopology.schemePointTopology K (c i).scheme K
    have : LocallyOfFiniteType (c i).scheme.hom := (c i).locallyOfFiniteType
    have : QuasiCompact (c i).scheme.hom := (c i).quasiCompact
    have : SecondCountableTopology (RingPoint K (c i).scheme K) :=
      Langlands.AlgebraicGeometry.PointTopology.schemePointSecondCountability K K (c i).scheme
    exact secondCountableTopology_range (c i).continuous_pointMap
      (EtaleFiniteTypeChart.isOpenMap_pointMap hK (c i))
  have hopen : ∀ i, IsOpen (Set.range (c i).pointMap) := fun i => by
    let _ : TopologicalSpace (RingPoint K (c i).scheme K) :=
      Langlands.AlgebraicGeometry.PointTopology.schemePointTopology K (c i).scheme K
    exact (EtaleFiniteTypeChart.isOpenMap_pointMap hK (c i)).isOpen_range
  have := hsc
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i => Set.range (c i).pointMap) hopen ?_
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨i, u, hu⟩ := hcov x
  exact Set.mem_iUnion.mpr ⟨i, u, hu⟩

end EtaleChartSecondCountable

end Langlands.AlgebraicGeometry.AlgebraicSpace
