import Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibreProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPointsSmall
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.AlgebraicGeometry.PointTopology.ConvergentGermsHenselian
import Langlands.AlgebraicGeometry.PointTopology.UltrapowerSpreading
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof

/-!
# Limits of rational points of algebraic spaces along ultrafilters

The valuative lift for separated universally closed morphisms of algebraic spaces, applied over
the ring of convergent germs of an ultrapower of a local field, produces limits of families of
rational points whose images converge.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace LocalFieldProperPointLimit

section Affine

variable {K : Type u} [Field K] [TopologicalSpace K] {W : Over (Spec (CommRingCat.of K))}
  [IsAffine W.left] {I : Type u}

/-- Convergence of rational points of an affine scheme is coordinatewise convergence. -/
theorem tendsto_affine_iff {l : Filter I} (q : I → RingPoint K W K) (w : RingPoint K W K) :
    Tendsto q l (@nhds _ (schemePointTopology K W K) w) ↔
      ∀ t, Tendsto (fun i => affineSchemePointEquiv K W K (q i) t) l
        (𝓝 (affineSchemePointEquiv K W K w t)) := by
  rw [schemePointTopology_eq_affine,
    (affineSchemePointHomeomorph K W K).isInducing.tendsto_nhds_iff,
    AlgPoint.isEmbedding_evaluation.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

omit [TopologicalSpace K] in
/-- The coordinates of a point with values in a product of copies of `K` are the families of
coordinates of its components. -/
theorem affineSchemePointEquiv_pi (P : RingPoint K W (I → K)) (t : AffineCoordinateRing K W)
    (i : I) :
    affineSchemePointEquiv K W (I → K) P t i =
      affineSchemePointEquiv K W K (P.changeRing (Pi.evalAlgHom K (fun _ => K) i)) t := by
  rw [affineSchemePointEquiv_changeRing]
  rfl

end Affine

section Germs

variable {K : Type u} [NontriviallyNormedField K] [LocallyCompactSpace K] {I : Type u}
  (𝒰 : Ultrafilter I) (hnd : ¬ DiscreteTopology K)

/-- A point with values in `K^I` whose components converge along `𝒰` on an affine scheme gives a
point with values in the convergent germs, lifting the ultrapower point and reducing to the
limit. -/
theorem exists_convergentGerm_point {V : Over (Spec (CommRingCat.of K))} [IsAffine V.left]
    (P : RingPoint K V (I → K)) (v₀ : RingPoint K V K)
    (hP : Tendsto (fun i => P.changeRing (Pi.evalAlgHom K (fun _ => K) i)) 𝒰
      (@nhds _ (schemePointTopology K V K) v₀)) :
    ∃ vO : RingPoint K V (convergentGerms K 𝒰 hnd),
      vO.changeRing (IsScalarTower.toAlgHom K (convergentGerms K 𝒰 hnd)
          (UltrapowerField K 𝒰)) = P.changeRing (ultrapowerMap K 𝒰) ∧
        vO.changeRing (standardPart K 𝒰 hnd) = v₀ := by
  rw [tendsto_affine_iff] at hP
  let φ := (affineSchemePointEquiv K V (I → K) P).toAlgHom
  have hconv : ∀ t, Tendsto (φ t) 𝒰 (𝓝 (affineSchemePointEquiv K V K v₀ t)) := fun t => by
    have h := hP t
    have e : φ t = fun i => affineSchemePointEquiv K V K
        (P.changeRing (Pi.evalAlgHom K (fun _ => K) i)) t :=
      funext fun i => affineSchemePointEquiv_pi P t i
    rw [e]
    exact h
  have hmem : ∀ t, ultrapowerMap K 𝒰 (φ t) ∈ convergentGerms K 𝒰 hnd :=
    fun t => (mem_convergentGerms_iff K 𝒰 hnd).2 ⟨_, hconv t⟩
  let H : AffineCoordinateRing K V →ₐ[K] convergentGerms K 𝒰 hnd :=
    { RingHom.codRestrict ((ultrapowerMap K 𝒰).comp φ).toRingHom _ hmem with
      commutes' := fun c => Subtype.ext (((ultrapowerMap K 𝒰).comp φ).commutes c) }
  refine ⟨(affineSchemePointEquiv K V _).symm (AlgPoint.ofAlgHom H), ?_, ?_⟩
  · apply (affineSchemePointEquiv K V _).injective
    rw [affineSchemePointEquiv_changeRing, affineSchemePointEquiv_changeRing,
      Equiv.apply_symm_apply]
    ext t
    rfl
  · apply (affineSchemePointEquiv K V K).injective
    rw [affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
    ext t
    exact standardPart_eq_of_tendsto (H t) rfl (hconv t)

end Germs

section Chart

variable {K : Type u} [Field K]

/-- A chart point whose Yoneda composite is a given point maps to that point. -/
theorem pointMap_eq_of_comp {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X') (y : RingPoint K c.scheme K) (x : RingPoints K X' K)
    (h : (schemeYoneda _).map y ≫ hom c.hom = uliftYonedaEquiv.{u + 1}.symm x) :
    c.pointMap y = x := by
  let a : (schemeYoneda _).obj c.scheme ⟶ X'.presheaf := hom c.hom
  let y' : ringTest K K ⟶ c.scheme := y
  have h' : (schemeYoneda _).map y' ≫ a = uliftYonedaEquiv.{u + 1}.symm x := h
  have e := congrArg uliftYonedaEquiv.{u + 1} h'
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map] at e
  exact e.trans (Equiv.apply_symm_apply _ _)

/-- The Yoneda composite of a chart point is the Yoneda point of its image. -/
theorem comp_eq_pointMap {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X') (y : RingPoint K c.scheme K) :
    (schemeYoneda _).map y ≫ hom c.hom = uliftYonedaEquiv.{u + 1}.symm (c.pointMap y) := by
  let a : (schemeYoneda _).obj c.scheme ⟶ X'.presheaf := hom c.hom
  let y' : ringTest K K ⟶ c.scheme := y
  change (schemeYoneda _).map y' ≫ a = _
  apply uliftYonedaEquiv.{u + 1}.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
  exact (Equiv.apply_symm_apply _ _).symm

end Chart

section Spreading

variable {K : Type u} [NontriviallyNormedField K] [LocallyCompactSpace K] {I : Type u}
  (𝒰 : Ultrafilter I) (hnd : ¬ DiscreteTopology K)

/-- **Convergence through a chart.** Let `P ∈ X'(K^I)` have components `p i`, and let `z` be a
point of an affine chart with values in the convergent germs whose image over the ultrapower is
the ultrapower point of `P`. Then `p` converges along `𝒰` to the image of the reduction of
`z`. -/
theorem tendsto_of_chart_lift {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X') [IsAffine c.scheme.left]
    (p : I → RingPoints K X' K) (P : RingPoints K X' (I → K))
    (hP : ∀ i, RingPoints.changeRing (Pi.evalAlgHom K (fun _ => K) i) P = p i)
    (z : RingPoint K c.scheme (convergentGerms K 𝒰 hnd))
    (hz : (schemeYoneda _).map (z.changeRing (IsScalarTower.toAlgHom K
        (convergentGerms K 𝒰 hnd) (UltrapowerField K 𝒰))) ≫ hom c.hom =
      uliftYonedaEquiv.{u + 1}.symm (RingPoints.changeRing (ultrapowerMap K 𝒰) P)) :
    @Tendsto I _ p 𝒰 (@nhds _ (etaleChartTopology K X')
      (c.pointMap (z.changeRing (standardPart K 𝒰 hnd)))) := by
  classical
  let R := I → K
  let G := ultrapowerMap K 𝒰
  let ι := IsScalarTower.toAlgHom K (convergentGerms K 𝒰 hnd) (UltrapowerField K 𝒰)
  let ρ := standardPart K 𝒰 hnd
  let _ : Algebra R (UltrapowerField K 𝒰) := G.toRingHom.toAlgebra
  have : IsScalarTower K R (UltrapowerField K 𝒰) :=
    IsScalarTower.of_algebraMap_eq fun c => algebraMap_ultrapowerField_apply c
  have hsurj : Function.Surjective (algebraMap R (UltrapowerField K 𝒰)) :=
    ultrapowerMap_surjective
  have hker : ∀ f : R, algebraMap R (UltrapowerField K 𝒰) f = 0 ↔
      ∀ᶠ i in (𝒰 : Filter I), f i = 0 := fun f => by
    change G f = 0 ↔ _
    rw [← map_zero G, ultrapowerMap_eq_iff]
    rfl
  -- the represented pullback `E` of the chart along `P`
  let a : (schemeYoneda _).obj c.scheme ⟶ X'.presheaf := hom c.hom
  have ha : IsEtale a := c.isEtale
  let hr := X'.representable_from_scheme a
  let yP : (schemeYoneda _).obj (ringTest K R) ⟶ X'.presheaf := uliftYonedaEquiv.{u + 1}.symm P
  let E := hr.pullback yP
  let sE : E ⟶ ringTest K R := hr.snd yP
  let fE : E ⟶ c.scheme := Functor.relativelyRepresentable.fst' hr yP
  have hsq : IsPullback ((schemeYoneda _).map fE) ((schemeYoneda _).map sE) a yP :=
    Functor.relativelyRepresentable.isPullback' hr yP
  have hEt : Etale sE.left := ha.projection yP _ sE hsq
  let E' : Over (Spec (CommRingCat.of R)) := Over.mk sE.left
  have : LocallyOfFinitePresentation E'.hom := by
    change LocallyOfFinitePresentation sE.left
    infer_instance
  -- the ultrapower point of `E`
  let ωL := z.changeRing ι
  have hω : (schemeYoneda _).map ωL ≫ a = (schemeYoneda _).map (ringTestMap K G) ≫ yP := by
    change (schemeYoneda _).map ωL ≫ hom c.hom = _
    rw [hz, ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]
  let eL : ringTest K (UltrapowerField K 𝒰) ⟶ E :=
    Functor.relativelyRepresentable.lift' hr ωL (ringTestMap K G) hω
  have heL₁ : eL ≫ fE = ωL := Functor.relativelyRepresentable.lift'_fst hr _ _ _
  have heL₂ : eL ≫ sE = ringTestMap K G := Functor.relativelyRepresentable.lift'_snd hr _ _ _
  let pL : RingPoint R E' (UltrapowerField K 𝒰) := Over.homMk eL.left (by
    change eL.left ≫ sE.left = Spec.algebraMap R (UltrapowerField K 𝒰)
    rw [← Over.comp_left, heL₂]
    rfl)
  obtain ⟨A, hA, q, hq⟩ := exists_stage_ringPoint K 𝒰 hker hsurj E' pL
  -- the stage point as a `K`-point of `E`
  let B := R ⧸ vanishing K A
  have hqw : q.left ≫ E.hom = (ringTest K B).hom := by
    have h1 : q.left ≫ sE.left = Spec.algebraMap R B := Over.w q
    rw [← Over.w sE, ← Category.assoc, h1]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let qK : ringTest K B ⟶ E := Over.homMk q.left hqw
  have hqs : qK ≫ sE = ringTestMap K (Ideal.Quotient.mkₐ K (vanishing K A)) := by
    ext1
    exact Over.w q
  let σ : B →ₐ[K] UltrapowerField K 𝒰 := (stageMap K 𝒰 hker hA).restrictScalars K
  have hqσ : ringTestMap K σ ≫ qK = eL := by
    ext1
    exact congrArg (fun t : RingPoint R E' _ => t.left) hq
  let w' : RingPoint K c.scheme B := qK ≫ fE
  have hw'σ : w'.changeRing σ = ωL := by
    change ringTestMap K σ ≫ qK ≫ fE = ωL
    rw [← Category.assoc, hqσ, heL₁]
  have hw'c : (schemeYoneda _).map w' ≫ a =
      (schemeYoneda _).map (ringTestMap K (Ideal.Quotient.mkₐ K (vanishing K A))) ≫ yP := by
    change (schemeYoneda _).map (qK ≫ fE) ≫ a = _
    rw [Functor.map_comp, Category.assoc, hsq.w, ← Category.assoc, ← Functor.map_comp, hqs]
  -- components of the stage point
  let ev : ∀ i ∈ A, B →ₐ[K] K := fun i hi =>
    Ideal.Quotient.liftₐ (vanishing K A) (Pi.evalAlgHom K (fun _ => K) i) (fun f hf => hf i hi)
  have hcomp : ∀ i (hi : i ∈ A), c.pointMap (w'.changeRing (ev i hi)) = p i := by
    intro i hi
    apply pointMap_eq_of_comp
    have he : (ev i hi).comp (Ideal.Quotient.mkₐ K (vanishing K A)) =
        Pi.evalAlgHom K (fun _ => K) i := AlgHom.ext fun _ => rfl
    change (schemeYoneda _).map (ringTestMap K (ev i hi) ≫ w') ≫ a = _
    rw [Functor.map_comp, Category.assoc, hw'c, ← Category.assoc, ← Functor.map_comp,
      ← ringTestMap_comp, he, ← hP i, ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]
  -- coordinates converge
  let z₀ := z.changeRing ρ
  let wfam : I → RingPoint K c.scheme K := fun i =>
    if hi : i ∈ A then w'.changeRing (ev i hi) else z₀
  have hwt : Tendsto wfam 𝒰 (@nhds _ (schemePointTopology K c.scheme K) z₀) := by
    rw [tendsto_affine_iff]
    intro t
    change Tendsto (fun i => AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme K (wfam i)) t)
      𝒰 (𝓝 (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme K z₀) t))
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective
      (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme B w') t)
    have h : AlgPoint.mapCoefficients σ (affineSchemePointEquiv K c.scheme B w') =
        AlgPoint.mapCoefficients ι (affineSchemePointEquiv K c.scheme _ z) := by
      rw [← affineSchemePointEquiv_changeRing, ← affineSchemePointEquiv_changeRing, hw'σ]
    have h' := congrArg (fun φ => AlgPoint.toAlgHom φ t) h
    change σ (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme B w') t) =
      ι (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme _ z) t) at h'
    rw [← hf] at h'
    have h1 : ((AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme _ z) t :
        convergentGerms K 𝒰 hnd) : UltrapowerField K 𝒰) = G f := h'.symm
    have h2 := tendsto_standardPart K 𝒰 hnd _ h1
    have h3 : ρ (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme _ z) t) =
        AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme K z₀) t := by
      change _ = AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme K (z.changeRing ρ)) t
      rw [affineSchemePointEquiv_changeRing]
      rfl
    rw [← h3]
    refine h2.congr' ?_
    filter_upwards [hA] with i hi
    have hw : wfam i = w'.changeRing (ev i hi) := by simp only [wfam, hi, ↓reduceDIte]
    rw [hw, affineSchemePointEquiv_changeRing]
    change f i = ev i hi (AlgPoint.toAlgHom (affineSchemePointEquiv K c.scheme B w') t)
    rw [← hf]
    rfl
  have hcont := @Continuous.tendsto _ _ (schemePointTopology K c.scheme K)
    (etaleChartTopology K X') _ c.continuous_pointMap z₀
  refine (hcont.comp hwt).congr' ?_
  filter_upwards [hA] with i hi
  have hw : wfam i = w'.changeRing (ev i hi) := by simp only [wfam, hi, ↓reduceDIte]
  change c.pointMap (wfam i) = p i
  rw [hw]
  exact hcomp i hi

end Spreading

section Tower

/-- The spectrum of a scalar tower. -/
theorem spec_algebraMap_tower (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.algebraMap R A = Spec.algebraMap R B := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The generic test object of the valuative statement for a tower `R → A → B`. -/
abbrev towerTest : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ (ringTest R A).hom)

/-- The identification of the generic test object with the test scheme of `B`. -/
def towerHom : towerTest R A B ⟶ ringTest R B :=
  Over.homMk (𝟙 (Spec (CommRingCat.of B))) (by
    change 𝟙 (Spec (CommRingCat.of B)) ≫ Spec.algebraMap R B =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.algebraMap R A
    rw [Category.id_comp, spec_algebraMap_tower])

/-- Its inverse. -/
def towerInv : ringTest R B ⟶ towerTest R A B :=
  Over.homMk (𝟙 (Spec (CommRingCat.of B))) (by
    change 𝟙 (Spec (CommRingCat.of B)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.algebraMap R A) = Spec.algebraMap R B
    rw [Category.id_comp, spec_algebraMap_tower])

theorem towerInv_comp_towerHom : towerInv R A B ≫ towerHom R A B = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (CommRingCat.of B)) ≫ 𝟙 (Spec (CommRingCat.of B)) = 𝟙 (Spec (CommRingCat.of B))
  exact Category.id_comp _

/-- The restriction map of the valuative statement factors through the identification. -/
theorem homMk_eq_towerHom_comp :
    (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) rfl :
        towerTest R A B ⟶ Over.mk (ringTest R A).hom) =
      towerHom R A B ≫ ringTestMap R (IsScalarTower.toAlgHom R A B) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap A B)) = 𝟙 (Spec (CommRingCat.of B)) ≫
    Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom R A B).toRingHom)
  rw [Category.id_comp]
  rfl

end Tower

section Core

variable {K : Type u} [NontriviallyNormedField K] [LocallyCompactSpace K] [CompleteSpace K]

omit [LocallyCompactSpace K] [CompleteSpace K] in
/-- A space of finite type is locally of finite type over the base. -/
theorem locallyOfFiniteTypeOverBase_of_finiteType {X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (h : FiniteTypeOverRing K X') : LocallyOfFiniteTypeOverBase X' := by
  obtain ⟨U, a, ha, hs, hU⟩ := h
  exact ⟨U, a, ha, hs, hU.1⟩

/-- **Limits in the fibre product.** Let `f : X ⟶ Y` be quasi-compact, separated and universally
closed, let `d` be an affine étale chart of `Y`, and let `p` be a family of rational points of
`X ×_Y h_V` whose chart coordinates converge to `v₀` along `𝒰`. Then `p` converges to a rational
point of `X ×_Y h_V` over `v₀`. -/
theorem exists_limit_fibre (hVC : SpaceValuativeExistenceStatement.{u})
    (hnd : ¬ DiscreteTopology K)
    {X Y : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (huc : IsUniversallyClosedMorphism f) (hX : LocallyOfFiniteTypeOverBase X)
    {V : Over (Spec (CommRingCat.of K))} [IsAffine V.left]
    [_root_.AlgebraicGeometry.IsSeparated V.hom]
    (g : (schemeYoneda _).obj V ⟶ Y.presheaf) (hg : IsEtale g)
    {I : Type u} (𝒰 : Ultrafilter I)
    (p : I → RingPoints K (ChartFibre.space f g hsep hqc) K)
    (v₀ : RingPoint K V K)
    (hp : Tendsto (fun i => ((p i).1.2.down : RingPoint K V K)) 𝒰
      (@nhds _ (schemePointTopology K V K) v₀)) :
    ∃ x' : RingPoints K (ChartFibre.space f g hsep hqc) K,
      (x'.1.2.down : RingPoint K V K) = v₀ ∧
        @Tendsto I _ p 𝒰
          (@nhds _ (etaleChartTopology K (ChartFibre.space f g hsep hqc)) x') := by
  classical
  let X' := ChartFibre.space f g hsep hqc
  have hX'sep : IsSeparated X' := ChartFibre.isSeparated_space f g hsep hqc
  have hX'ft : FiniteTypeOverRing K X' :=
    ChartFibre.finiteTypeOverRing_space f g hX hg hsep hqc
  let G := ultrapowerMap K 𝒰
  let O := convergentGerms K 𝒰 hnd
  let ι := IsScalarTower.toAlgHom K O (UltrapowerField K 𝒰)
  let ρ := standardPart K 𝒰 hnd
  -- the product point
  have : IsAdicComplete (IsLocalRing.maximalIdeal K) K := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  obtain ⟨P, hPp⟩ := SpaceProductPoints.separatedProductPoints_surjective hX'sep hX'ft I
    (fun _ => K) p
  have hP : ∀ i, RingPoints.changeRing (Pi.evalAlgHom K (fun _ => K) i) P = p i :=
    fun i => congrFun hPp i
  let PV : RingPoint K V (I → K) := P.1.2.down
  have hPV : ∀ i, PV.changeRing (Pi.evalAlgHom K (fun _ => K) i) = (p i).1.2.down :=
    fun i => congrArg (fun q => q.1.2.down) (hP i)
  obtain ⟨vO, hvO₁, hvO₂⟩ := exists_convergentGerm_point 𝒰 hnd PV v₀ (by
    simp only [hPV]
    exact hp)
  -- the valuative square
  let ξ : RingPoints K X' (UltrapowerField K 𝒰) := RingPoints.changeRing G P
  let s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of K) := (ringTest K O).hom
  let j := towerHom K O (UltrapowerField K 𝒰)
  let xV : X.sections (towerTest K O (UltrapowerField K 𝒰)) := X.pullback j ξ.1.1
  let vO' : ringTest K O ⟶ V := vO
  let vU : ((schemeYoneda _).obj V).obj (op (ringTest K O)) := ULift.up vO'
  let yV : Y.sections (ringTest K O) := g.app _ vU
  have he : ξ.1.2 = ((schemeYoneda _).obj V).map (ringTestMap K ι).op vU := by
    change ULift.up (ringTestMap K G ≫ PV) = ULift.up (ringTestMap K ι ≫ vO)
    exact congrArg ULift.up hvO₁.symm
  have hyV : g.app _ ξ.1.2 = Y.pullback (ringTestMap K ι) yV := by
    rw [he]
    exact NatTrans.naturality_apply g (ringTestMap K ι).op vU
  have hsq : mapSections f (towerTest K O (UltrapowerField K 𝒰)) xV =
      Y.pullback (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap O (UltrapowerField K 𝒰))))
        rfl) yV := by
    rw [homMk_eq_towerHom_comp, pullback_comp, ← hyV, ← ξ.2]
    exact (mapSections_naturality f j ξ.1.1).symm
  obtain ⟨a, ha₁, ha₂⟩ := hVC (Spec (CommRingCat.of K)) X Y f hqc hsep huc O
    (UltrapowerField K 𝒰) (ringTest K O).hom xV yV hsq
  -- the convergent-germ point of the fibre product
  let a₀ : X.sections (ringTest K O) := a
  have ha₂' : (hom f).app _ a₀ = g.app _ vU := ha₂
  let a' : RingPoints K X' O := ⟨(a₀, vU), ha₂'⟩
  have hinj : ∀ z₁ z₂ : X.sections (ringTest K (UltrapowerField K 𝒰)),
      X.pullback j z₁ = X.pullback j z₂ → z₁ = z₂ := fun z₁ z₂ h => by
    have h' := congrArg (X.pullback (towerInv K O (UltrapowerField K 𝒰))) h
    rwa [← pullback_comp, ← pullback_comp, towerInv_comp_towerHom, pullback_id,
      pullback_id] at h'
  have hξ : RingPoints.changeRing ι a' = ξ := by
    apply Subtype.ext
    apply Prod.ext
    · apply hinj
      change X.pullback j (X.pullback (ringTestMap K ι) a₀) = X.pullback j ξ.1.1
      rw [← pullback_comp, ← homMk_eq_towerHom_comp]
      exact ha₁
    · exact he.symm
  let x' : RingPoints K X' K := RingPoints.changeRing ρ a'
  have hx'v : (x'.1.2.down : RingPoint K V K) = v₀ := hvO₂
  -- an affine chart at the limit and a henselian lift
  obtain ⟨c, w₀, hcaff, hw₀⟩ := exists_affine_chart_pointMap_eq
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX'sep)
    (locallyOfFiniteTypeOverBase_of_finiteType hX'ft) x'
  have : IsAffine c.scheme.left := hcaff
  let ac : (schemeYoneda _).obj c.scheme ⟶ X'.presheaf := hom c.hom
  have hac : IsEtale ac := c.isEtale
  have : HenselianLocalRing O := convergentGerms_henselian
  let _ : Algebra O K := ρ.toRingHom.toAlgebra
  have : IsScalarTower K O K := IsScalarTower.of_algebraMap_eq fun x => (ρ.commutes x).symm
  have hρs : Function.Surjective (algebraMap O K) := fun x => ⟨algebraMap K O x, ρ.commutes x⟩
  have hū : (schemeYoneda _).map w₀ ≫ ac =
      (schemeYoneda _).map (ringTestMap K (IsScalarTower.toAlgHom K O K)) ≫
        uliftYonedaEquiv.{u + 1}.symm a' := by
    change (schemeYoneda _).map w₀ ≫ hom c.hom = _
    rw [comp_eq_pointMap, hw₀, ← ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]
    rfl
  obtain ⟨z₁, hz⟩ := ProductPointsLocalLift.exists_point_of_field_point ac hac hρs a' w₀ hū
  let z : RingPoint K c.scheme O := z₁
  have hz' : (schemeYoneda _).map (z.changeRing ι) ≫ hom c.hom =
      uliftYonedaEquiv.{u + 1}.symm (RingPoints.changeRing G P) := by
    change (schemeYoneda _).map (ringTestMap K ι ≫ z₁) ≫ ac = _
    rw [Functor.map_comp, Category.assoc, hz,
      ← ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing, hξ]
  have hlim := tendsto_of_chart_lift 𝒰 hnd c p P hP z hz'
  have hpt : c.pointMap (z.changeRing ρ) = x' := by
    apply pointMap_eq_of_comp
    change (schemeYoneda _).map (ringTestMap K ρ ≫ z₁) ≫ ac = _
    rw [Functor.map_comp, Category.assoc, hz,
      ← ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]
  refine ⟨x', hx'v, ?_⟩
  rw [← hpt]
  exact hlim

end Core

section Main

/-- **Corollary 5.6 from the valuative lift.** The valuative existence criterion for separated
quasi-compact universally closed morphisms of algebraic spaces implies Conrad's Corollary 5.6
for algebraic spaces. -/
theorem localFieldProperPointMap_of_valuative (hVC : SpaceValuativeExistenceStatement.{u}) :
    LocalFieldProperPointMapStatement.{u} := by
  intro K _ _ X Y f hXqs hXlft hYqs hYlft hf
  obtain ⟨hsep, hqc, -, huc⟩ := hf
  have : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have hK : IsHenselianValuedField K := completeHenselianValuedField K
  have hnd : ¬ DiscreteTopology K := by
    intro h
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
    exact (not_lt_of_ge (NormedDivisionRing.norm_le_one_of_discrete x)) hx
  let _ : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let _ : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  refine isProperMap_iff_ultrafilter.mpr
    ⟨continuous_ringPointsMap hK ⟨hYqs, hYlft⟩ f, fun 𝒰 y hy => ?_⟩
  -- an affine chart of the target at the limit
  obtain ⟨d, v₀, hdaff, hdv⟩ := exists_affine_chart_pointMap_eq hYqs hYlft y
  have : IsAffine d.scheme.left := hdaff
  have : LocallyOfFiniteType d.scheme.hom := d.locallyOfFiniteType
  let g : (schemeYoneda _).obj d.scheme ⟶ Y.presheaf := hom d.hom
  have hg : IsEtale g := d.isEtale
  have hdv' : schemePointsMap g v₀ = y := hdv
  let X' := ChartFibre.space f g hsep hqc
  let _ : TopologicalSpace (RingPoints K X' K) := etaleChartTopology K X'
  let _ : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K d.scheme K
  -- lift the ultrafilter to the fibre product
  have hopen : IsOpenMap (schemePointsMap g) := isOpenMap_schemePointsMap hK g hg
  let sndV : RingPoints K X' K → RingPoint K d.scheme K := fun q => q.1.2.down
  let fstX : RingPoints K X' K → RingPoints K X K := fun q => q.1.1
  obtain ⟨𝒲, h𝒲₁, h𝒲₂⟩ := exists_ultrafilter_lift (RingPoints.map (A := K) f)
    (schemePointsMap g) fstX sndV
    (fun a b h => ⟨⟨(a, ULift.up (show PointTopology.ringTest K K ⟶ d.scheme from b)), h⟩,
      rfl, rfl⟩) 𝒰 v₀
    (fun N hN => hopen.image_mem_nhds hN) (by rw [hdv']; exact hy)
  -- index the lifted ultrafilter by a small type
  have hX'sep : IsSeparated X' := ChartFibre.isSeparated_space f g hsep hqc
  have hX'ft : FiniteTypeOverRing K X' := ChartFibre.finiteTypeOverRing_space f g hXlft hg hsep hqc
  obtain ⟨U, a, hU, ha, hs⟩ := SpaceProductPoints.exists_affine_atlas hX'ft
  have : IsAffine U.left := hU
  have : Small.{u} (RingPoints K X' K) := RingPointsSmall.small_ringPoints
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hX'sep) a ha hs
  let e : Shrink.{u} (RingPoints K X' K) ≃ RingPoints K X' K := (equivShrink _).symm
  let 𝒰I : Ultrafilter (Shrink.{u} (RingPoints K X' K)) := 𝒲.map e.symm
  have hmap : Filter.map e (𝒰I : Filter _) = (𝒲 : Filter _) := by
    rw [Ultrafilter.coe_map, Filter.map_map, Equiv.self_comp_symm, Filter.map_id]
  have hp : Tendsto (sndV ∘ e) 𝒰I (@nhds _ (schemePointTopology K d.scheme K) v₀) := by
    rw [← Filter.tendsto_map'_iff, hmap]
    exact h𝒲₂
  obtain ⟨x', hx'v, hx'⟩ := exists_limit_fibre hVC hnd f hsep hqc huc hXlft g hg 𝒰I
    (fun i => e i) v₀ hp
  have h𝒲x : (𝒲 : Filter _) ≤ 𝓝 x' := by
    rw [← hmap]
    exact hx'
  have hcont : Continuous fstX :=
    continuous_ringPointsMap hK ⟨hXqs, hXlft⟩ (ChartFibre.pr₁ f g hsep hqc)
  refine ⟨fstX x', ?_, ?_⟩
  · change (hom f).app _ x'.1.1 = y
    rw [x'.2]
    have hv : sndV x' = v₀ := hx'v
    change schemePointsMap g (sndV x') = y
    rw [hv, hdv']
  · rw [← h𝒲₁, Ultrafilter.coe_map]
    exact (hcont.tendsto x').mono_left h𝒲x

end Main

end LocalFieldProperPointLimit

end Langlands.AlgebraicGeometry.AlgebraicSpace
