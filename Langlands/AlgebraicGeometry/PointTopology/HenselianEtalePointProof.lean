import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.Topology.SeparatedMap
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-!
# Proof of the henselian assertions on Conrad's printed p.14
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IntermediateField
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section SeparablyClosed

variable (K : Type u) [NontriviallyNormedField K]

local notation "K̂" => UniformSpace.Completion K

/-- A henselian valued field is separably closed in its completion. -/
theorem separableClosure_completion_eq_bot (hK : IsHenselianValuedField K) :
    separableClosure K K̂ = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [mem_separableClosure_iff] at hx
  rw [IntermediateField.mem_bot]
  by_contra hne
  have hint : IsIntegral K x := hx.isIntegral
  have hdeg : 2 ≤ (minpoly K x).natDegree := by
    have h1 := minpoly.natDegree_pos hint
    have h2 : (minpoly K x).natDegree ≠ 1 := by
      intro h
      exact hne ((minpoly.natDegree_eq_one_iff).mp h)
    omega
  let Ω := AlgebraicClosure K
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := Ω) hx
    (IsAlgClosed.splits _)
  obtain ⟨r₁, r₂, hr⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
    1 < Fintype.card ((minpoly K x).rootSet Ω))
  have hroot : ∀ r : (minpoly K x).rootSet Ω, (r : Ω) ∈ (minpoly K x).aroots Ω := by
    intro r
    have := (Polynomial.mem_rootSet.mp r.property)
    exact Polynomial.mem_aroots.mpr ⟨this.1, this.2⟩
  let L := K⟮x⟯
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hint
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let σ₁ : L →ₐ[K] Ω := (IntermediateField.algHomAdjoinIntegralEquiv K hint).symm
    ⟨r₁, hroot r₁⟩
  let σ₂ : L →ₐ[K] Ω := (IntermediateField.algHomAdjoinIntegralEquiv K hint).symm
    ⟨r₂, hroot r₂⟩
  let g : L := IntermediateField.AdjoinSimple.gen K x
  have hσ₁ : σ₁ g = r₁ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen K hint _
  have hσ₂ : σ₂ g = r₂ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen K hint _
  obtain ⟨w, hw, -⟩ := hK Ω
  obtain ⟨v, -, huniq⟩ := hK L
  let v₀ : AbsoluteValue L ℝ :=
    (NormedField.toAbsoluteValue K̂).comp (f := (L.val : L →+* K̂)) Subtype.val_injective
  have hv₀ : ∀ k : K, v₀ (algebraMap K L k) = ‖k‖ := by
    intro k
    change ‖algebraMap K K̂ k‖ = ‖k‖
    exact UniformSpace.Completion.norm_coe k
  have hσ : ∀ σ : L →ₐ[K] Ω, w.comp (f := (σ : L →+* Ω)) σ.injective = v₀ := by
    intro σ
    have h₁ : ∀ k : K, (w.comp (f := (σ : L →+* Ω)) σ.injective) (algebraMap K L k) = ‖k‖ := by
      intro k
      change w (σ (algebraMap K L k)) = ‖k‖
      rw [AlgHom.commutes]
      exact hw k
    exact (huniq _ h₁).trans (huniq _ hv₀).symm
  have hv₁ : ∀ z : L, w (σ₁ z) = v₀ z := fun z =>
    congrArg (fun v : AbsoluteValue L ℝ => v z) (hσ σ₁)
  have hv₂ : ∀ z : L, w (σ₂ z) = v₀ z := fun z =>
    congrArg (fun v : AbsoluteValue L ℝ => v z) (hσ σ₂)
  have hbound : ∀ ε > (0 : ℝ), w ((r₁ : Ω) - r₂) ≤ 2 * ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe x ε hε
    have hgk : v₀ (g - algebraMap K L k) < ε := by
      change ‖x - algebraMap K K̂ k‖ < ε
      rw [← dist_eq_norm]
      exact hk
    have hkg : v₀ (algebraMap K L k - g) < ε := by
      rw [AbsoluteValue.map_sub]
      exact hgk
    calc w ((r₁ : Ω) - r₂)
        = w ((σ₁ g - σ₁ (algebraMap K L k)) + (σ₂ (algebraMap K L k) - σ₂ g)) := by
          rw [hσ₁, hσ₂, AlgHom.commutes, AlgHom.commutes]
          congr 1
          ring
      _ ≤ w (σ₁ g - σ₁ (algebraMap K L k)) + w (σ₂ (algebraMap K L k) - σ₂ g) :=
          w.add_le _ _
      _ = v₀ (g - algebraMap K L k) + v₀ (algebraMap K L k - g) := by
          rw [← map_sub, ← map_sub, hv₁, hv₂]
      _ ≤ 2 * ε := by linarith
  have hzero : w ((r₁ : Ω) - r₂) = 0 := by
    apply le_antisymm _ (w.nonneg _)
    by_contra hpos
    push Not at hpos
    have := hbound (w ((r₁ : Ω) - r₂) / 4) (by positivity)
    linarith
  apply hr
  apply Subtype.ext
  exact sub_eq_zero.mp ((w.eq_zero).mp hzero)

/-- The first assertion of `HenselianEtalePointStatement`. -/
theorem henselianSeparablyClosedInCompletion :
    HenselianSeparablyClosedInCompletionStatement.{u} := by
  intro K _ hK
  exact separableClosure_completion_eq_bot K hK

end SeparablyClosed

section CoefficientEmbedding

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- A local coefficient homomorphism preserves the closed-point image of an actual
point. -/
theorem changeRing_left_closedPoint [IsLocalRing S] [IsLocalRing T]
    {X : Over (Spec (CommRingCat.of R))} (f : S →ₐ[R] T) [IsLocalHom f.toRingHom]
    (p : RingPoint R X S) :
    (RingPoint.changeRing f p).left (IsLocalRing.closedPoint T) =
      p.left (IsLocalRing.closedPoint S) := by
  have key : ∀ q : ringTest R S ⟶ X, (ringTestMap R f ≫ q).left (IsLocalRing.closedPoint T) =
      q.left (IsLocalRing.closedPoint S) := by
    intro q
    exact congrArg q.left (IsLocalRing.comap_closedPoint f.toRingHom)
  exact key p

variable [TopologicalSpace S] [TopologicalSpace T]
variable [IsLocalRing S] [IsLocalRing T] [ContinuousMul T] [IsOpenUnits T]

/-- A local topological embedding of value rings gives a topological embedding of
actual scheme points, for arbitrary relative schemes. -/
theorem isEmbedding_schemeChangeRing
    (X : Over (Spec (CommRingCat.of R))) (f : S →ₐ[R] T) [IsLocalHom f.toRingHom]
    (hf : IsEmbedding f) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R X T) := schemePointTopology R X T
    IsEmbedding (RingPoint.changeRing (X := X) f) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R X T) := schemePointTopology R X T
  let e : RingPoint R X S → RingPoint R X T := RingPoint.changeRing (X := X) f
  have hchart : ∀ U : X.left.affineOpens,
      IsEmbedding (RingPoint.changeRing (X := openOver R X U.val) f) := fun U =>
    (affineSchemeCoefficientEmbeddings_proof R S T (openOver R X U.val) f).1 hf
  have hcomm : ∀ (U : X.left.Opens) (q : RingPoint R (openOver R X U) S),
      openPointMap R X T U (RingPoint.changeRing f q) = e (openPointMap R X S U q) :=
    fun U q => (congrFun (changeRing_openPointMap R S T X U f) q).symm
  have hlift : ∀ (U : X.left.Opens) (p : RingPoint R X S)
      (r : RingPoint R (openOver R X U) T), openPointMap R X T U r = e p →
        ∃ q : RingPoint R (openOver R X U) S, openPointMap R X S U q = p := by
    intro U p r hr
    have hU : p.left (IsLocalRing.closedPoint S) ∈ U := by
      rw [← changeRing_left_closedPoint R S T f p]
      change (e p).left (IsLocalRing.closedPoint T) ∈ U
      rw [← hr]
      exact (r.left (IsLocalRing.closedPoint T)).property
    exact ⟨openPointLift R X S U p ((range_subset_open_iff_closedPoint R X S U p).mpr hU),
      openPointMap_lift R X S U p _⟩
  have hinj : Function.Injective e := by
    intro p p' h
    obtain ⟨U, q, rfl⟩ := exists_affineOpenPoint R X S p
    obtain ⟨q', rfl⟩ := hlift U.val p' (RingPoint.changeRing f q) ((hcomm U.val q).trans h)
    have h' : openPointMap R X T U.val (RingPoint.changeRing f q) =
        openPointMap R X T U.val (RingPoint.changeRing f q') :=
      (hcomm U.val q).trans (h.trans (hcomm U.val q').symm)
    exact congrArg (openPointMap R X S U.val)
      ((hchart U).injective (openPointMap_injective R X T U.val h'))
  have hcont : Continuous e := schemeCoefficientContinuity_proof R S T X f hf.continuous
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hWU : ∀ U : X.left.affineOpens,
      ∃ t : Set (RingPoint R (openOver R X U.val) T), IsOpen t ∧
        RingPoint.changeRing f ⁻¹' t = openPointMap R X S U.val ⁻¹' W := fun U =>
    (hchart U).isInducing.isOpen_iff.mp ((schemePointTopology_isOpen_iff R X S W).mp hW U)
  choose t ht hte using hWU
  refine isOpen_induced_iff.mpr ⟨⋃ U, openPointMap R X T U.val '' t U, ?_, ?_⟩
  · exact isOpen_iUnion fun U =>
      (isOpenEmbedding_schemeAffineChart R T X U).isOpenMap _ (ht U)
  · ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨U, r, hrt, hr⟩
      obtain ⟨q, rfl⟩ := hlift U.val p r hr
      have hqr : RingPoint.changeRing f q = r :=
        openPointMap_injective R X T U.val ((hcomm U.val q).trans hr.symm)
      have hq : q ∈ RingPoint.changeRing f ⁻¹' t U := by
        rw [Set.mem_preimage, hqr]
        exact hrt
      rw [hte U] at hq
      exact hq
    · intro hp
      obtain ⟨U, q, rfl⟩ := exists_affineOpenPoint R X S p
      refine ⟨U, RingPoint.changeRing f q, ?_, hcomm U.val q⟩
      change q ∈ RingPoint.changeRing f ⁻¹' t U
      rw [hte U]
      exact hp

end CoefficientEmbedding

section FibreRationality

/-- Over a field separably closed in an extension field, every extension-valued
point of an unramified scheme over a rational point is itself rational. -/
theorem exists_lift_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (k L : Type u) [Field k] [Field L] [Algebra k L] (hk : separableClosure k L = ⊥)
    (q : Spec (CommRingCat.of L) ⟶ X) (y : Spec (CommRingCat.of k) ⟶ Y)
    (h : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ y) :
    ∃ l : Spec (CommRingCat.of k) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ l = q := by
  obtain ⟨⟨s, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Y).symm.surjective y
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective q
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at h ⊢
  have h' : (Scheme.SpecToEquivOfField L Y).symm ⟨f x, f.residueFieldMap x ≫ φ⟩ =
      (Scheme.SpecToEquivOfField L Y).symm ⟨s, a ≫ CommRingCat.ofHom (algebraMap k L)⟩ := by
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Spec.map_comp,
      Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Category.assoc, h]
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    ((Scheme.SpecToEquivOfField L Y).symm.injective h')
  dsimp only at e he
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have hcomp : (algebraMap k L).comp a.hom = φ.hom.comp (f.residueFieldMap x).hom := by
    have := congrArg CommRingCat.Hom.hom he
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
    exact this.symm
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hsep : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := inferInstance
  have hmem : ∀ z : X.residueField x, φ.hom z ∈ (⊥ : IntermediateField k L) := by
    intro z
    rw [← hk, mem_separableClosure_iff]
    let P := minpoly (Y.residueField (f x)) z
    have hP : P.Separable := Algebra.IsSeparable.isSeparable _ z
    have hroot : Polynomial.aeval (φ.hom z) (P.map a.hom) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂]
      have h0 : Polynomial.eval₂ (f.residueFieldMap x).hom z P = 0 := minpoly.aeval _ z
      rw [h0, map_zero]
    exact (hP.map).of_dvd (minpoly.dvd k (φ.hom z) hroot)
  let φ₀ : X.residueField x →+* k :=
    (IntermediateField.botEquiv k L).toAlgHom.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hφ₀ : (algebraMap k L).comp φ₀ = φ.hom := by
    ext z
    change algebraMap k L (IntermediateField.botEquiv k L ⟨φ.hom z, hmem z⟩) = φ.hom z
    obtain ⟨c, hc⟩ := (IntermediateField.botEquiv k L).symm.surjective ⟨φ.hom z, hmem z⟩
    rw [← hc, AlgEquiv.apply_symm_apply]
    rw [IntermediateField.botEquiv_symm] at hc
    exact congrArg Subtype.val hc
  refine ⟨Spec.map (CommRingCat.ofHom φ₀) ≫ X.fromSpecResidueField x, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ₀]
  rfl

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The relative form: an `L`-point of an unramified relative scheme lying over a
rational point is the coefficient change of a rational point. -/
theorem exists_changeRing_eq_of_formallyUnramified (hk : separableClosure k L = ⊥)
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) [FormallyUnramified f.left]
    [LocallyOfFiniteType f.left] (q : RingPoint k X L) (y : RingPoint k Y k)
    (h : q ≫ f = RingPoint.changeRing (Algebra.ofId k L) y) :
    ∃ p : RingPoint k X k, RingPoint.changeRing (Algebra.ofId k L) p = q := by
  have hleft : q.left ≫ f.left =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ y.left :=
    congrArg (fun z : RingPoint k Y L => z.left) h
  obtain ⟨l, hl⟩ := exists_lift_of_formallyUnramified f.left k L hk q.left y.left hleft
  have hbase : l ≫ X.hom = Spec.algebraMap k k := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (l ≫ X.hom)
    rw [← hα]
    have h₁ : Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ Spec.map α =
        Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
      rw [hα, ← Category.assoc, hl]
      exact Over.w q
    rw [← Spec.map_comp] at h₁
    have h₂ := Spec.map_injective h₁
    congr 1
    ext c
    have h₃ := congrArg (fun φ => φ.hom c) h₂
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h₃
    exact (algebraMap k L).injective h₃
  refine ⟨Over.homMk l hbase, ?_⟩
  apply RingPoint.ext
  exact hl

end FibreRationality

section LocalInjectivity

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- An unramified locally finite type morphism is locally injective on actual points:
its diagonal is an open immersion. -/
theorem isLocallyInjective_schemePointMap
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [FormallyUnramified f.left]
    [LocallyOfFiniteType f.left] :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    IsLocallyInjective (X := RingPoint R X S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let c := relativeSchemePullback R f f
  let hc := relativeSchemePullbackIsLimit R f f
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  let Δ : X ⟶ c.pt := Over.homMk (pullback.diagonal f.left) (by
    change pullback.diagonal f.left ≫ pullback.fst f.left f.left ≫ X.hom = X.hom
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp])
  have : IsOpenImmersion Δ.left := inferInstanceAs (IsOpenImmersion (pullback.diagonal f.left))
  have hΔ := isOpenEmbedding_schemePointMap R S Δ
  have hfst : Δ ≫ c.fst = 𝟙 X := by
    apply Over.OverMorphism.ext
    exact pullback.diagonal_fst f.left
  have hsnd : Δ ≫ c.snd = 𝟙 X := by
    apply Over.OverMorphism.ext
    exact pullback.diagonal_snd f.left
  let H := schemePullbackPointHomeomorph R S c hc
  have hH : ∀ p : RingPoint R X S, (H (p ≫ Δ)).val = (p, p) := by
    intro p
    dsimp only [RingPoint] at p
    change ((p ≫ Δ) ≫ c.fst, (p ≫ Δ) ≫ c.snd) = (p, p)
    rw [Category.assoc, Category.assoc, hfst, hsnd, Category.comp_id]
  rw [isLocallyInjective_iff_isOpen_diagonal]
  have hdiag : Function.pullbackDiagonal (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) =
      H '' Set.range (fun p : RingPoint R X S => (p ≫ Δ : RingPoint R c.pt S)) := by
    ext z
    constructor
    · intro hz
      refine ⟨z.val.1 ≫ Δ, ⟨z.val.1, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [hH]
      exact Prod.ext rfl hz
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      change (H (p ≫ Δ)).val.1 = (H (p ≫ Δ)).val.2
      rw [hH]
  rw [hdiag]
  exact H.isOpenMap _ hΔ.isOpen_range

end LocalInjectivity

section Henselian

variable (K : Type u) [NontriviallyNormedField K]

local notation "K̂" => UniformSpace.Completion K

/-- The completion of a nontrivially normed field, as a nontrivially normed field. -/
abbrev completionNontriviallyNormedField : NontriviallyNormedField K̂ where
  __ : NormedField K̂ := inferInstance
  non_trivial := by
    obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
    exact ⟨k, by rw [UniformSpace.Completion.norm_coe]; exact hk⟩

/-- Smooth maps are open on points with values in the completion. -/
theorem isOpenMap_completionSmoothPointMap
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) [Smooth f.left] :
    letI : TopologicalSpace (RingPoint K X K̂) := schemePointTopology K X K̂
    letI : TopologicalSpace (RingPoint K Y K̂) := schemePointTopology K Y K̂
    IsOpenMap (X := RingPoint K X K̂) (Y := RingPoint K Y K̂)
      (fun p : RingPoint K X K̂ => (p ≫ f : RingPoint K Y K̂)) := by
  let : TopologicalSpace (RingPoint K X K̂) := schemePointTopology K X K̂
  let : TopologicalSpace (RingPoint K Y K̂) := schemePointTopology K Y K̂
  let : TopologicalSpace (RingPoint K̂ (ringBaseChange K K̂ X) K̂) :=
    schemePointTopology K̂ (ringBaseChange K K̂ X) K̂
  let : TopologicalSpace (RingPoint K̂ (ringBaseChange K K̂ Y) K̂) :=
    schemePointTopology K̂ (ringBaseChange K K̂ Y) K̂
  let g : ringBaseChange K K̂ X ⟶ ringBaseChange K K̂ Y :=
    (Over.pullback (Spec.algebraMap K K̂)).map f
  have : Smooth g.left := MorphismProperty.overPullbackMap (P := @Smooth)
    (Spec.algebraMap K K̂) f inferInstance
  have hX := schemeBaseChangeTopology_proof K K̂ K̂ X
  have hY := schemeBaseChangeTopology_proof K K̂ K̂ Y
  have hg : IsOpenMap (X := RingPoint K̂ (ringBaseChange K K̂ X) K̂)
      (Y := RingPoint K̂ (ringBaseChange K K̂ Y) K̂)
      (fun p : RingPoint K̂ (ringBaseChange K K̂ X) K̂ =>
      (p ≫ g : RingPoint K̂ (ringBaseChange K K̂ Y) K̂)) := by
    let := completionNontriviallyNormedField K
    exact isOpenMap_smoothSchemePointMap K̂ g
  intro W hW
  have hset : (fun p : RingPoint K X K̂ => (p ≫ f : RingPoint K Y K̂)) '' W =
      ringPointBaseChangeEquiv K K̂ K̂ Y ⁻¹'
        ((fun p => (p ≫ g : RingPoint K̂ (ringBaseChange K K̂ Y) K̂)) ''
          (ringPointBaseChangeEquiv K K̂ K̂ X '' W)) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, (ringPointBaseChangeEquiv_natural K K̂ K̂ f p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, hy⟩
      refine ⟨p, hp, (ringPointBaseChangeEquiv K K̂ K̂ Y).injective ?_⟩
      exact (ringPointBaseChangeEquiv_natural K K̂ K̂ f p).trans hy
  exact (congrArg (IsOpen (X := RingPoint K Y K̂)) hset).mpr
    ((hg _ (hX.isOpenMap _ hW)).preimage hY.continuous)

/-- Over a henselian valued field, an étale map is open on rational points. -/
theorem isOpenMap_henselianEtalePointMap (hK : IsHenselianValuedField K)
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) [Etale f.left] :
    letI : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
    letI : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
    IsOpenMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  let : TopologicalSpace (RingPoint K X K̂) := schemePointTopology K X K̂
  let : TopologicalSpace (RingPoint K Y K̂) := schemePointTopology K Y K̂
  have hsep := separableClosure_completion_eq_bot K hK
  let ι : K →ₐ[K] K̂ := Algebra.ofId K K̂
  have hι : IsEmbedding ι := (UniformSpace.Completion.isUniformEmbedding_coe K).isEmbedding
  have heX := isEmbedding_schemeChangeRing K K K̂ X ι hι
  have heY := isEmbedding_schemeChangeRing K K K̂ Y ι hι
  have hopen := isOpenMap_completionSmoothPointMap K f
  intro W hW
  obtain ⟨Ŵ, hŴ, rfl⟩ := heX.isInducing.isOpen_iff.mp hW
  have hset : (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) ''
        (RingPoint.changeRing ι ⁻¹' Ŵ) =
      RingPoint.changeRing ι ⁻¹'
        ((fun p : RingPoint K X K̂ => (p ≫ f : RingPoint K Y K̂)) '' Ŵ) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨RingPoint.changeRing ι p, hp, Category.assoc _ _ _⟩
    · rintro ⟨q, hq, hqy⟩
      obtain ⟨p, rfl⟩ := exists_changeRing_eq_of_formallyUnramified K K̂ hsep f q y hqy
      refine ⟨p, hq, heY.injective ?_⟩
      exact (Category.assoc _ _ _).symm.trans hqy
  exact (congrArg (IsOpen (X := RingPoint K Y K)) hset).mpr
    ((hopen Ŵ hŴ).preimage heY.continuous)

/-- The second assertion of `HenselianEtalePointStatement`: Conrad's Lemma 5.3. -/
theorem henselianEtalePointLocalHomeomorph :
    HenselianEtalePointLocalHomeomorphStatement.{u} := by
  intro K _ hK X Y _ _ f _
  let : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  let g : RingPoint K X K → RingPoint K Y K := fun p => p ≫ f
  change IsLocalHomeomorph g
  have hcont : Continuous g := schemePointContinuity_proof K K X Y f
  have hopen : IsOpenMap g := isOpenMap_henselianEtalePointMap K hK f
  have hinj : IsLocallyInjective g := isLocallyInjective_schemePointMap K K f
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨U, hU, hxU, hinjU⟩ := hinj x
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hcont.comp continuous_subtype_val)
    (fun a b hab => Subtype.ext (hinjU a.property b.property hab))
    (hopen.domRestrict hU)

/-- Both henselian assertions of Conrad's printed p.14. -/
theorem henselianEtalePoint : HenselianEtalePointStatement.{u} :=
  ⟨henselianSeparablyClosedInCompletion, henselianEtalePointLocalHomeomorph⟩

end Henselian

end Langlands.AlgebraicGeometry.PointTopology
