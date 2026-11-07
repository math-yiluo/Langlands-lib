import Langlands.GroupScheme.HomScheme.TorusChartOpen
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartStatements
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartAffineTestsProof
import Langlands.Algebra.FiniteSubcomodule
import Mathlib.RingTheory.Smooth.Flat

/-! # The window charts cover the field points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

/-- An algebra with a prime ideal has a point with values in a field. -/
theorem Langlands.GroupScheme.HomScheme.TorusChart.exists_fieldPoint {R : Type u} [CommRing R]
    {C : Type u} [CommRing C] [Algebra R C] (P : Ideal C) [P.IsPrime] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra R K), Nonempty (C →ₐ[R] K) :=
  ⟨P.ResidueField, inferInstance, inferInstance, ⟨IsScalarTower.toAlgHom R C _⟩⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.TorusChart

open Langlands.Algebra Langlands.Algebra.TorusChartRing Langlands.Algebra.TorusChartAlgebra

section Lift

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → A} {n : ℕ} (d : Datum R A r m gen n)

open TorusChartExistence in
/-- A field point of `W_f` at which `N` does not vanish extends to `B_f`. -/
theorem exists_lift_Bf {K : Type u} [Field K] [Algebra R K] (y : Localization.Away d.f →ₐ[R] K)
    (hy : y (algebraMap (W R A r m) (Localization.Away d.f) d.N) ≠ 0) :
    ∃ yK : Bf d →ₐ[R] K, yK.comp (uS d) = y := by
  let w := y.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f))
  obtain ⟨b₀, hb₀⟩ := exists_factor_away w (c := d.N) (isUnit_iff_ne_zero.mpr hy)
  have hf : IsUnit (b₀ (algebraMap (W R A r m) d.B d.f)) := by
    have := congrArg (fun F => F d.f) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact (IsLocalization.Away.algebraMap_isUnit d.f).map y
  obtain ⟨yK, hyK⟩ := exists_factor_away b₀ hf
  refine ⟨yK, ?_⟩
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers d.f)
  ext x
  have h1 := congrArg (fun F => F x) (uS_comp d)
  have h2 := congrArg (fun F => F (algebraMap (W R A r m) d.B x)) hyK
  have h3 := congrArg (fun F => F x) hb₀
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 h3
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, h1]
  rw [IsScalarTower.algebraMap_apply (W R A r m) d.B (Bf d), h2, h3]
  rfl

end Lift

/-- The character lattice of a finite type, identified with a standard lattice. -/
def stdLattice (I : Type u) [Fintype I] : (I → ℤ) ≃+ (ULift.{u} (Fin (Fintype.card I)) → ℤ) :=
  AddEquiv.arrowCongr ((Fintype.equivFin I).trans Equiv.ulift.symm) (AddEquiv.refl ℤ)

section Field

open HopfPointClosedLocus HopfPointWeightWindow HopfPointWeightLocus HopfPointExtension
  LatticeConfiguration TorusChartExistence

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G}
  {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
  {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} {N₀ : ℕ}

/-- A closed split Hopf point over a field, transported from a piece of a splitting, is the
window torus at a point of some window chart. -/
theorem exists_window_point (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C : Type u} [CommRing C] [Algebra R C]
    (bk : FiniteSource.specOver R C ⟶ T) {I : Type u} [Fintype I] [DecidableEq I]
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hfk : Function.Surjective (AlgHom.liftEquiv R C _ _ fk.1))
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G C).symm fk))
    {K : Type u} [Field K] [Algebra R K] (x' : C →ₐ[R] K) :
    ∃ (n m : ℕ) (_ : NeZero m) (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G)
        (ULift.{u} (Fin (Fintype.card I))) m gen n V δ N₀) (yK : Bf dw.toDatum →ₐ[R] K),
      TorusSubgroupModuli.evaluate (j G dw.toDatum) (FiniteSource.specMap yK ≫ pOver dw.toDatum) =
        TorusSubgroupModuli.evaluate i (FiniteSource.specMap x' ≫ bk) := by
  have hsurjPush : Function.Surjective
      (AlgHom.liftEquiv R K _ _ (FiniteBialgebraHom.pushPoint R x' fk.1)) := by
    rw [surjective_liftEquiv_iff, HopfPointBridge.toGroupAlgebra_pushPoint]
    exact surjective_scalarExt_mapAlgHom x' ((surjective_liftEquiv_iff fk.1).mp hfk)
  let fK : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      FiniteBialgebraHom.IsHopfPoint R f} :=
    ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩
  let T₀ := stdLattice I
  let α₀ := (AddMonoidAlgebra.mapDomainAlgHom R K T₀.toAddMonoidHom).comp
    (HopfPointBridge.toGroupAlgebra fK.1)
  have hα₀ : IsHopfPoint α₀ :=
    ((HopfPointBridge.isHopfPoint_iff fK.1).mp fK.2).mapDomain T₀.toAddMonoidHom
  have hs₀ : Function.Surjective (scalarExt α₀) :=
    surjective_scalarExt_mapDomain _ T₀.surjective ((surjective_liftEquiv_iff fK.1).mp hsurjPush)
  obtain ⟨n, m, hm, dw, y, hyN, hy⟩ := exists_windowDatum hδ hι hgenV hgen hP hN₀ hα₀ hs₀
  obtain ⟨yK, hyK⟩ := exists_lift_Bf dw.toDatum y hyN
  refine ⟨n, m, hm, dw, yK, ?_⟩
  have hpt : (⟨ofGroupAlgebra α₀, isHopfPoint_ofGroupAlgebra hα₀⟩ :
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R]
        AddMonoidAlgebra R (ULift.{u} (Fin (Fintype.card I)) → ℤ) //
        FiniteBialgebraHom.IsHopfPoint R f}) =
      ⟨FiniteBialgebraHom.pushPoint R yK (fS G dw.toDatum).1,
        (fS G dw.toDatum).2.pushPoint R yK⟩ := by
    apply Subtype.ext
    show ofGroupAlgebra α₀ = FiniteBialgebraHom.pushPoint R yK (fS G dw.toDatum).1
    rw [← hy, ← hyK, ← ofGroupAlgebra_toGroupAlgebra G
      (FiniteBialgebraHom.pushPoint R yK (fS G dw.toDatum).1), toGroupAlgebra_pushPoint_fS]
    rfl
  rw [evaluate_j_comp_pOver, evaluate_iS_specMap, evaluate_comp_of_eq_range G i bk fk hev x',
    range_twist_eq G fK hsurjPush T₀]
  exact congrArg (fun g => SubgroupFunctor.range ((SplitTorusPoint.splitPointEquiv G K).symm g))
    hpt.symm

/-- Every closed torus subgroup over a field point is the evaluation of a window chart at a
point of the chart. -/
theorem exists_window_of_field (hP3 : EtaleSplitStatement.{u}) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
    {L : GroupScheme (Spec (CommRingCat.of F))}
    (i : L ⟶ (GroupScheme.baseChange (Over.mk x).hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeTorus.IsTorus L) :
    ∃ (c n m : ℕ) (_ : NeZero m)
      (dw : WindowDatum R (AffineCoordinates.hopfAlgebra G) (ULift.{u} (Fin c)) m gen n V δ N₀)
      (a : Over.mk x ⟶ U dw.toDatum),
      TorusSubgroupModuli.evaluate (j G dw.toDatum) a = SubgroupFunctor.range i := by
  have hT : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  obtain ⟨nk, C, _, _, bk, I, _, _, f, -, hcov, hsurj, hev⟩ :=
    @hP3 R _ G _ (Over.mk x) hT L i hi hL
  obtain ⟨k, z, -⟩ := hcov (default : PrimeSpectrum F)
  obtain ⟨K, _, _, ⟨x'⟩⟩ := exists_fieldPoint (R := R) (show PrimeSpectrum (C k) from z).asIdeal
  obtain ⟨n, m, hm, dw, yK, heq⟩ := @exists_window_point R _ G _ _ σ' gen V _ δ N₀ hδ hι hgenV hgen
    hP hN₀ (Over.mk x) L i (C k) _ _ (bk k) (I k) _ _ (f k) (hsurj k) (hev k) K _ _ x'
  -- openness forces the whole field point into the chart
  obtain ⟨V', hV'⟩ := isOpen_affine G hP3 (r := ULift.{u} (Fin (Fintype.card (I k)))) (m := m)
    (gen := gen) (n := n) (V := V) (δ := δ) (N₀ := N₀) hδ hι hgenV hP hN₀ dw (Over.mk x) hT L i
    hi hL
  have h1 := (hV' (FiniteSource.specOver R K) (FiniteSource.specMap x' ≫ bk k)).mp
    ⟨FiniteSource.specMap yK ≫ pOver dw.toDatum, heq⟩
  have htop : ∀ t : (Over.mk x).left, t ∈ V' := by
    intro t
    obtain ⟨pt⟩ : Nonempty (FiniteSource.specOver R K).left :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    rw [Subsingleton.elim t ((FiniteSource.specMap x' ≫ bk k).left.base pt)]
    exact h1 (Set.mem_range_self pt)
  obtain ⟨a, ha⟩ := (hV' (Over.mk x) (𝟙 (Over.mk x))).mpr (by
    rintro _ ⟨t, rfl⟩
    exact htop _)
  exact ⟨Fintype.card (I k), n, m, hm, dw, a,
    ha.trans (TorusSubgroupModuli.evaluate_id (M := Over.mk x) i)⟩

end Field

section Assembly

open HopfPointWeightWindow HopfPointExtension TorusChartExistence

variable (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {σ' : Type u} (gen : σ' → AffineCoordinates.hopfAlgebra G)
  (V : Submodule R (AffineCoordinates.hopfAlgebra G)) [Module.Finite R V]
  (δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G) (N₀ : ℕ)

/-- The index type of all window charts on standard lattices. -/
abbrev WindowIndex : Type u :=
  Σ (c n : ℕ) (m : ℕ+),
    WindowDatum R (AffineCoordinates.hopfAlgebra G) (ULift.{u} (Fin c)) m gen n V δ N₀

variable {R G gen V δ N₀}

/-- The window charts cover the field points. -/
theorem coversFieldPoints (hP3 : EtaleSplitStatement.{u}) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀) :
    TorusSubgroupModuli.CoversFieldPoints (G := G)
      (U := fun k : WindowIndex R G gen V δ N₀ => U k.2.2.2.toDatum)
      (K := fun k => K G k.2.2.2.toDatum) (fun k => j G k.2.2.2.toDatum) := by
  intro F _ x L i hi hL
  obtain ⟨c, n, m, hm, dw, a, ha⟩ := exists_window_of_field G hP3 hδ hι hgenV hgen hP hN₀ x i hi hL
  exact ⟨⟨c, n, ⟨m, Nat.pos_of_ne_zero hm.out⟩, dw⟩, a, ha⟩

end Assembly

/-- The chart cover over affine bases of finite type over `ℤ`, given the étale-local splitting
of closed tori and the smoothness of the coordinate and representing algebras. -/
theorem finiteTypeChartCover_of (hP3 : EtaleSplitStatement.{u})
    (hsm : ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
      [IsAffine G.X.left] [Smooth G.X.hom], Algebra.Smooth R (AffineCoordinates.hopfAlgebra G))
    (hW : ∀ (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
      [Algebra.Smooth R A] (r : Type u) [Fintype r] (m : ℕ) [NeZero m],
      Algebra.Smooth R (W R A r m)) :
    TorusSubgroupModuli.FiniteTypeChartCoverStatement.{u} := by
  intro R _ _ G _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Algebra.Smooth R (AffineCoordinates.hopfAlgebra G) := hsm R G
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨V₀, hV₀fg, hV₀c, hV₀adj⟩ :=
    FiniteSubcomodule.exists_fg_isRightSubcomodule_adjoin_eq_top (R := R)
      (A := AffineCoordinates.hopfAlgebra G)
  have : Module.Finite R V₀ := Module.Finite.iff_fg.mpr hV₀fg
  obtain ⟨δ, hδ, hι⟩ := HopfPointWeightWindow.exists_coaction V₀ hV₀c
  obtain ⟨s, hs⟩ := hV₀fg
  let gen : s → AffineCoordinates.hopfAlgebra G := Subtype.val
  have hgenV : ∀ i, gen i ∈ V₀ := fun i => hs ▸ Submodule.subset_span i.2
  have hgen : Algebra.adjoin R (Set.range gen) = ⊤ := by
    have hr : Set.range gen = (s : Set (AffineCoordinates.hopfAlgebra G)) := Subtype.range_coe
    rw [hr, eq_top_iff, ← hV₀adj, ← hs]
    exact Algebra.adjoin_le fun a ha =>
      (Submodule.span_le.mpr Algebra.subset_adjoin :
        Submodule.span R (s : Set (AffineCoordinates.hopfAlgebra G)) ≤
          Subalgebra.toSubmodule (Algebra.adjoin R (s : Set (AffineCoordinates.hopfAlgebra G)))) ha
  obtain ⟨N₀, hN₀, hP⟩ := HopfPointWindowExtension.exists_isBoundedPresentation hgen
  refine ⟨WindowIndex R G gen V₀ δ N₀, fun k => U k.2.2.2.toDatum, fun k => K G k.2.2.2.toDatum,
    fun k => j G k.2.2.2.toDatum, fun k => ?_, coversFieldPoints hP3 hδ hι hgenV hgen hP hN₀⟩
  have : Algebra.Smooth R
      (W R (AffineCoordinates.hopfAlgebra G) (ULift.{u} (Fin k.1)) k.2.2.1) :=
    hW _ _ _ _
  exact TorusSubgroupModuli.isOpenChartOfAffines _ _ _ _ _
    (isOpenChartOnAffines G hP3 hδ hι hgenV hP hN₀ k.2.2.2)

end Langlands.GroupScheme.HomScheme.TorusChart
