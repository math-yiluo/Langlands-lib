import Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartOpen
import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupChartStatements
import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupChartAffineTestsProof
import Langlands.Algebra.FiniteSubcomodule
import Langlands.GroupScheme.HomScheme.TorusChartCover
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # The multiplicative-type window charts cover the field points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart

open Langlands.Algebra Langlands.Algebra.MixedChartRing Langlands.Algebra.MixedChartAlgebra
  DiagonalizablePoint

section Lift

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] {r : Type u} [Fintype r] [DecidableEq r]
  {F : Type u} [AddCommGroup F] [Fintype F] {m : ℕ} [NeZero m]
  {σ' : Type u} {gen : σ' → A} {n : ℕ} (d : Datum R A r F m gen n)

open TorusChartExistence in
/-- A field point of `W_f` at which `N` does not vanish extends to `B_f`. -/
theorem exists_lift_Bf {K : Type u} [Field K] [Algebra R K] (y : Localization.Away d.f →ₐ[R] K)
    (hy : y (algebraMap (W R A ((r → ZMod m) × F)) (Localization.Away d.f) d.N) ≠ 0) :
    ∃ yK : Bf d →ₐ[R] K, yK.comp (uS d) = y := by
  let w := y.comp (IsScalarTower.toAlgHom R (W R A ((r → ZMod m) × F)) (Localization.Away d.f))
  obtain ⟨b₀, hb₀⟩ := exists_factor_away w (c := d.N) (isUnit_iff_ne_zero.mpr hy)
  have hf : IsUnit (b₀ (algebraMap (W R A ((r → ZMod m) × F)) d.B d.f)) := by
    have := congrArg (fun φ => φ d.f) hb₀
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]
    exact (IsLocalization.Away.algebraMap_isUnit d.f).map y
  obtain ⟨yK, hyK⟩ := exists_factor_away b₀ hf
  refine ⟨yK, ?_⟩
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers d.f)
  ext x
  have h1 := congrArg (fun φ => φ x) (uS_comp d)
  have h2 := congrArg (fun φ => φ (algebraMap (W R A ((r → ZMod m) × F)) d.B x)) hyK
  have h3 := congrArg (fun φ => φ x) hb₀
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 h3
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, h1]
  rw [IsScalarTower.algebraMap_apply (W R A ((r → ZMod m) × F)) d.B (Bf d), h2, h3]
  rfl

end Lift

/-- A type with `k` elements in universe `u`, without algebraic structure. It carries the
finite part of a character group in the chart index. -/
def Carrier (k : ℕ) : Type u := ULift.{u} (Fin k)

instance (k : ℕ) : Fintype (Carrier.{u} k) := inferInstanceAs (Fintype (ULift.{u} (Fin k)))

/-- **Normal form of finitely generated commutative groups.** A finitely generated commutative
group is isomorphic to `ℤ^c × F`, where the finite group `F` is carried by `Carrier k` with
some group structure `s`. -/
theorem exists_normalForm (Λ' : Type u) [AddCommGroup Λ'] [AddGroup.FG Λ'] :
    ∃ (c k : ℕ) (s : AddCommGroup (Carrier.{u} k)),
      letI := s
      Nonempty (Λ' ≃+ (ULift.{u} (Fin c) → ℤ) × Carrier.{u} k) := by
  classical
  obtain ⟨c, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod Λ'
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  obtain ⟨k, ⟨eT⟩⟩ := Finite.exists_equiv_fin (DirectSum ι fun i => ZMod (p i ^ e i))
  let eU : (DirectSum ι fun i => ZMod (p i ^ e i)) ≃ Carrier.{u} k :=
    eT.trans Equiv.ulift.symm
  let s : AddCommGroup (Carrier.{u} k) := eU.symm.addCommGroup
  refine ⟨c, k, s, ?_⟩
  let _ := s
  let eFree : (Fin c →₀ ℤ) ≃+ (ULift.{u} (Fin c) → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin c)).toAddEquiv.trans
      (AddEquiv.arrowCongr Equiv.ulift.symm (AddEquiv.refl ℤ))
  exact ⟨f.trans (AddEquiv.prodCongr eFree (eU.symm.addEquiv).symm)⟩

section Field

open HopfPointClosedLocus HopfPointWeightWindow HopfPointWeightLocus HopfPointExtension
  MixedLatticeConfiguration

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {σ' : Type u} {gen : σ' → AffineCoordinates.hopfAlgebra G}
  {V : Submodule R (AffineCoordinates.hopfAlgebra G)} [Module.Finite R V]
  {δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G} {N₀ : ℕ}

/-- A closed diagonalizable Hopf point over a field, transported from a piece of a splitting,
is the window subgroup at a point of some window chart on a standard lattice. -/
theorem exists_window_point (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {T : Over (Spec (CommRingCat.of R))} {L : GroupScheme T.left}
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G) {C : Type u} [CommRing C] [Algebra R C]
    (bk : FiniteSource.specOver R C ⟶ T) {Λ' : Type u} [AddCommGroup Λ'] [AddGroup.FG Λ']
    (fk : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f})
    (hfk : Function.Surjective (AlgHom.liftEquiv R C _ _ fk.1))
    (hev : TorusSubgroupModuli.evaluate i bk =
      SubgroupFunctor.range ((diagPointEquiv G C).symm fk))
    {K : Type u} [Field K] [Algebra R K] (x' : C →ₐ[R] K) :
    ∃ (c k : ℕ) (s : AddCommGroup (Carrier.{u} k)) (n m : ℕ) (_ : NeZero m),
      letI := s
      ∃ (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G)
          (ULift.{u} (Fin c)) (Carrier.{u} k) m gen n V δ N₀)
        (yK : Bf dw.toDatum →ₐ[R] K),
        TorusSubgroupModuli.evaluate (j G dw.toDatum)
            (FiniteSource.specMap yK ≫ pOver dw.toDatum) =
          TorusSubgroupModuli.evaluate i (FiniteSource.specMap x' ≫ bk) := by
  obtain ⟨c, k, s, hT₀⟩ := exists_normalForm Λ'
  let _ := s
  obtain ⟨T₀⟩ := hT₀
  have hsurjPush : Function.Surjective
      (AlgHom.liftEquiv R K _ _ (FiniteBialgebraHom.pushPoint R x' fk.1)) := by
    rw [TorusChartRing.surjective_liftEquiv_iff, HopfPointBridge.toGroupAlgebra_pushPoint]
    exact surjective_scalarExt_mapAlgHom x'
      ((TorusChartRing.surjective_liftEquiv_iff fk.1).mp hfk)
  let fK : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R] AddMonoidAlgebra R Λ' //
      FiniteBialgebraHom.IsHopfPoint R f} :=
    ⟨FiniteBialgebraHom.pushPoint R x' fk.1, fk.2.pushPoint R x'⟩
  let α₀ := (AddMonoidAlgebra.mapDomainAlgHom R K T₀.toAddMonoidHom).comp
    (HopfPointBridge.toGroupAlgebra fK.1)
  have hα₀ : IsHopfPoint α₀ :=
    ((HopfPointBridge.isHopfPoint_iff fK.1).mp fK.2).mapDomain T₀.toAddMonoidHom
  have hs₀ : Function.Surjective (scalarExt α₀) :=
    TorusChartRing.surjective_scalarExt_mapDomain _ T₀.surjective
      ((TorusChartRing.surjective_liftEquiv_iff fK.1).mp hsurjPush)
  obtain ⟨n, m, hm, dw, y, hyN, hy⟩ :=
    MixedChartExistence.exists_windowDatum hδ hι hgenV hgen hP hN₀ hα₀ hs₀
  obtain ⟨yK, hyK⟩ := exists_lift_Bf dw.toDatum y hyN
  refine ⟨c, k, s, n, m, hm, dw, yK, ?_⟩
  have hα₀eq : α₀ = dw.toDatum.pushα (yK.comp (uS dw.toDatum)) := by
    rw [hyK]
    exact hy.symm
  have hpt : (⟨TorusChartRing.ofGroupAlgebra α₀, TorusChartRing.isHopfPoint_ofGroupAlgebra hα₀⟩ :
      {f : AffineCoordinates.hopfAlgebra G →ₐ[R] K ⊗[R]
        AddMonoidAlgebra R ((ULift.{u} (Fin c) → ℤ) × Carrier.{u} k) //
        FiniteBialgebraHom.IsHopfPoint R f}) =
      ⟨FiniteBialgebraHom.pushPoint R yK (fS G dw.toDatum).1,
        (fS G dw.toDatum).2.pushPoint R yK⟩ := by
    apply Subtype.ext
    change TorusChartRing.ofGroupAlgebra α₀ =
      FiniteBialgebraHom.pushPoint R yK (fS G dw.toDatum).1
    rw [hα₀eq, ← toGroupAlgebra_pushPoint_fS G dw.toDatum yK,
      TorusChart.ofGroupAlgebra_toGroupAlgebra]
  exact (evaluate_j_comp_pOver G dw.toDatum _).trans ((evaluate_iS_specMap G dw.toDatum yK).trans
    ((congrArg (fun g => SubgroupFunctor.range ((diagPointEquiv G K).symm g)) hpt.symm).trans
      ((range_twist_eq G fK hsurjPush T₀).symm.trans
        (evaluate_comp_of_eq_range G i bk fk hev x').symm)))

/-- Every closed multiplicative-type subgroup over a field point is the evaluation of a window
chart at a point of the chart. -/
theorem exists_window_of_field (hP3 : FppfSplitStatement.{u}) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀)
    {Fld : Type u} [Field Fld] (x : Spec (CommRingCat.of Fld) ⟶ Spec (CommRingCat.of R))
    {L : GroupScheme (Spec (CommRingCat.of Fld))}
    (i : L ⟶ (GroupScheme.baseChange (Over.mk x).hom).obj G) (hi : IsClosedSubgroup i)
    (hL : RelativeMultiplicativeType.IsMultiplicativeType L) :
    ∃ (c k : ℕ) (s : AddCommGroup (Carrier.{u} k)) (n m : ℕ) (_ : NeZero m),
      letI := s
      ∃ (dw : MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G)
          (ULift.{u} (Fin c)) (Carrier.{u} k) m gen n V δ N₀)
        (a : Over.mk x ⟶ U dw.toDatum),
        TorusSubgroupModuli.evaluate (j G dw.toDatum) a = SubgroupFunctor.range i := by
  have hT : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Fld)))
  obtain ⟨nk, C, _, _, bk, Λk, _, _, f, -, -, hcov, hsurj, hev⟩ :=
    @hP3 R _ G _ (Over.mk x) hT L i hi hL
  obtain ⟨k₀, z, -⟩ := hcov (default : PrimeSpectrum Fld)
  obtain ⟨K, _, _, ⟨x'⟩⟩ :=
    TorusChart.exists_fieldPoint (R := R) (show PrimeSpectrum (C k₀) from z).asIdeal
  have hwp := @exists_window_point R _ G _ _ σ' gen V _ δ N₀ hδ hι hgenV hgen hP hN₀ (Over.mk x) L
    i (C k₀) _ _ (bk k₀) (Λk k₀) _ _ (f k₀) (hsurj k₀) (hev k₀) K _ _ x'
  obtain ⟨c, k, s, n, m, hm, hrest⟩ := hwp
  let _ := s
  obtain ⟨dw, yK, heq⟩ := hrest
  -- openness forces the whole field point into the chart
  have hopen := isOpen_affine G hP3 (r := ULift.{u} (Fin c)) (F := Carrier.{u} k)
    (m := m) (gen := gen) (n := n) (V := V) (δ := δ) (N₀ := N₀) hδ hι hgenV hP hN₀ dw
    (Over.mk x) hT L i hi hL
  obtain ⟨V', hV'⟩ := hopen
  have h1 := (hV' (FiniteSource.specOver R K) (FiniteSource.specMap x' ≫ bk k₀)).mp
    ⟨FiniteSource.specMap yK ≫ pOver dw.toDatum, heq⟩
  have htop : ∀ t : (Over.mk x).left, t ∈ V' := by
    intro t
    obtain ⟨pt⟩ : Nonempty (FiniteSource.specOver R K).left :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (PrimeSpectrum Fld))
    rw [Subsingleton.elim t ((FiniteSource.specMap x' ≫ bk k₀).left.base pt)]
    exact h1 (Set.mem_range_self pt)
  obtain ⟨a, ha⟩ := (hV' (Over.mk x) (𝟙 (Over.mk x))).mpr (by
    rintro _ ⟨t, rfl⟩
    exact htop _)
  exact ⟨c, k, s, n, m, hm, dw, a, ha.trans (TorusSubgroupModuli.evaluate_id (M := Over.mk x) i)⟩

end Field

section Assembly

open HopfPointWeightWindow HopfPointExtension

variable (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G)]
  {σ' : Type u} (gen : σ' → AffineCoordinates.hopfAlgebra G)
  (V : Submodule R (AffineCoordinates.hopfAlgebra G)) [Module.Finite R V]
  (δ : V →ₗ[R] V ⊗[R] AffineCoordinates.hopfAlgebra G) (N₀ : ℕ)

/-- The index type of all window charts on standard lattices `ℤ^c × F`, the finite group `F`
being carried by `Carrier k` with the group structure `s`. -/
abbrev WindowIndex : Type u :=
  Σ (c n : ℕ) (m : ℕ+) (k : ℕ) (s : AddCommGroup (Carrier.{u} k)),
    letI := s
    MixedChartExistence.WindowDatum R (AffineCoordinates.hopfAlgebra G) (ULift.{u} (Fin c))
      (Carrier.{u} k) m gen n V δ N₀

variable {R G gen V δ N₀}

/-- The parameter scheme of the window chart with index `x`. -/
abbrev indexU (x : WindowIndex R G gen V δ N₀) : Over (Spec (CommRingCat.of R)) :=
  letI := x.2.2.2.2.1
  U x.2.2.2.2.2.toDatum

/-- The subgroup family of the window chart with index `x`. -/
abbrev indexK (x : WindowIndex R G gen V δ N₀) : GroupScheme (indexU x).left :=
  letI := x.2.2.2.2.1
  K G x.2.2.2.2.2.toDatum

/-- The inclusion of the subgroup family of the window chart with index `x`. -/
abbrev indexJ (x : WindowIndex R G gen V δ N₀) :
    indexK x ⟶ (GroupScheme.baseChange (indexU x).hom).obj G :=
  letI := x.2.2.2.2.1
  j G x.2.2.2.2.2.toDatum

/-- The window charts cover the field points. -/
theorem coversFieldPoints (hP3 : FppfSplitStatement.{u}) (hδ : IsCoassoc δ)
    (hι : (Coalgebra.comul (R := R) (A := AffineCoordinates.hopfAlgebra G)) ∘ₗ V.subtype =
      V.subtype.rTensor _ ∘ₗ δ)
    (hgenV : ∀ i, gen i ∈ V) (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    (hP : IsBoundedPresentation (R := R) gen N₀) (hN₀ : 1 ≤ N₀) :
    MultiplicativeTypeSubgroupModuli.CoversFieldPoints (G := G)
      (U := fun x : WindowIndex R G gen V δ N₀ => indexU x) (K := fun x => indexK x)
      (fun x => indexJ x) := by
  intro Fld _ x L i hi hL
  obtain ⟨c, k, s, n, m, hm, hrest⟩ := exists_window_of_field G hP3 hδ hι hgenV hgen hP hN₀ x i
    hi hL
  let _ := s
  obtain ⟨dw, a, ha⟩ := hrest
  exact ⟨⟨c, n, ⟨m, Nat.pos_of_ne_zero hm.out⟩, k, s, dw⟩, a, ha⟩

end Assembly

/-- The chart cover over affine bases of finite type over `ℤ`, given the fppf-local splitting
of closed multiplicative-type subgroups and the smoothness of the coordinate and representing
algebras. -/
theorem finiteTypeChartCover_of (hP3 : FppfSplitStatement.{u})
    (hsm : ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
      [IsAffine G.X.left] [Smooth G.X.hom], Algebra.Smooth R (AffineCoordinates.hopfAlgebra G))
    (hW : ∀ (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
      [Algebra.Smooth R A] (L : Type u) [AddCommGroup L] [Fintype L],
      Algebra.Smooth R (W R A L)) :
    MultiplicativeTypeSubgroupModuli.FiniteTypeChartCoverStatement.{u} := by
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
  refine ⟨WindowIndex R G gen V₀ δ N₀, fun x => indexU x, fun x => indexK x,
    fun x => indexJ x, fun x => ?_, coversFieldPoints hP3 hδ hι hgenV hgen hP hN₀⟩
  let _ := x.2.2.2.2.1
  have : Algebra.Smooth R (W R (AffineCoordinates.hopfAlgebra G)
      ((ULift.{u} (Fin x.1) → ZMod x.2.2.1) × Carrier.{u} x.2.2.2.1)) :=
    hW _ _ _
  exact MultiplicativeTypeSubgroupModuli.isOpenChartOfAffines _ _ _ _ _
    (isOpenChartOnAffines G hP3 hδ hι hgenV hP hN₀ x.2.2.2.2.2)

end Langlands.GroupScheme.HomScheme.MultiplicativeTypeChart
