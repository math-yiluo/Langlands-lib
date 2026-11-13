import Langlands.Geometry.Building.UnramifiedFixedWallInvarianceStatement
import Langlands.Geometry.Building.UnramifiedFixedLocusStatement
import Langlands.Geometry.Building.UnramifiedValuationDescentReduction
import Langlands.Geometry.Building.QuasiSplitApartmentOpposite

/-! # V 5 at the Galois-fixed points from the wall invariance of `m(u)` (KP Corollary 9.4.10) -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- A nonzero character of a split torus takes every real value on the real cocharacters. -/
theorem exists_eval_eq_of_ne_zero {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (hS : IsSplitTorus S.toGrp)
    {a : characterLattice S} (ha : a ≠ 0) (r : ℝ) : ∃ v : V S, eval S a v = r := by
  obtain ⟨d, hd, ζ, hζ⟩ := hS.exists_pairing_eq_pos ha
  refine ⟨(r / d) ⊗ₜ[ℤ] ζ, ?_⟩
  rw [eval_tmul, hζ]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

private instance unramifiedOppositeReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 1600000 in
/-- **V 5 at one Galois-fixed point from the wall invariance**, with explicit binders. The
hypothesis `hW` is the conclusion of `UnramifiedFixedWallInvarianceStatement` for the given
data. -/
theorem unramifiedFixedOpposite_core
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (hW : ∀ z : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ z.val = z.val) →
      ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
        ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
          ∀ hm : g' * g * g'' ∈ normalizerPoints iS,
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = 0 →
            (⟨g' * g * g'', hm⟩ : normalizerPoints iS) •
              torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
                hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
                ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
              torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
                hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
                ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    (x : D.Apartment) (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
        g' * g * g'' ∈ normalizerPoints iS →
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) (-a) g' +
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = 0 := by
  intro a ha g hg hg1 g' hg' g'' hg'' hm
  have hS : IsSplitTorus S.toGrp := hiS.isSplitSubtorus.1
  have hTK := hiT.isSplitSubtorus.1
  have hfactor : CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫ (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  -- the restricted family at an apartment point
  set φ : D.Apartment → RootFunctionFamily S G := fun y =>
    torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
      hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
  -- Galois-fixed translates of `x` along the original real cocharacters
  have htrans : ∀ v : V S, ∃ y : D.Apartment,
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) ∧
      φ y = v +ᵥ φ x := by
    intro v
    refine ⟨⟨descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x.val,
      D.vadd_mem x.mem _⟩, ?_, ?_⟩
    · intro σ
      change RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ
          (descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x.val) =
        descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x.val
      rw [RootFunctionFamily.galoisAction_vadd, galoisCocharacterAction_descentCocharacterMap,
        hx σ]
    · exact torusFieldRestrictedRootFunctionFamily_descent_vadd (K := inertiaFixedField F) f iT
        hS hTK hE x.isValuation (D.isRootDatumValuation_of_mem (D.vadd_mem x.mem _)) v rfl
  -- finiteness of the values at nonidentity root points
  have hfin : ∀ (y : D.Apartment) (b : characterLattice S), b ∈ relativeRoots iS →
      ∀ e ∈ rootGroupPoints iS b, e ≠ 1 → ∃ r : ℝ, φ y b e = (r : WithTop ℝ) := by
    intro y b hb e he he1
    have hne : φ y b e ≠ ⊤ := by
      intro htop
      exact he1 ((torusFieldRestrictedRootFunctionFamily_eq_top_iff (K := inertiaFixedField F)
        iS hS hTK hE (D.isRootDatumValuation_of_mem y.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) hfactor
        b hb e he).1 htop)
    exact WithTop.ne_top_iff_exists.1 hne |>.imp fun r hr => hr.symm
  -- the opposite factor pair and its reflection
  let m : normalizerPoints iS := ⟨g' * g * g'', hm⟩
  have hp : RelativeRoot.IsOppositeFactorPair iS a g (g', g'') := ⟨hg', hg'', hm⟩
  have ha0 : a ≠ 0 := ha.1
  have hma : weylAction iS m a = -a := hp.weylAction_eq_neg iS hS ha0 hg hg1
  have hminv : weylAction iS m⁻¹ a = -a := by
    have h1 : weylAction iS m⁻¹ (-a) = a := by
      rw [← hma, map_inv]
      exact (weylAction iS m).symm_apply_apply a
    have h2 := congrArg (fun χ => -χ) h1
    simpa only [map_neg, neg_neg] using h2
  have hmneg : weylAction iS m (-a) = a := by rw [map_neg, hma, neg_neg]
  have hg'1 : g' ≠ 1 := (hp.factors_ne_one iS hS ha0 hg hg1).1
  have hna : -a ∈ relativeRoots iS := neg_mem_relativeRoots_of_weylAction_eq_neg iS ha m hma
  -- the pair of `g'` for the root `-a` has the same product `m`
  have hq1 : (m : rationalPoints G) * g'' * (m : rationalPoints G)⁻¹ ∈ rootGroupPoints iS (-(-a)) := by
    rw [neg_neg, ← hmneg]
    exact conj_mem_rootGroupPoints m hg''
  have hq2 : g ∈ rootGroupPoints iS (-(-a)) := by rwa [neg_neg]
  have hqprod : (m : rationalPoints G) * g'' * (m : rationalPoints G)⁻¹ * g' * g =
      g' * g * g'' := by
    change g' * g * g'' * g'' * (g' * g * g'')⁻¹ * g' * g = g' * g * g''
    group
  have hqm : (m : rationalPoints G) * g'' * (m : rationalPoints G)⁻¹ * g' * g ∈
      normalizerPoints iS := by
    rw [hqprod]
    exact hm
  -- values at `x`
  obtain ⟨r, hr⟩ := hfin x a ha g hg hg1
  obtain ⟨r', hr'⟩ := hfin x (-a) hna g' hg' hg'1
  -- the wall point of `g`
  obtain ⟨v, hv⟩ := exists_eval_eq_of_ne_zero hS ha0 (-r)
  obtain ⟨z, hz, hφz⟩ := htrans v
  have hzg : φ z a g = 0 := by
    rw [hφz, RootFunctionFamily.vadd_apply, hr, hv, ← WithTop.coe_add, add_neg_cancel,
      WithTop.coe_zero]
  have hWz : m • φ z = φ z := hW z hz a ha g hg hg1 g' hg' g'' hg'' hm hzg
  -- the wall point of `g'`
  have hna0 : -a ≠ 0 := neg_ne_zero.2 ha0
  obtain ⟨v', hv'⟩ := exists_eval_eq_of_ne_zero hS hna0 (-r')
  obtain ⟨z', hz', hφz'⟩ := htrans v'
  have hzg' : φ z' (-a) g' = 0 := by
    rw [hφz', RootFunctionFamily.vadd_apply, hr', hv', ← WithTop.coe_add, add_neg_cancel,
      WithTop.coe_zero]
  have hWz' := hW z' hz' (-a) hna g' hg' hg'1 _ hq1 g hq2 hqm hzg'
  have hmm : (⟨(m : rationalPoints G) * g'' * (m : rationalPoints G)⁻¹ * g' * g, hqm⟩ :
      normalizerPoints iS) = m := Subtype.ext hqprod
  rw [hmm] at hWz'
  change m • φ z' = φ z' at hWz'
  -- compare the two invariances
  have hφzz : φ z' = (v' - v) +ᵥ φ z := by
    rw [hφz', hφz, vadd_vadd, sub_add_cancel]
  rw [hφzz, RootFunctionFamily.smul_vadd, hWz] at hWz'
  have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ a g) hWz'
  simp only [RootFunctionFamily.vadd_apply, hzg, zero_add, WithTop.coe_inj] at hval
  rw [eval_normalizer_smul, hminv, eval_neg_char] at hval
  have hw0 : eval S a (v' - v) = 0 := by linarith
  have hv'a : eval S a v' = r' := by
    have h := hv'
    rw [eval_neg_char] at h
    linarith
  rw [map_sub, hv'a, hv] at hw0
  change φ x (-a) g' + φ x a g = 0
  rw [hr, hr', ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj]
  linarith

set_option maxHeartbeats 8000000 in
/-- `UnramifiedFixedWallInvarianceStatement` for fixed data, with explicit binders. -/
theorem unramifiedFixedWallInvariance_apply
    (hW : UnramifiedFixedWallInvarianceStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (z : D.Apartment) (hz : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ z.val = z.val) :
    ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
        ∀ hm : g' * g * g'' ∈ normalizerPoints iS,
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = 0 →
          (⟨g' * g * g'', hm⟩ : normalizerPoints iS) •
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem z.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) :=
  hW F G hG S iS hiS T iT f hf hiT hE D C hDC z hz

/-- **The reduction of V 5 at the Galois-fixed points to the wall invariance of `m(u)`.**
Internal proposition naming the implication proved below (KP Corollary 9.4.10 from the last
assertion of Proposition 9.4.9). Neither side is asserted. -/
def UnramifiedFixedOppositeReductionStatement : Prop :=
  UnramifiedFixedWallInvarianceStatement.{u} → UnramifiedFixedOppositeStatement.{u}

set_option maxHeartbeats 8000000 in
/-- **V 5 at the Galois-fixed points from the wall invariance of `m(u)`** (KP Corollary
9.4.10 from the last assertion of Proposition 9.4.9). -/
theorem unramifiedFixedOpposite_of_wallInvariance
    (hW : UnramifiedFixedWallInvarianceStatement.{u}) :
    UnramifiedFixedOppositeStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ x hx
  exact unramifiedFixedOpposite_core F G S iS hiS T iT f hf hiT hE D
    (fun z hz => unramifiedFixedWallInvariance_apply hW F G hG S iS hiS T iT f hf hiT hE D C hDC
      z hz) x hx

/-- The proposition `UnramifiedFixedOppositeReductionStatement` holds. -/
theorem unramifiedFixedOppositeReduction : UnramifiedFixedOppositeReductionStatement.{u} :=
  unramifiedFixedOpposite_of_wallInvariance

end Langlands.Geometry.Building
