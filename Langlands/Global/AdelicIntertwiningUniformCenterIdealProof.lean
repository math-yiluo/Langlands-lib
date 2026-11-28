import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof
import Langlands.Automorphic.GroupSchemeCharacterTwistEnveloping
import Langlands.Global.AdelicIntertwiningCenterIdealReduction
import Langlands.Global.AdelicIntertwiningStabilizerModulusProof
import Langlands.Global.AdelicLeviCenterTransferReduction
import Langlands.Global.AdelicParameterTwistCenterFiniteReduction
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # One center ideal for all regular intertwining integrals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints

local notation "Ainf(" F ")" => CommAlgCat.of F (InfiniteAdeleRing F)

private theorem infiniteLeviRestriction_rightAction
    {F : Type u} [Field F] [NumberField F]
    {G Q M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] {q : Q ⟶ G}
    (l : M ⟶ Q) (g : InfiniteAdelicGroupPoints F G) (f : InfinitePlotSmoothFunctions F G) :
    infiniteLeviRestriction (q := q) l 1
        (G.plotSmoothRightAction Ainf(F) (B := mixedEmbedding.mixedSpace F)
          (RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F)) g f) =
      infiniteLeviRestriction (q := q) l g f := by
  apply Subtype.ext
  funext m
  change f.val (M.affinePointsTarget (l ≫ q) Ainf(F) m * 1 * g) =
    f.val (M.affinePointsTarget (l ≫ q) Ainf(F) m * g)
  rw [mul_one]

set_option maxHeartbeats 800000 in
/-- Finite parabolic center restriction produces a parameter-independent annihilator for every
plot-smooth slice of the regular intertwining integral. -/
theorem intertwiningUniformCenterIdeal :
    IntertwiningUniformCenterIdealStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hAs hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₀, hR⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hAs hT q iV l'
    w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨hleft, hsm, -, ⟨J, hJfin, hJ⟩, -⟩ := hφ
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType Q.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
  have : LocallyOfFiniteType V.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := iV ≫ q) ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
  have : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
  have : IsClosedImmersion iU.hom.hom.left := hU.1.isClosedSubgroup
  have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  have hM' : IsConnectedReductive M' := hl'.isConnectedReductive
  have : IsAffine M'.X.left := hM'.affineScheme
  have : Smooth M'.X.hom := hM'.smooth
  obtain ⟨d', hsmooth'⟩ := hM'.exists_smoothOfRelativeDimension
  have hcalc' := adelicDifferentialCommutator_of_smooth F M' hsmooth'
  have hp := r.isCompatible.parabolic
  have hl := r.isCompatible.levi
  let : IsIso c := hw.isIso
  have hlP : IsRationalLeviSubgroup (c ≫ l) := hl.iso_comp (asIso c)
  obtain ⟨pP, hpPfin, hpPAction⟩ := parabolicLeviCenterRestriction F G P M' U p iU (c ≫ l) hG hp hU hlP
    (hlP.isIso_subgroupMultiplication_of_radical hU) hsmooth hsmooth' hcalc hcalc' 1
  obtain ⟨I, hIfin, hIkill⟩ := exists_cofinite_center_ideal_of_leviRestriction
    (q := p) (c ≫ l) iU hcalc hcalc' 1 pP hpPfin hpPAction J hJfin
  obtain ⟨pQ, -, hpQAction⟩ := parabolicLeviCenterRestriction F G Q M' V q iV l' hG hq hV hl' hmul
    hsmooth hsmooth' hcalc hcalc' 1

  -- The source shift acts on the normalized inducing restrictions.
  let χP (m : InfiniteAdelicGroupPoints F M') :=
    parameterPower F P (-halfModulusParameter F P) (map F M' P (c ≫ l) (ofInfinite F M' m))
  have hχP : χP ∈ InfinitePlotSmoothFunctions F M' :=
    parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions (c ≫ l) _
  obtain ⟨θP, hθP⟩ := exists_centerShift_plotSmoothMultiplication F M' hsmooth' hcalc' χP hχP
    (parameterPower_map_ofInfinite_mul (c ≫ l) _) (by
      simp only [χP, map_one, parameterPower_at_one])

  -- The positive target character converts the normalized target restriction to the raw one.
  let χQ (m : InfiniteAdelicGroupPoints F M') :=
    parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' (ofInfinite F M' m))
  let χQinv (m : InfiniteAdelicGroupPoints F M') :=
    parameterPower F Q (-halfModulusParameter F Q) (map F M' Q l' (ofInfinite F M' m))
  have hχQ : χQ ∈ InfinitePlotSmoothFunctions F M' :=
    parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions l' _
  have hχQinv : χQinv ∈ InfinitePlotSmoothFunctions F M' :=
    parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions l' _
  obtain ⟨θQ, hθQ⟩ := exists_centerShift_plotSmoothMultiplication F M' hsmooth' hcalc' χQ hχQ
    (parameterPower_map_ofInfinite_mul l' _) (by simp only [χQ, map_one, parameterPower_at_one])
  let TQ := plotSmoothMultiplication F M' χQ hχQ
  let TQinv := plotSmoothMultiplication F M' χQinv hχQinv
  have hQcancel (f : InfinitePlotSmoothFunctions F M') : TQ (TQinv f) = f := by
    apply Subtype.ext
    funext m
    change χQ m * (χQinv m * f.val m) = f.val m
    rw [← mul_assoc]
    simp only [χQ, χQinv, parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_mul]
  have hTQinj : Function.Injective TQ := by
    intro f g hfg
    apply Subtype.ext
    funext m
    exact mul_left_cancel₀ (Complex.exp_ne_zero _)
      (congrArg (fun k : InfinitePlotSmoothFunctions F M' => k.val m) hfg)

  let centerMap := θP.comp (θQ.comp pQ)
  refine ⟨R₀, I.comap centerMap.toRingHom, ?_, ?_⟩
  · have : Module.Finite ℂ (AdelicEnvelopingCenter F M' hsmooth' ⧸ I) :=
      (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ I)).mp hIfin
    exact (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ _)).mpr
      (Langlands.Algebra.quotientFinite_comap centerMap I)
  intro lam hlam z hz b h
  have hdom : ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∃ bd : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) → ℝ,
        Integrable bd (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) ∧
        ∀ r, ∀ g ∈ C, ‖hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g r‖ ≤ bd r := by
    intro C hCc
    obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG hp
    have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)), r.IsRegularParameter hAs hT R₀ (e s) := by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
      exact hlam
    obtain ⟨bd, hbd, hbound⟩ := hR C hCc n e {e.symm lam} isCompact_singleton hsingle
    exact ⟨bd, hbd, fun x g hg => by
      simpa only [e.apply_symm_apply] using hbound x g hg (e.symm lam) (Set.mem_singleton _)⟩
  let y := θQ (pQ z)
  have hyI : θP y ∈ I := hz
  let R := G.plotSmoothRightAction Ainf(F) (B := mixedEmbedding.mixedSpace F)
    (RingEquiv.toRingHom (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  let ρG := plotSmoothCenterAction F G hsmooth hcalc
  let ρM := plotSmoothCenterAction F M' hsmooth' hcalc'
  refine IsIwasawaCompact.centerAction_intertwiningOperator_eq_zero_of_levi
    hK hK' intertwiningStabilizerModulus hG hp hU hl hq hV hl' hw hπ hsmooth
    hcalc hsmooth' hcalc' hsm.1 hleft hsm.2.1 z y.val ?_ ?_ lam hdom b h
  · intro f hf hInv g hNorm
    let f₀ : InfinitePlotSmoothFunctions F G := ⟨f, hf⟩
    let S := infiniteLeviRestriction (q := q) l'
    have hgInv (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G) :
        (R g f₀).val (V.affinePointsTarget (iV ≫ q) Ainf(F) v * x) = (R g f₀).val x := by
      change f (_ * x * g) = f (x * g)
      rw [mul_assoc, hInv]
    have hRaw : S g (ρG z f₀) = ρM (pQ z) (S g f₀) := by
      rw [← infiniteLeviRestriction_rightAction l' g (ρG z f₀),
        plotSmoothCenterAction_rightTranslation F G hsmooth hcalc hG g z f₀]
      exact (hpQAction (R g f₀) hgInv z).trans
        (congrArg (ρM (pQ z)) (infiniteLeviRestriction_rightAction l' g f₀))
    have hNormalized : ρM y (TQinv (S g f₀)) = TQinv (S g (ρG z f₀)) := by
      apply hTQinj
      calc
        TQ (ρM y (TQinv (S g f₀))) = ρM (pQ z) (TQ (TQinv (S g f₀))) :=
          (hθQ (pQ z) (TQinv (S g f₀))).symm
        _ = ρM (pQ z) (S g f₀) := congrArg (ρM (pQ z)) (hQcancel (S g f₀))
        _ = S g (ρG z f₀) := hRaw.symm
        _ = TQ (TQinv (S g (ρG z f₀))) := (hQcancel (S g (ρG z f₀))).symm
    exact congrArg (fun f : InfinitePlotSmoothFunctions F M' => f.val) hNormalized
  · intro b₀ g hNorm
    let f : InfinitePlotSmoothFunctions F G := ⟨_, hsm.2.1 b₀⟩
    let S := infiniteLeviRestriction (q := p) (c ≫ l)
    have hleftU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
      fun x hx g => hleft x (Subgroup.mem_sup_left hx) g
    have hgInv (v : InfiniteAdelicGroupPoints F U) (x : InfiniteAdelicGroupPoints F G) :
        (R g f).val (U.affinePointsTarget (iU ≫ p) Ainf(F) v * x) = (R g f).val x := by
      change functionInfiniteSlice F G φ b₀ (_ * x * g) = functionInfiniteSlice F G φ b₀ (x * g)
      rw [mul_assoc]
      exact functionInfiniteSlice_unipotent_mul iU hleftU b₀ v (x * g)
    have hgJ : ∀ z' ∈ J, ρG z' (R g f) = 0 := by
      intro z' hz'
      change plotSmoothCenterAction F G hsmooth hcalc z' (R g f) = 0
      rw [← plotSmoothCenterAction_rightTranslation F G hsmooth hcalc hG g z' f,
        hJ z' hz' b₀ (hsm.2.1 b₀), map_zero]
    have hRaw : ρM (θP y) (S g f) = 0 := by
      rw [← infiniteLeviRestriction_rightAction (c ≫ l) g f]
      exact hIkill (R g f) hgInv hgJ (θP y) hyI
    have hNormalized : ρM y (plotSmoothMultiplication F M' χP hχP (S g f)) = 0 := by
      change plotSmoothCenterAction F M' hsmooth' hcalc' y
        (plotSmoothMultiplication F M' χP hχP (S g f)) = 0
      rw [hθP y (S g f), hRaw, map_zero]
    have hSlice : (⟨_, hNorm⟩ : InfinitePlotSmoothFunctions F M') =
        plotSmoothMultiplication F M' χP hχP (S g f) := by
      apply Subtype.ext
      funext m
      change χP m * f.val (M'.affinePointsTarget (c ≫ l ≫ p) Ainf(F) m * g) =
        χP m * f.val (M'.affinePointsTarget ((c ≫ l) ≫ p) Ainf(F) m * g)
      rw [Category.assoc]
    change ρM y ⟨_, hNorm⟩ = 0
    rw [hSlice, hNormalized]

end Langlands.Global
