import Langlands.Representation.Intertwining.PQIntegralIdentificationGroup
import Langlands.Representation.Intertwining.PQIntegralIntertwiningReduction
import Langlands.Representation.Intertwining.PQBoundaryVanishingCompactSupportProof

/-! # Renard VII.3.4: the integral identification and the integral-normalized `J_{Q|P}` -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology Filter MeasureTheory
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme MatrixRepresentation

/-- Renard's decomposition `U = (U ∩ N)(U ∩ N̄)` of the unipotent radical of `Q` (VII.3.4, proof,
printed p.236 / PDF p.242) as a homeomorphism: multiplication
`(N ∩ U)(F) × (N̄ ∩ U)(F) → U(F)`, `(a, b) ↦ a b`, is a homeomorphism, the factors read as
subgroups of `U(F)`. It is `MatrixRepresentation.unipotentIntersectionProduct` for the
split-component cocharacters of `P` and `Q`. -/
theorem exists_radical_product_homeomorph {k : Type u} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {P M N Q U Pb Nb : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    {pb : Pb ⟶ G} {lb : M ⟶ Pb} {rb : Nb ⟶ Pb}
    (hpb : IsParabolicSubgroup pb) (hlb : IsRationalLeviSubgroup lb)
    (hrb : LeviSubgroup.IsGeometricUnipotentRadical rb)
    (hsame : l ≫ p = lQ ≫ q) (hbar : lb ≫ pb = l ≫ p)
    (hopp : pointImage p ⊓ pointImage pb = pointImage (l ≫ p)) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∃ m : ((pointImage (r ≫ p)).subgroupOf (pointImage (rQ ≫ q))) ×
        ((pointImage (rb ≫ pb) ⊓ pointImage (rQ ≫ q)).subgroupOf (pointImage (rQ ≫ q))) ≃ₜ
          pointImage (rQ ≫ q),
      ∀ x, m x = (x.1 : pointImage (rQ ≫ q)) * (x.2 : pointImage (rQ ≫ q)) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨presP⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ a hq hlQ ha
  obtain ⟨presB⟩ := parabolicRootPresentationExistence k G hG Pb M A pb lb a hpb hlb ha
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := k)
  have hξM : gmRationalPoint t ≫
      (CommGroupScheme.groupHom presQ.splitComponentCocharacter ≫ a ≫ lQ ≫ q).hom.hom ∈
        pointImage (l ≫ p) := by
    refine ⟨gmRationalPoint t ≫
      (CommGroupScheme.groupHom presQ.splitComponentCocharacter ≫ a).hom.hom, ?_⟩
    change _ ≫ (l ≫ p).hom.hom = _
    rw [hsame]
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hPχ := presP.parabolic_eq_splitComponentCocharacter
  have hMχ := presP.levi_eq_splitComponentCocharacter
  have hNχ := presP.range_comp_radical_eq hr
  have hUξ := presQ.range_comp_radical_eq hrQ
  have hPb := presB.parabolic_eq_splitComponentCocharacter
  have hMb := presB.levi_eq_splitComponentCocharacter
  have hNb := presB.range_comp_radical_eq hrb
  generalize CommGroupScheme.groupHom presP.splitComponentCocharacter ≫ a ≫ l ≫ p = χ
    at hPχ hMχ hNχ
  generalize CommGroupScheme.groupHom presQ.splitComponentCocharacter ≫ a ≫ lQ ≫ q = ξ
    at hUξ hξM
  generalize CommGroupScheme.groupHom presB.splitComponentCocharacter ≫ a ≫ lb ≫ pb = χb
    at hPb hMb hNb
  have hM : pointImage (l ≫ p) = (Dynamic.centralizer χ).rationalPoints := by
    change (SubgroupFunctor.range (l ≫ p)).rationalPoints = _
    rw [hMχ]
  have hN : pointImage (r ≫ p) = (Dynamic.unipotent χ).rationalPoints := by
    change (SubgroupFunctor.range (r ≫ p)).rationalPoints = _
    rw [hNχ]
  have hU : pointImage (rQ ≫ q) = (Dynamic.unipotent ξ).rationalPoints := by
    change (SubgroupFunctor.range (rQ ≫ q)).rationalPoints = _
    rw [hUξ]
  have hZ : Dynamic.centralizer χb = Dynamic.centralizer χ := by
    rw [← hMb, ← hMχ, hbar]
  have hPP : (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
      (Dynamic.parabolic χb).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← hPχ, ← hPb, ← hMχ]
    exact hopp
  have hNbar : pointImage (rb ≫ pb) = (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).rationalPoints := by
    change (SubgroupFunctor.range (rb ≫ pb)).rationalPoints = _
    rw [hNb, (oppositeDynamicParabolicUniqueness k G hG χ χb hZ hPP).2]
    rfl
  have hξ : gmRationalPoint t ≫ ξ.hom.hom ∈ (Dynamic.centralizer χ).rationalPoints := by
    rw [← hM]
    exact hξM
  have hZU : ∀ m ∈ (Dynamic.centralizer χ).rationalPoints,
      m ∈ (Dynamic.unipotent ξ).rationalPoints → m = 1 := by
    intro m hm hmU
    rw [← hM, hsame] at hm
    rw [← hU] at hmU
    exact IsSemidirectDecomposition.eq_one_of_mem_of_mem
      (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ) hm hmU
  rw [Subgroup.inf_subgroupOf_right, hN, hU, hNbar]
  exact ⟨unipotentIntersectionProduct k χ ξ t ht hξ hZU, fun x => rfl⟩

open IntegralIdentification DualIntegral in
set_option maxHeartbeats 6400000 in
/-- **Renard VII.3.4, first paragraph of the proof.** The identification
`F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` induced by `f ↦ ∫_{N̄(F) ∩ U(F)} f(v) dv`. -/
theorem pqIntegralIdentification : PQIntegralIdentificationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U Pb Nb p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ pb lb rb hpb hlb hrb
    hmulb hsame hbar hopp V _ _ haar _
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  -- Topology of `G(F)`.
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  -- The subgroups and their elementary properties.
  have hPd := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  have hNc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hPc : IsClosed (pointImage p : Set (rationalPoints G)) :=
    isClosed_pointImage p hp.isClosedSubgroup
  have hQc : IsClosed (pointImage q : Set (rationalPoints G)) :=
    isClosed_pointImage q hq.isClosedSubgroup
  have hUc := isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup
  have hNlim := isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1
  have hUlim := isLimitOfCompactSubgroups_pointImage_radical q rQ hq.isClosedSubgroup hrQ.1
  have hproj := continuous_projection_pointImage p l r hp hl hr hmul
  have hVc : IsClosed (V : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb rb hpb.isClosedSubgroup hrb.1.isClosedSubgroup).inter hUc
  have hVU : V ≤ pointImage (rQ ≫ q) := inf_le_right
  have hUQ : pointImage (rQ ≫ q) ≤ pointImage q := pointImage_comp_le q rQ
  have hVQ : V ≤ pointImage q := hVU.trans hUQ
  have hPV : ∀ v ∈ V, v ∈ pointImage p → v = 1 := by
    intro v hv hvp
    have hvpb : v ∈ pointImage pb := pointImage_comp_le pb rb hv.1
    have hvM : v ∈ pointImage (lb ≫ pb) := by
      rw [hbar, ← hopp]
      exact ⟨hvp, hvpb⟩
    exact IsSemidirectDecomposition.eq_one_of_mem_of_mem
      (isSemidirectDecomposition_pointImage pb lb rb hpb.isClosedSubgroup hrb hmulb) hvM hv.1
  have hMV : ∀ m ∈ pointImage (l ≫ p), ∀ v ∈ V, m⁻¹ * v * m ∈ V := by
    intro m hm v hv
    have hmb : m⁻¹ ∈ Subgroup.normalizer (pointImage (rb ≫ pb) : Set (rationalPoints G)) :=
      Subgroup.inv_mem _ (pointImage_le_normalizer pb lb rb hrb (by rw [hbar]; exact hm))
    have hmq : m⁻¹ ∈ Subgroup.normalizer (pointImage (rQ ≫ q) : Set (rationalPoints G)) :=
      Subgroup.inv_mem _ (pointImage_le_normalizer q lQ rQ hrQ (by rw [← hsame]; exact hm))
    have h1 := (Subgroup.mem_normalizer_iff.mp hmb v).mp hv.1
    have h2 := (Subgroup.mem_normalizer_iff.mp hmq v).mp hv.2
    rw [inv_inv] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨mprod, hmprod⟩ :=
    exists_radical_product_homeomorph hG hp hl hr hq hlQ hrQ hmulQ hpb hlb hrb hsame hbar hopp
  -- The double coset `D = P Q` and its local closedness.
  set D := DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
    (identityParabolicDoubleCoset p q) with hDdef
  have hD : ∀ x, x ∈ D ↔ ∃ a ∈ pointImage p, ∃ b ∈ pointImage q, x = a * b := by
    intro x
    rw [hDdef, DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq]
    simp
  have hDP : ∀ a ∈ pointImage p, ∀ x ∈ D, a * x ∈ D := by
    intro a ha x hx
    obtain ⟨a', ha', b, hb, rfl⟩ := (hD x).mp hx
    exact (hD _).mpr ⟨a * a', (pointImage p).mul_mem ha ha', b, hb, by rw [mul_assoc]⟩
  have h1D : (1 : rationalPoints G) ∈ D :=
    (hD 1).mpr ⟨1, (pointImage p).one_mem, 1, (pointImage q).one_mem, by rw [mul_one]⟩
  obtain ⟨n, c, z₀, hz₀, D₀, hglued⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hfinite : Finite (parabolicDoubleCosets p q) := Finite.of_surjective c c.surjective
  obtain ⟨nn, ⟨so⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q) hPc hQc hfinite
  have hloc : IsLocallyClosed (Geometric.cosetOrbit (pointImage p) (pointImage q) 1) := by
    have := (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q)
      so.bruhatLinearOrder so.isBruhatRefinement_bruhatLinearOrder 1).orbit_isLocallyClosed
    simpa only [inv_one] using this
  have hlocD : IsLocallyClosed D := by
    have hpre : D = Induction.quotientMap (pointImage p) ⁻¹'
        Geometric.cosetOrbit (pointImage p) (pointImage q) 1 := by
      ext x
      rw [hD]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        refine ⟨⟨b, hb⟩, ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        simpa [mul_assoc] using ha
      · rintro ⟨⟨b, hb⟩, hbx⟩
        have hxb : x * (1⁻¹ * b)⁻¹ ∈ pointImage p :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact hbx)
        exact ⟨x * (1⁻¹ * b)⁻¹, hxb, b, hb, by simp⟩
    rw [hpre]
    exact hloc.preimage continuous_quotient_mk'
  have hQPV : ∀ x ∈ pointImage q, ∃ v ∈ V, x * v⁻¹ ∈ pointImage p := by
    have hU := pointImage_radical_eq_mul hG hp hl hr hq hlQ hrQ hmulQ hpb hlb hrb hsame hbar hopp
    intro x hx
    let dQ := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
    set mx := dQ.projection ⟨x, hx⟩ with hmx
    have hux' : ((mx : rationalPoints G))⁻¹ * x ∈
        ((pointImage (rQ ≫ q) : Subgroup (rationalPoints G)) : Set (rationalPoints G)) :=
      dQ.projection_inv_mul_mem ⟨x, hx⟩
    rw [hU] at hux'
    obtain ⟨a, ha, b, hb, hab⟩ := hux'
    refine ⟨b, hb, ?_⟩
    have hle : pointImage (lQ ≫ q) ≤ pointImage p := by
      rw [← hsame]
      exact pointImage_comp_le p l
    have hmP : (mx : rationalPoints G) ∈ pointImage p := hle mx.2
    have haP : a ∈ pointImage p := pointImage_comp_le p r ha.1
    have heq : x * b⁻¹ = (mx : rationalPoints G) * a := by
      rw [← mul_inv_eq_iff_eq_mul.mpr hab.symm]
      group
    rw [heq]
    exact (pointImage p).mul_mem hmP haP
  have hlocV : IsLocallyClosed (Geometric.cosetOrbit (pointImage p) V 1) := by
    have horb : Geometric.cosetOrbit (pointImage p) V 1 =
        Geometric.cosetOrbit (pointImage p) (pointImage q) 1 := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨⟨v, hVQ v.2⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨v, hv, hbv⟩ := hQPV b b.2
        refine ⟨⟨v, hv⟩, ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        simpa [mul_assoc] using hbv
    rw [horb]
    exact hloc
  have hVD : ∀ v ∈ V, v ∈ D := fun v hv =>
    (hD v).mpr ⟨1, (pointImage p).one_mem, v, hVQ hv, (one_mul v).symm⟩
  -- Per-representation data.
  have hcsW := pqBoundaryVanishingCompactSupport.{u, v} k G hG P M N Q U Pb Nb p l r hp hl hr
    hmul q lQ rQ hq hlQ hrQ hmulQ pb lb rb hpb hlb hrb hmulb hsame hbar hopp
  have hBV : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : (leviInductionFunctor p l r hp hr hl hmul).obj W),
      f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
        (identityParabolicDoubleCoset p q)).obj W ↔
      ∀ x ∈ closure D \ D, Induction.eval (pointImage p) (inducingRepresentation hPd hNc
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W)) f x = 0 := fun W f =>
    Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p) (pointImage q) _
      (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p q))
      ((leviInducingFunctor p l r hp hr hl hmul).obj W) f
  have hCV : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (f : (leviInductionFunctor p l r hp hr hl hmul).obj W),
      f ∈ (closureVanishingSubfunctor p l r hp hr hl hmul q
        (identityParabolicDoubleCoset p q)).obj W ↔
      ∀ x ∈ closure D, Induction.eval (pointImage p) (inducingRepresentation hPd hNc
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W)) f x = 0 := fun W f =>
    Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p) (pointImage q) _
      (Geometric.closure_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p q))
      ((leviInducingFunctor p l r hp hr hl hmul).obj W) f
  let Sb : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      Submodule ℂ (Induction.SmoothFunctions (pointImage p) (inducingRepresentation hPd hNc
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W))) :=
    fun W => ((boundaryVanishingSubfunctor p l r hp hr hl hmul q
      (identityParabolicDoubleCoset p q)).obj W).toSubmodule
  have hSU : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)), ∀ x ∈ pointImage (rQ ≫ q),
      ∀ f, f ∈ Sb W → Induction.smoothInduced (pointImage p) (inducingRepresentation hPd hNc
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W)) x f ∈ Sb W :=
    fun W x hx f hf => ((boundaryVanishingSubfunctor p l r hp hr hl hmul q
      (identityParabolicDoubleCoset p q)).obj W).apply_mem_toSubmodule ⟨x, hUQ hx⟩ hf
  have hScs : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)) f, f ∈ Sb W →
      HasCompactSupportOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V f :=
    fun W f hf => (hcsW W f).mp hf
  let φ : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      Sb W →ₗ[ℂ] ((boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj W).toSubmodule := fun W =>
    LinearMap.codRestrict _ ((Jacquet.Localization.mk
      ((leviInductionFunctor p l r hp hr hl hmul).obj W).representation
        (pointImage (rQ ≫ q)) 1).comp (Sb W).subtype) (fun s => ⟨s.1, s.2, rfl⟩)
  have hφsurj : ∀ W, Function.Surjective (φ W) := by
    rintro W ⟨_, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hker : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M), LinearMap.ker (φ W) ≤
      LinearMap.ker (integralLinear hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W)
        V haar (Sb W) (hScs W)) := by
    intro W s hs
    have hmk : Jacquet.Localization.mk
        ((leviInductionFunctor p l r hp hr hl hmul).obj W).representation
        (pointImage (rQ ≫ q)) 1 s.1 = 0 := congrArg Subtype.val hs
    have hrel := (Jacquet.Localization.mk_eq_zero _ _ _ _).mp hmk
    exact eq_zero_of_mem_relations ((leviInductionFunctor p l r hp hr hl hmul).obj W).isSmooth
      (pointImage (rQ ≫ q)) hUlim (Sb W) (hSU W) _
      (fun x t => integralOn_smoothInduced hPd hNc _ hNlim hUc hVc hVU hUlim mprod hmprod haar
        (hScs W t.1 t.2) x) s hrel
  let J : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj W).toSubmodule →ₗ[ℂ] W := fun W =>
    LinearDescent.descend (φ W) (hφsurj W) _ (hker W)
  have hJ : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (s : Sb W),
      J W (φ W s) = integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W)
        V haar s := fun W s =>
    LinearDescent.descend_apply (φ W) (hφsurj W) _ (hker W) s
  -- The integral vanishes on `F^{≤1̄}`: such functions vanish on `V ⊆ closure (P Q)`.
  have hlow : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).lowerInUpper
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) W).toSubmodule ≤ LinearMap.ker (J W) := by
    intro W y hy
    obtain ⟨f', hf', hfy⟩ := hy
    have hf'S : f' ∈ Sb W := (hBV W f').mpr (fun x hx => (hCV W f').mp hf' x hx.1)
    have hy' : y = φ W ⟨f', hf'S⟩ := Subtype.ext hfy.symm
    rw [LinearMap.mem_ker, hy', hJ]
    exact ((hasDualIntegral_zero (X := V)).congr fun x : V =>
      ((hCV W f').mp hf' x (subset_closure (hVD x x.2))).symm).dualIntegral_eq
  let Low : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      Submodule ℂ ((boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).obj W).toSubmodule := fun W =>
    ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (identityParabolicDoubleCoset p q)).lowerInUpper
      (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)) W).toSubmodule
  let I : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) W) →ₗ[ℂ] W := fun W =>
    (Low W).liftQ (J W) (hlow W)
  have hI : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (s : Sb W),
      I W (Submodule.Quotient.mk (p := Low W) (φ W s)) =
        integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar s :=
    fun W s => (Submodule.liftQ_apply _ _ _).trans (hJ W s)
  have hIsmul : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (c : ℂ) (s : Sb W),
      I W (Submodule.Quotient.mk (p := Low W) (c • φ W s)) =
        c • integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar s :=
    fun W c s => (LinearDescent.liftQ_mk_smul _ _ _ c _).trans (congrArg (c • ·) (hJ W s))
  -- Surjectivity: induced functions with prescribed integral.
  have hsurj : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M), Function.Surjective (I W) := by
    intro W w
    obtain ⟨f, hfbv, hfw⟩ := exists_integralOn_eq hPd hNc
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) hPc hproj hVc hlocV hPV haar D hDP
      h1D hlocD (fun f hf => hScs W f ((hBV W f).mpr hf)) w
    exact ⟨Submodule.Quotient.mk (p := Low W) (φ W ⟨f, (hBV W f).mpr hfbv⟩),
      (hI W ⟨f, (hBV W f).mpr hfbv⟩).trans hfw⟩
  -- Naturality in the representation.
  have hnat : ∀ (W W' : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (g : W ⟶ W') x,
      I W' (((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientMap
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) g).hom x) = SmoothRep.hom g (I W x) := by
    intro W W' g x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Low W) x
    obtain ⟨⟨f, hf⟩, rfl⟩ := hφsurj W y
    have hf' := (boundaryVanishingSubfunctor p l r hp hr hl hmul q
      (identityParabolicDoubleCoset p q)).map_mem g hf
    have hq : ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientMap
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) g).hom
          (Submodule.Quotient.mk (p := Low W) (φ W ⟨f, hf⟩)) =
          Submodule.Quotient.mk (p := Low W') (φ W' ⟨_, hf'⟩) := rfl
    rw [hq, hI, hI]
    exact (((hasDualIntegral_integralOn hPd hNc _ V haar (hScs W f hf)).map
      (SmoothRep.hom g).toLinearMap).congr fun _ => rfl).dualIntegral_eq
  -- Twisted equivariance under `M(F)`, for a scalar independent of the representation.
  have hMQ : pointImage (lQ ≫ q) ≤ pointImage q := pointImage_comp_le q lQ
  have hm'mem : ∀ m : rationalPoints M,
      (leviPointsEquiv q lQ hq hlQ m : rationalPoints G) ∈ pointImage (l ≫ p) := by
    intro m
    rw [hsame]
    exact (leviPointsEquiv q lQ hq hlQ m).2
  let m' : rationalPoints M → pointImage (l ≫ p) := fun m =>
    ⟨(leviPointsEquiv q lQ hq hlQ m : rationalPoints G), hm'mem m⟩
  have hm' : ∀ m, (leviPointsEquiv p l hp hl).symm (m' m) = m := by
    intro m
    rw [ContinuousMulEquiv.symm_apply_eq]
    apply Subtype.ext
    change rationalPoints.map (lQ ≫ q) m = rationalPoints.map (l ≫ p) m
    rw [hsame]
  let χ : rationalPoints M → ℂ := fun m =>
    ((HaarModulus.closedInverseHalfCharacter (pointImage (rQ ≫ q)) hUc (pointImage (lQ ≫ q))
      (pointImage_le_normalizer q lQ rQ hrQ) (leviPointsEquiv q lQ hq hlQ m) : ℂˣ) : ℂ) *
      leviFactor hPd hNc haar hMV (m' m)
  have hχ : ∀ (W : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (m : rationalPoints M)
      (x : (closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) W),
      I W (((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) W).ρ m x) =
        χ m • W.representation m (I W x) := by
    intro W m x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Low W) x
    obtain ⟨⟨f, hf⟩, rfl⟩ := hφsurj W y
    have hf' := ((boundaryVanishingSubfunctor p l r hp hr hl hmul q
      (identityParabolicDoubleCoset p q)).obj W).apply_mem_toSubmodule
        ⟨_, hMQ (leviPointsEquiv q lQ hq hlQ m).2⟩ hf
    have hq : ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
        (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)) W).ρ m
          (Submodule.Quotient.mk (p := Low W) (φ W ⟨f, hf⟩)) =
        Submodule.Quotient.mk (p := Low W)
          (((HaarModulus.closedInverseHalfCharacter (pointImage (rQ ≫ q)) hUc
            (pointImage (lQ ≫ q)) (pointImage_le_normalizer q lQ rQ hrQ)
            (leviPointsEquiv q lQ hq hlQ m) : ℂˣ) : ℂ) • φ W ⟨_, hf'⟩) := rfl
    rw [hq, hIsmul, hI]
    have hlevi := integralOn_smoothInduced_levi hPd hNc
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar hVc hMV (hScs W f hf) (m' m)
    change _ • integralOn hPd hNc _ V haar (Induction.smoothInduced (pointImage p)
      (inducingRepresentation hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W))
        ((m' m : pointImage (l ≫ p)) : rationalPoints G) f) = _
    have hXY : (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W).representation (m' m)
        (integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar f) =
        W.representation m
          (integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar f) :=
      congrArg (fun g => W.representation g
        (integralOn hPd hNc (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm W) V haar f))
        (hm' m)
    rw [hlevi]
    exact (smul_smul _ _ _).trans (congrArg (fun z => χ m • z) hXY)
  -- Conclusion: the natural identification of `pqSupportGraded`, rigidity, and `χ = 1`.
  obtain ⟨e, he⟩ := (pqSupportGraded.{u, v} k G hG P M N Q U p l r hp hl hr hmul q lQ rQ hq
    hlQ hrQ hmulQ hsame).2
  intro σ
  obtain ⟨E, hE⟩ := SmoothRep.exists_equiv_of_natural_surjective
    (fun W => (closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientObj
      (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)) W)
    (fun g => ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientMap
      (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)) g).hom.toLinearMap)
    e he I hnat hsurj χ hχ σ
  refine ⟨E, ?_⟩
  intro f hf y hy hyf ℓ
  subst hyf
  have h := hasDualIntegral_integralOn hPd hNc _ V haar (hScs σ f hf) ℓ
  exact ⟨h.1, (congrArg ℓ ((hE _).trans (hI σ ⟨f, hf⟩))).trans h.2⟩

/-- **Renard VII.3.4** (integral form of `J_{Q|P}`): the integral identification of
`F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ)` with `σ`, and for `PQ`-regular `σ` the unique intertwining operator
`J_{Q|P}(σ)` with `J(f)(1) = ∫_{N̄(F) ∩ U(F)} f(v) dv` on `F̃^{<1̄}_{PQ}(σ)`. -/
theorem pqIntegralIntertwiningOperator : PQIntegralIntertwiningOperatorStatement.{u, v} :=
  pqIntegralIntertwiningOperator_of_identification pqIntegralIdentification.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
