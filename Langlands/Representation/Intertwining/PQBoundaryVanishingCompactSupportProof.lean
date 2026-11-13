import Langlands.Representation.Aubert.General.SemidirectIntersection
import Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction
import Langlands.Representation.Intertwining.PQIdentitySupportProof
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof

/-! # Renard's compact-support description of `F̃^{<1̄}_{PQ}` -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

section Abstract

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- A function invariant under right translation by an open subgroup has open fibres over
every set of values. -/
theorem isOpen_setOf_mem_of_openSubgroup {X : Type*} {φ : Γ → X} (K₀ : OpenSubgroup Γ)
    (hK₀ : ∀ (x : Γ) (k : K₀), φ (x * k) = φ x) (s : Set X) : IsOpen {x | φ x ∈ s} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hmem : (fun y => x⁻¹ * y) ⁻¹' (K₀ : Set Γ) ∈ 𝓝 x := by
    apply (K₀.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simp
  filter_upwards [hmem] with y hy
  have h := hK₀ x ⟨x⁻¹ * y, hy⟩
  simp only [mul_inv_cancel_left] at h
  change φ y ∈ s
  rw [h]
  exact hx

/-- Abstract form of Renard's description of `F̃^{<1̄}_{PQ}`. Let `P` and `V` be closed subgroups
of a locally compact σ-compact group with `P \ Γ` compact, let `Q` be a subgroup with the orbit
`P \ PQ` locally closed, and let `V ≤ Q` meet `P` trivially with `Q ⊆ PV`. A locally constant
function `φ` whose zero set is left `P`-invariant vanishes on `closure (PQ) \ PQ` exactly when
its restriction to `V` vanishes off a compact set. -/
theorem boundaryVanishing_iff_compactSupport [LocallyCompactSpace Γ] [SigmaCompactSpace Γ]
    {P Q V : Subgroup Γ} (hP : IsClosed (P : Set Γ)) (hV : IsClosed (V : Set Γ))
    [CompactSpace (Induction.LeftQuotient P)]
    (hloc : IsLocallyClosed (Geometric.cosetOrbit P Q 1))
    (hVQ : V ≤ Q) (hPV : ∀ v ∈ V, v ∈ P → v = 1)
    (hQPV : ∀ x ∈ Q, ∃ v ∈ V, x * v⁻¹ ∈ P)
    {X : Type*} [Zero X] (φ : Γ → X)
    (hcov : ∀ p ∈ P, ∀ x, φ x = 0 → φ (p * x) = 0)
    (K₀ : OpenSubgroup Γ) (hK₀ : ∀ (x : Γ) (k : K₀), φ (x * k) = φ x) :
    (∀ x ∈ closure (DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1)) \
        DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1), φ x = 0) ↔
      ∃ K : Set V, IsCompact K ∧ ∀ x : V, x ∉ K → φ x = 0 := by
  classical
  set D := DoubleCoset.quotToDoubleCoset P Q (DoubleCoset.mk P Q 1) with hDdef
  have hD : ∀ x, x ∈ D ↔ ∃ p ∈ P, ∃ q ∈ Q, x = p * q := by
    intro x
    rw [hDdef, DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq]
    simp
  have hcov' : ∀ p ∈ P, ∀ x, φ (p * x) = 0 → φ x = 0 := by
    intro p hp x h
    have := hcov p⁻¹ (P.inv_mem hp) (p * x) h
    simpa using this
  set S : Set Γ := {x | φ x ≠ 0} with hSdef
  have hSopen : IsOpen S := isOpen_setOf_mem_of_openSubgroup K₀ hK₀ {0}ᶜ
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    convert isOpen_setOf_mem_of_openSubgroup K₀ hK₀ {0} using 1
    ext x
    simp [hSdef]
  constructor
  · intro hvan
    let π := Induction.quotientMap P
    let Z : Set Γ := closure D ∩ S
    have hclP : ∀ p ∈ P, ∀ x ∈ closure D, p * x ∈ closure D := by
      intro p hp x hx
      refine map_mem_closure
        (show Continuous (fun y : Γ => p * y) from continuous_const.mul continuous_id) hx ?_
      intro y hy
      obtain ⟨p', hp', q, hq, rfl⟩ := (hD y).mp hy
      exact (hD _).mpr ⟨p * p', P.mul_mem hp hp', q, hq, by rw [mul_assoc]⟩
    have hZsat : π ⁻¹' (π '' Z) = Z := by
      ext x
      constructor
      · rintro ⟨y, ⟨hycl, hyS⟩, hxy⟩
        have h : x * y⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
        refine ⟨?_, ?_⟩
        · have := hclP _ h y hycl
          simpa using this
        · intro hx0
          apply hyS
          apply hcov' _ h y
          simpa using hx0
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hTclosed : IsClosed (π '' Z) := by
      apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
      change IsClosed (π ⁻¹' (π '' Z))
      rw [hZsat]
      exact isClosed_closure.inter hSclosed
    have hTO : π '' Z ⊆ Geometric.cosetOrbit P V 1 := by
      rintro _ ⟨x, ⟨hxcl, hxS⟩, rfl⟩
      have hxD : x ∈ D := by
        by_contra h
        exact hxS (hvan x ⟨hxcl, h⟩)
      obtain ⟨p, hp, q, hq, rfl⟩ := (hD x).mp hxD
      obtain ⟨b, hb, hqb⟩ := hQPV q hq
      refine ⟨⟨b, hb⟩, ?_⟩
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      have := P.mul_mem hp hqb
      simpa [mul_assoc] using this
    have horb : Geometric.cosetOrbit P V 1 = Geometric.cosetOrbit P Q 1 := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨⟨v, hVQ v.2⟩, rfl⟩
      · rintro ⟨q, rfl⟩
        obtain ⟨b, hb, hqb⟩ := hQPV q q.2
        refine ⟨⟨b, hb⟩, ?_⟩
        apply Quotient.sound
        apply QuotientGroup.rightRel_apply.mpr
        simpa [mul_assoc] using hqb
    have hloc' : IsLocallyClosed (Geometric.cosetOrbit P V 1) := horb ▸ hloc
    let h := Geometric.cosetOrbitHomeomorph P V 1 hP hV hloc'
    have hρinv : ∀ a b : V, (QuotientGroup.rightRel (Geometric.orbitStabilizer P V 1)) a b →
        id a = id b := by
      intro a b hab
      have hba : b * a⁻¹ ∈ Geometric.orbitStabilizer P V 1 := QuotientGroup.rightRel_apply.mp hab
      have hba' : (b : Γ) * (a : Γ)⁻¹ ∈ P := by
        simpa [Geometric.orbitStabilizer] using hba
      have := hPV _ (V.mul_mem b.2 (V.inv_mem a.2)) hba'
      exact (Subtype.ext (mul_inv_eq_one.mp this)).symm
    let ρbar : Induction.LeftQuotient (Geometric.orbitStabilizer P V 1) → V :=
      Quotient.lift id hρinv
    have hρbar : Continuous ρbar := continuous_id.quotient_lift _
    let T' : Set (Geometric.cosetOrbit P V 1) := Subtype.val ⁻¹' (π '' Z)
    have hT' : IsCompact T' := by
      apply Subtype.isCompact_iff.mpr
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hTO]
      exact hTclosed.isCompact
    refine ⟨ρbar '' (h.symm '' T'), (hT'.image h.symm.continuous).image hρbar, ?_⟩
    intro v hvK
    by_contra hv
    apply hvK
    refine ⟨h.symm (Geometric.cosetOrbitMap P V 1 v), ⟨_, ?_, rfl⟩, ?_⟩
    · change Induction.quotientMap P (1⁻¹ * (v : Γ)) ∈ π '' Z
      refine ⟨v, ⟨subset_closure ((hD v).mpr ⟨1, P.one_mem, v, hVQ v.2, by simp⟩), hv⟩, ?_⟩
      simp [π]
    · rw [Geometric.cosetOrbitHomeomorph_symm_map P V 1 hP hV hloc' v]
      rfl
  · rintro ⟨K, hK, hKv⟩ x ⟨hxcl, hxD⟩
    by_contra hx
    let C : Set Γ := (P : Set Γ) * (Subtype.val '' K)
    have hC : IsClosed C := hP.mul_right_of_isCompact (hK.image continuous_subtype_val)
    have hxC : x ∉ C := by
      rintro ⟨p, hp, _, ⟨w, -, rfl⟩, rfl⟩
      exact hxD ((hD _).mpr ⟨p, hp, w, hVQ w.2, rfl⟩)
    have hW : IsOpen (S ∩ Cᶜ) := hSopen.inter hC.isOpen_compl
    obtain ⟨y, ⟨hyS, hyC⟩, hyD⟩ := mem_closure_iff.mp hxcl _ hW ⟨hx, hxC⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := (hD y).mp hyD
    obtain ⟨b, hbV, hqb⟩ := hQPV q hq
    have hpb : p * q * b⁻¹ ∈ P := by
      have := P.mul_mem hp hqb
      simpa [mul_assoc] using this
    have hb : φ b ≠ 0 := by
      intro hb0
      apply hyS
      have := hcov _ hpb b hb0
      simpa [mul_assoc] using this
    have hbK : (⟨b, hbV⟩ : V) ∈ K := by
      by_contra h
      exact hb (hKv ⟨b, hbV⟩ h)
    exact hyC ⟨p * q * b⁻¹, hpb, b, ⟨⟨b, hbV⟩, hbK, rfl⟩, by simp⟩

end Abstract

open GroupScheme MatrixRepresentation

/-- Renard's decomposition `U = (U ∩ N)(U ∩ N̄)` of the unipotent radical of `Q` (VII.3.4, proof,
printed p.236 / PDF p.242), on rational points over a nonarchimedean local field: for parabolics
`P = MN`, `Q = MU` with the same Levi and the opposite parabolic `P̄ = MN̄`, every rational point
of `U` is the product of a rational point of `U ∩ N` and a rational point of `U ∩ N̄`. -/
theorem pointImage_radical_eq_mul {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
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
    ((pointImage (rQ ≫ q) : Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
      ((pointImage (r ≫ p) ⊓ pointImage (rQ ≫ q) : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) *
        ((pointImage (rb ≫ pb) ⊓ pointImage (rQ ≫ q) : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨presP⟩ := parabolicRootPresentationExistence k G hG P M A p l a hp hl ha
  obtain ⟨presQ⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ a hq hlQ ha
  obtain ⟨presB⟩ := parabolicRootPresentationExistence k G hG Pb M A pb lb a hpb hlb ha
  obtain ⟨t, ht⟩ := BruhatTits.DynamicUnipotentContainment.exists_unit_tendsto_pow_zero (F := k)
  -- The value `ξ(t)` of the split-component cocharacter of `Q` lies in `M(F)`.
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
  let : TopologicalSpace (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology k G.X
  let e := unipotentIntersectionProduct k χ ξ t ht hξ hZU
  rw [hN, hU, hNbar]
  ext x
  constructor
  · intro hx
    obtain ⟨⟨h, h'⟩, hhh⟩ := e.surjective ⟨x, hx⟩
    have hval := congrArg Subtype.val hhh
    rw [unipotentIntersectionProduct_apply] at hval
    exact ⟨h.1.1, ⟨h.2, h.1.2⟩, h'.1.1, ⟨h'.2, h'.1.2⟩, hval⟩
  · rintro ⟨y, ⟨-, hy⟩, z, ⟨-, hz⟩, rfl⟩
    exact Subgroup.mul_mem _ hy hz

set_option maxHeartbeats 1200000 in
/-- Renard's description of `F̃^{<1̄}_{PQ}` by compact support on `N̄(F) ∩ U(F)`. -/
theorem pqBoundaryVanishingCompactSupport :
    PQBoundaryVanishingCompactSupportStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U Pb Nb p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ pb lb rb hpb hlb hrb
    hmulb hsame hbar hopp V
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  intro σ f
  have hU := pointImage_radical_eq_mul hG hp hl hr hq hlQ hrQ hmulQ hpb hlb hrb hsame hbar hopp
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  obtain ⟨m, c, z₀, hz₀, D₀, hglued⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hfinite : Finite (parabolicDoubleCosets p q) := Finite.of_surjective c c.surjective
  obtain ⟨n, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q) (isClosed_pointImage p hp.isClosedSubgroup)
      (isClosed_pointImage q hq.isClosedSubgroup) hfinite
  have hloc : IsLocallyClosed (Geometric.cosetOrbit (pointImage p) (pointImage q) 1) := by
    have := (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q)
      s.bruhatLinearOrder s.isBruhatRefinement_bruhatLinearOrder 1).orbit_isLocallyClosed
    simpa only [inv_one] using this
  have hVclosed : IsClosed (V : Set (rationalPoints G)) :=
    (isClosed_pointImage_comp pb rb hpb.isClosedSubgroup hrb.1.isClosedSubgroup).inter
      (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
  have hVQ : V ≤ pointImage q := inf_le_right.trans (pointImage_comp_le q rQ)
  have hPV : ∀ v ∈ V, v ∈ pointImage p → v = 1 := by
    intro v hv hvp
    have hvpb : v ∈ pointImage pb := pointImage_comp_le pb rb hv.1
    have hvM : v ∈ pointImage (lb ≫ pb) := by
      rw [hbar, ← hopp]
      exact ⟨hvp, hvpb⟩
    exact IsSemidirectDecomposition.eq_one_of_mem_of_mem
      (isSemidirectDecomposition_pointImage pb lb rb hpb.isClosedSubgroup hrb hmulb) hvM hv.1
  have hQPV : ∀ x ∈ pointImage q, ∃ v ∈ V, x * v⁻¹ ∈ pointImage p := by
    intro x hx
    let dQ := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
    set mx := dQ.projection ⟨x, hx⟩ with hmx
    have hux : ((mx : rationalPoints G))⁻¹ * x ∈ pointImage (rQ ≫ q) :=
      dQ.projection_inv_mul_mem ⟨x, hx⟩
    have hux' : ((mx : rationalPoints G))⁻¹ * x ∈
        ((pointImage (rQ ≫ q) : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := hux
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
  let φ := Induction.eval (pointImage p)
    (inducingRepresentation
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f
  have hcov : ∀ p' ∈ pointImage p, ∀ x, φ x = 0 → φ (p' * x) = 0 := by
    intro p' hp' x hx
    have h := f.1.2 ⟨p', hp'⟩ x
    change φ (p' * x) = _ at h
    rw [h]
    have hx' : f.1.1 x = 0 := hx
    rw [hx', map_zero]
    rfl
  obtain ⟨K₀, hK₀⟩ := f.property
  have hsmooth : ∀ (x : rationalPoints G) (k : K₀), φ (x * k) = φ x := by
    intro x k
    exact congrArg (fun F => F.1 x) (hK₀ k)
  rw [← boundaryVanishing_iff_compactSupport (isClosed_pointImage p hp.isClosedSubgroup)
    hVclosed hloc hVQ hPV hQPV φ hcov K₀ hsmooth]
  exact Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p) (pointImage q) _
    (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p q)) _ f

end Langlands.Aubert.General.RepresentedParabolic
